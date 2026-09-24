module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.Proofs.RuleSupport.StrConcatSupport
public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-! ## Generic helpers -/

/-- `__eo_list_concat f a b` reduces to the recursive concat when both are lists. -/
private theorem list_concat_reduce_local (f a b : Term)
    (ha : __eo_is_list f a = Term.Boolean true)
    (hb : __eo_is_list f b = Term.Boolean true) :
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) = __eo_list_concat_rec a b
  rw [ha, hb]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

/-- Stable rewrite for evaluating SMT `str_rev` terms. -/
private theorem smtx_eval_str_rev_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_rev x) =
      __smtx_model_eval_str_rev (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- `str_rev` preserves the value relation. -/
private theorem smt_value_rel_model_eval_str_rev_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev a) (__smtx_model_eval_str_rev b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_rev, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

/-- Translation/seq-type helper. -/
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

/-- `__eo_typeof_str_rev T ≠ Stuck` forces `T = Seq U` for some `U`. -/
private theorem eo_typeof_str_rev_arg_seq
    (T : Term) (h : __eo_typeof_str_rev T ≠ Term.Stuck) :
    ∃ U, T = Term.Apply Term.Seq U := by
  cases T <;> simp [__eo_typeof_str_rev, Term.Seq] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_rev] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_rev, Term.Seq] at h ⊢

/-- `__eo_typeof_str_rev T = Seq U` forces `T = Seq U`. -/
private theorem eo_typeof_str_rev_arg_eq
    (T U : Term) (h : __eo_typeof_str_rev T = Term.Apply Term.Seq U) :
    T = Term.Apply Term.Seq U := by
  cases T <;> simp [__eo_typeof_str_rev, Term.Seq] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_rev] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_rev, Term.Seq] at h ⊢
      case Seq => exact h

/-- `__eo_typeof_str_rev (Seq U) = Seq U`. -/
private theorem typeof_str_rev_seq (U : Term) :
    __eo_typeof_str_rev (Term.Apply Term.Seq U) = Term.Apply Term.Seq U := rfl

/-- `__eo_typeof_str_concat A B = Seq U` forces both arguments to be `Seq U`. -/
private theorem eo_typeof_str_concat_args_seq
    (A B U : Term)
    (h : __eo_typeof_str_concat A B = Term.Apply Term.Seq U) :
    A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
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
            cases opB <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
            case Seq =>
              -- h : __eo_requires (__eo_eq xA xB) (Boolean true) (Apply Seq xA) = Apply Seq U
              have hNe : __eo_requires (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) ≠ Term.Stuck := by
                rw [h]; simp [Term.Seq]
              have hRes : Term.Apply Term.Seq xA = Term.Apply Term.Seq U := by
                rw [← eo_requires_eq_result_of_ne_stuck (__eo_eq xA xB)
                  (Term.Boolean true) (Term.Apply Term.Seq xA) hNe]; exact h
              have hxAU : xA = U := (Term.Apply.inj hRes).2
              have hCond : __eo_eq xA xB = Term.Boolean true :=
                eo_requires_eq_of_ne_stuck (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) hNe
              have hxBA : xB = xA := RuleProofs.eq_of_eo_eq_true xA xB hCond
              exact ⟨by rw [hxAU], by rw [hxBA, hxAU]⟩

/-! ## Program reduction -/

/-- Raw reduction: only the three Stuck guards block the match. -/
private theorem prog_seq_rev_concat_raw
    (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck) :
    __eo_prog_seq_rev_concat x1 y1 z1 =
      __eo_mk_apply
        (__eo_mk_apply Term.eq
          (__eo_mk_apply Term.str_rev
            (__eo_mk_apply (Term.Apply Term.str_concat x1)
              (__eo_list_concat Term.str_concat y1
                (__eo_mk_apply (Term.Apply Term.str_concat z1)
                  (__eo_nil Term.str_concat (__eo_typeof x1)))))))
        (__eo_mk_apply (Term.Apply Term.str_concat (Term.Apply Term.str_rev z1))
          (__eo_mk_apply
            (__eo_mk_apply Term.str_concat
              (__eo_mk_apply Term.str_rev
                (__eo_list_singleton_elim Term.str_concat
                  (Term.Apply (Term.Apply Term.str_concat x1) y1))))
            (__eo_nil Term.str_concat (__eo_typeof (Term.Apply Term.str_rev z1))))) := by
  cases hx1 : x1 <;> first
    | exact False.elim (hX1 hx1)
    | (cases hy1 : y1 <;> first
        | exact False.elim (hY1 hy1)
        | (cases hz1 : z1 <;> first
            | exact False.elim (hZ1 hz1)
            | rfl))

/-- `__eo_mk_apply` collapses to `Term.Apply` when both arguments are non-stuck. -/
private theorem mk_apply_collapse {f a : Term}
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

/-- `__eo_nil str_concat (typeof x) = __seq_empty (typeof x)` for sequence-typed `x`. -/
private theorem eo_nil_str_concat_of_typeof_seq (x T : Term)
    (h : __eo_typeof x = Term.Apply Term.Seq T) :
    __eo_nil Term.str_concat (__eo_typeof x) = __seq_empty (__eo_typeof x) := by
  rw [h]; rfl

private theorem seq_empty_seq_ne_stuck (A T : Term)
    (h : A = Term.Apply Term.Seq T) : __seq_empty A ≠ Term.Stuck := by
  subst A; cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op => cases op <;> simp [__seq_empty, Term.Seq]

private theorem is_list_nil_seq_empty_seq (A T : Term)
    (h : A = Term.Apply Term.Seq T) :
    __eo_is_list_nil Term.str_concat (__seq_empty A) = Term.Boolean true := by
  subst A; cases T <;>
    simp [__seq_empty, Term.Seq, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq]
  case UOp op =>
    cases op <;>
      simp [__seq_empty, Term.Seq, __eo_is_list_nil, __eo_is_list_nil_str_concat,
        __eo_eq, native_teq]

/-- `__seq_empty (typeof x)` is a `str_concat`-list when `x` is sequence-typed. -/
private theorem is_list_seq_empty_seq (A T : Term)
    (h : A = Term.Apply Term.Seq T) :
    __eo_is_list Term.str_concat (__seq_empty A) = Term.Boolean true :=
  strConcat_is_list_nil_true_of_nil_true _ (is_list_nil_seq_empty_seq A T h)

/-- Clean reduction of the program to an `mkEq` of readable `mkConcat`/`str_rev`
    forms, given the extracted type and list facts. -/
private theorem prog_seq_rev_concat_eq
    (x1 y1 z1 T Tz : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hX1Ty : __eo_typeof x1 = Term.Apply Term.Seq T)
    (hRevZTy : __eo_typeof (Term.Apply Term.str_rev z1) = Term.Apply Term.Seq Tz)
    (hY1List : __eo_is_list Term.str_concat y1 = Term.Boolean true)
    (hElim : __str_nary_elim (mkConcat x1 y1) ≠ Term.Stuck) :
    __eo_prog_seq_rev_concat x1 y1 z1 =
      mkEq
        (Term.Apply Term.str_rev
          (mkConcat x1
            (__eo_list_concat_rec y1
              (mkConcat z1 (__seq_empty (__eo_typeof x1))))))
        (mkConcat (Term.Apply Term.str_rev z1)
          (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
            (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) := by
  rw [prog_seq_rev_concat_raw x1 y1 z1 hX1 hY1 hZ1]
  -- reduce the two nils to seq_empty
  rw [eo_nil_str_concat_of_typeof_seq x1 T hX1Ty]
  rw [eo_nil_str_concat_of_typeof_seq (Term.Apply Term.str_rev z1) Tz hRevZTy]
  -- collapse the inner `mkConcat z1 (seq_empty …)`
  have hTailMk :
      __eo_mk_apply (Term.Apply Term.str_concat z1) (__seq_empty (__eo_typeof x1)) =
        mkConcat z1 (__seq_empty (__eo_typeof x1)) :=
    mk_apply_collapse (by simp) (seq_empty_seq_ne_stuck (__eo_typeof x1) T hX1Ty)
  rw [hTailMk]
  -- reduce the list-concat to its recursive form
  have hTailList :
      __eo_is_list Term.str_concat (mkConcat z1 (__seq_empty (__eo_typeof x1))) =
        Term.Boolean true :=
    strConcat_is_list_cons_true_of_tail_list z1 (__seq_empty (__eo_typeof x1))
      (is_list_seq_empty_seq (__eo_typeof x1) T hX1Ty)
  rw [list_concat_reduce_local Term.str_concat y1
      (mkConcat z1 (__seq_empty (__eo_typeof x1))) hY1List hTailList]
  -- collapse the str_rev wrapper around the nary-elim
  have hSEMk :
      __eo_mk_apply Term.str_rev
          (__eo_list_singleton_elim Term.str_concat (mkConcat x1 y1)) =
        Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)) :=
    mk_apply_collapse (by simp) hElim
  -- collapse the str_concat wrapper around the list-concat-rec
  have hLCNeStuck :
      __eo_list_concat_rec y1 (mkConcat z1 (__seq_empty (__eo_typeof x1))) ≠
        Term.Stuck :=
    eo_list_concat_rec_ne_stuck_of_list Term.str_concat y1
      (mkConcat z1 (__seq_empty (__eo_typeof x1))) hY1List (by simp)
  have hBigMk :
      __eo_mk_apply (Term.Apply Term.str_concat x1)
          (__eo_list_concat_rec y1 (mkConcat z1 (__seq_empty (__eo_typeof x1)))) =
        mkConcat x1
          (__eo_list_concat_rec y1 (mkConcat z1 (__seq_empty (__eo_typeof x1)))) :=
    mk_apply_collapse (by simp) hLCNeStuck
  have hNILv0Ne :
      __seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)) ≠ Term.Stuck :=
    seq_empty_seq_ne_stuck (__eo_typeof (Term.Apply Term.str_rev z1)) Tz hRevZTy
  rw [hBigMk, hSEMk]
  simp [__eo_mk_apply, mkEq, mkConcat, hNILv0Ne]

/-! ## Stuck propagation / fact extraction -/

/-- `__eo_requires` with a stuck body is stuck. -/
private theorem eo_requires_stuck_right (a b : Term) :
    __eo_requires a b Term.Stuck = Term.Stuck := by
  simp [__eo_requires, native_ite]

/-- `__eo_mk_apply _ Stuck = Stuck`, regardless of the first argument. -/
private theorem mk_apply_right_stuck (a : Term) :
    __eo_mk_apply a Term.Stuck = Term.Stuck := by
  cases a <;> rfl

/-- `__eo_mk_apply Stuck _ = Stuck`. -/
private theorem mk_apply_left_stuck (a : Term) :
    __eo_mk_apply Term.Stuck a = Term.Stuck := rfl

/-- `__eo_list_concat str_concat a Stuck` is stuck. -/
private theorem list_concat_right_stuck (a : Term) :
    __eo_list_concat Term.str_concat a Term.Stuck = Term.Stuck := by
  change __eo_requires (__eo_is_list Term.str_concat a) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.str_concat Term.Stuck) (Term.Boolean true)
        (__eo_list_concat_rec a Term.Stuck)) = Term.Stuck
  have hInner : __eo_is_list Term.str_concat Term.Stuck = Term.Stuck := rfl
  rw [hInner]
  have hReq : __eo_requires Term.Stuck (Term.Boolean true)
      (__eo_list_concat_rec a Term.Stuck) = Term.Stuck := by
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  rw [hReq, eo_requires_stuck_right]

/-- If the program is non-stuck, the `nil` placed for `x1` is non-stuck. -/
private theorem nilx_ne_stuck_of_prog_ne_stuck (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hProg : __eo_prog_seq_rev_concat x1 y1 z1 ≠ Term.Stuck) :
    __eo_nil Term.str_concat (__eo_typeof x1) ≠ Term.Stuck := by
  intro hNil
  apply hProg
  rw [prog_seq_rev_concat_raw x1 y1 z1 hX1 hY1 hZ1, hNil]
  simp only [list_concat_right_stuck, mk_apply_right_stuck, mk_apply_left_stuck]

/-- From `list_concat … ≠ Stuck` extract that the left argument is a list. -/
private theorem is_list_left_of_list_concat_ne_stuck (a b : Term)
    (h : __eo_list_concat Term.str_concat a b ≠ Term.Stuck) :
    __eo_is_list Term.str_concat a = Term.Boolean true := by
  change __eo_requires (__eo_is_list Term.str_concat a) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.str_concat b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) ≠ Term.Stuck at h
  exact eo_requires_eq_of_ne_stuck _ _ _ h

/-- A non-stuck `nil` for `str_concat` forces a sequence type. -/
private theorem typeof_seq_of_nil_ne_stuck (A : Term)
    (h : __eo_nil Term.str_concat A ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_nil, __eo_nil_str_concat, Term.Seq] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_nil, __eo_nil_str_concat] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_nil, __eo_nil_str_concat, Term.Seq] at h ⊢

/-- Stuck propagation through the list-concat slot. -/
private theorem prog_stuck_of_lc_stuck (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hLC : __eo_list_concat Term.str_concat y1
        (__eo_mk_apply (Term.Apply Term.str_concat z1)
          (__eo_nil Term.str_concat (__eo_typeof x1))) = Term.Stuck) :
    __eo_prog_seq_rev_concat x1 y1 z1 = Term.Stuck := by
  rw [prog_seq_rev_concat_raw x1 y1 z1 hX1 hY1 hZ1, hLC]
  simp only [mk_apply_right_stuck, mk_apply_left_stuck]

/-- Stuck propagation through the nary-elim slot. -/
private theorem prog_stuck_of_elim_stuck (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hElim : __eo_list_singleton_elim Term.str_concat
        (Term.Apply (Term.Apply Term.str_concat x1) y1) = Term.Stuck) :
    __eo_prog_seq_rev_concat x1 y1 z1 = Term.Stuck := by
  rw [prog_seq_rev_concat_raw x1 y1 z1 hX1 hY1 hZ1, hElim]
  simp only [mk_apply_right_stuck, mk_apply_left_stuck]

/-- Stuck propagation through the `nil` for `str_rev z1`. -/
private theorem prog_stuck_of_nilv0_stuck (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hNil : __eo_nil Term.str_concat (__eo_typeof (Term.Apply Term.str_rev z1)) =
        Term.Stuck) :
    __eo_prog_seq_rev_concat x1 y1 z1 = Term.Stuck := by
  rw [prog_seq_rev_concat_raw x1 y1 z1 hX1 hY1 hZ1, hNil]
  simp only [mk_apply_right_stuck, mk_apply_left_stuck]

/-- Master extraction: structural facts from the program being non-stuck. -/
private theorem extract_facts (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hProg : __eo_prog_seq_rev_concat x1 y1 z1 ≠ Term.Stuck) :
    (∃ T, __eo_typeof x1 = Term.Apply Term.Seq T) ∧
      (∃ Tz, __eo_typeof (Term.Apply Term.str_rev z1) = Term.Apply Term.Seq Tz) ∧
      __eo_is_list Term.str_concat y1 = Term.Boolean true ∧
      __str_nary_elim (mkConcat x1 y1) ≠ Term.Stuck := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact typeof_seq_of_nil_ne_stuck (__eo_typeof x1)
      (nilx_ne_stuck_of_prog_ne_stuck x1 y1 z1 hX1 hY1 hZ1 hProg)
  · refine typeof_seq_of_nil_ne_stuck (__eo_typeof (Term.Apply Term.str_rev z1)) ?_
    intro hNil
    exact hProg (prog_stuck_of_nilv0_stuck x1 y1 z1 hX1 hY1 hZ1 hNil)
  · refine is_list_left_of_list_concat_ne_stuck y1
      (__eo_mk_apply (Term.Apply Term.str_concat z1)
        (__eo_nil Term.str_concat (__eo_typeof x1))) ?_
    intro hLC
    exact hProg (prog_stuck_of_lc_stuck x1 y1 z1 hX1 hY1 hZ1 hLC)
  · intro hElim
    exact hProg (prog_stuck_of_elim_stuck x1 y1 z1 hX1 hY1 hZ1 hElim)

/-- When `y1` is an empty `str_concat`-list, the nary-elim collapses to `x1`. -/
private theorem nary_elim_eq_self_of_nil (x1 y1 : Term)
    (hY1List : __eo_is_list Term.str_concat y1 = Term.Boolean true)
    (hnil : __eo_is_list_nil Term.str_concat y1 = Term.Boolean true) :
    __str_nary_elim (mkConcat x1 y1) = x1 := by
  show __eo_list_singleton_elim Term.str_concat (mkConcat x1 y1) = x1
  have hList : __eo_is_list Term.str_concat (mkConcat x1 y1) = Term.Boolean true :=
    strConcat_is_list_cons_true_of_tail_list x1 y1 hY1List
  change __eo_requires (__eo_is_list Term.str_concat (mkConcat x1 y1))
      (Term.Boolean true) (__eo_list_singleton_elim_2 (mkConcat x1 y1)) = x1
  rw [hList]
  have hReqT : __eo_requires (Term.Boolean true) (Term.Boolean true)
      (__eo_list_singleton_elim_2 (mkConcat x1 y1)) =
      __eo_list_singleton_elim_2 (mkConcat x1 y1) := by
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  rw [hReqT]
  change __eo_ite (__eo_is_list_nil Term.str_concat y1) x1 (mkConcat x1 y1) = x1
  rw [hnil]; rfl

/-- When `y1` is a non-empty `str_concat`-list, the nary-elim is the bare concat. -/
private theorem nary_elim_eq_concat_of_not_nil (x1 y1 : Term)
    (hY1List : __eo_is_list Term.str_concat y1 = Term.Boolean true)
    (hNil : __eo_is_list_nil Term.str_concat y1 = Term.Boolean false) :
    __str_nary_elim (mkConcat x1 y1) = mkConcat x1 y1 := by
  show __eo_list_singleton_elim Term.str_concat (mkConcat x1 y1) = mkConcat x1 y1
  have hList : __eo_is_list Term.str_concat (mkConcat x1 y1) = Term.Boolean true :=
    strConcat_is_list_cons_true_of_tail_list x1 y1 hY1List
  change __eo_requires (__eo_is_list Term.str_concat (mkConcat x1 y1))
      (Term.Boolean true) (__eo_list_singleton_elim_2 (mkConcat x1 y1)) = mkConcat x1 y1
  rw [hList]
  have hReqT : __eo_requires (Term.Boolean true) (Term.Boolean true)
      (__eo_list_singleton_elim_2 (mkConcat x1 y1)) =
      __eo_list_singleton_elim_2 (mkConcat x1 y1) := by
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  rw [hReqT]
  change __eo_ite (__eo_is_list_nil Term.str_concat y1) x1 (mkConcat x1 y1) = mkConcat x1 y1
  rw [hNil]; rfl

/-- Master typing extraction: a common element type and the `y1` nil/typing case. -/
private theorem typeof_args_of_prog_bool (x1 y1 z1 : Term)
    (hX1 : x1 ≠ Term.Stuck) (hY1 : y1 ≠ Term.Stuck) (hZ1 : z1 ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_seq_rev_concat x1 y1 z1) = Term.Bool) :
    ∃ T, __eo_typeof x1 = Term.Apply Term.Seq T ∧
      __eo_typeof z1 = Term.Apply Term.Seq T ∧
      __eo_is_list Term.str_concat y1 = Term.Boolean true ∧
      __str_nary_elim (mkConcat x1 y1) ≠ Term.Stuck ∧
      (__eo_is_list_nil Term.str_concat y1 = Term.Boolean true ∨
        __eo_typeof y1 = Term.Apply Term.Seq T) := by
  have hProgNe : __eo_prog_seq_rev_concat x1 y1 z1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  obtain ⟨⟨T1, hX1Ty⟩, ⟨Tz, hRevZTy⟩, hY1List, hElim⟩ :=
    extract_facts x1 y1 z1 hX1 hY1 hZ1 hProgNe
  have hZ1Ty : __eo_typeof z1 = Term.Apply Term.Seq Tz :=
    eo_typeof_str_rev_arg_eq (__eo_typeof z1) Tz hRevZTy
  rw [prog_seq_rev_concat_eq x1 y1 z1 T1 Tz hX1 hY1 hZ1 hX1Ty hRevZTy hY1List hElim]
    at hTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply Term.str_rev
        (mkConcat x1 (__eo_list_concat_rec y1
          (mkConcat z1 (__seq_empty (__eo_typeof x1)))))))
      (__eo_typeof (mkConcat (Term.Apply Term.str_rev z1)
        (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
          (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))))) = Term.Bool
    at hTy
  obtain ⟨hLhsNe, hRhsNe⟩ := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hTyEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
  -- Decompose LHS typeof.
  change __eo_typeof_str_rev
      (__eo_typeof_str_concat (__eo_typeof x1)
        (__eo_typeof (__eo_list_concat_rec y1
          (mkConcat z1 (__seq_empty (__eo_typeof x1)))))) ≠ Term.Stuck at hLhsNe
  obtain ⟨U, hUEq⟩ := eo_typeof_str_rev_arg_seq _ hLhsNe
  obtain ⟨hX1U, hBigU⟩ := eo_typeof_str_concat_args_seq _ _ U hUEq
  -- U = T1
  have hUT1 : U = T1 := by
    have hcopy := hX1U; rw [hX1Ty] at hcopy; exact (Term.Apply.inj hcopy).2.symm
  -- typeof LHS = Seq U
  have hLhsTy : __eo_typeof (Term.Apply Term.str_rev
      (mkConcat x1 (__eo_list_concat_rec y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1)))))) = Term.Apply Term.Seq U := by
    show __eo_typeof_str_rev
        (__eo_typeof_str_concat (__eo_typeof x1)
          (__eo_typeof (__eo_list_concat_rec y1
            (mkConcat z1 (__seq_empty (__eo_typeof x1)))))) = Term.Apply Term.Seq U
    rw [hUEq, typeof_str_rev_seq]
  -- typeof RHS = Seq U
  have hRhsTy : __eo_typeof (mkConcat (Term.Apply Term.str_rev z1)
      (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
        (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) =
        Term.Apply Term.Seq U := by
    rw [← hTyEq, hLhsTy]
  -- Decompose RHS typeof to get typeof SE = Seq U.
  change __eo_typeof_str_concat (__eo_typeof (Term.Apply Term.str_rev z1))
      (__eo_typeof (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
        (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) =
        Term.Apply Term.Seq U at hRhsTy
  obtain ⟨hRevZU, hInnerU⟩ := eo_typeof_str_concat_args_seq _ _ U hRhsTy
  change __eo_typeof_str_concat
      (__eo_typeof (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1))))
      (__eo_typeof (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))) =
        Term.Apply Term.Seq U at hInnerU
  obtain ⟨hRevSEU, hNilU⟩ := eo_typeof_str_concat_args_seq _ _ U hInnerU
  have hSEU : __eo_typeof (__str_nary_elim (mkConcat x1 y1)) = Term.Apply Term.Seq U := by
    have : __eo_typeof_str_rev (__eo_typeof (__str_nary_elim (mkConcat x1 y1))) =
        Term.Apply Term.Seq U := hRevSEU
    exact eo_typeof_str_rev_arg_eq _ U this
  -- Assemble the common type T := U.
  refine ⟨U, ?_, ?_, hY1List, hElim, ?_⟩
  · rw [hX1Ty, hUT1]
  · exact eo_typeof_str_rev_arg_eq (__eo_typeof z1) U hRevZU
  · obtain ⟨b, hb⟩ := eo_is_list_nil_str_concat_boolean_of_ne_stuck y1 hY1
    cases b
    · right
      have hSEconcat : __str_nary_elim (mkConcat x1 y1) = mkConcat x1 y1 :=
        nary_elim_eq_concat_of_not_nil x1 y1 hY1List hb
      rw [hSEconcat] at hSEU
      change __eo_typeof_str_concat (__eo_typeof x1) (__eo_typeof y1) =
        Term.Apply Term.Seq U at hSEU
      obtain ⟨_, hY1U⟩ := eo_typeof_str_concat_args_seq _ _ U hSEU
      exact hY1U
    · exact Or.inl hb

/-! ## Impl lemmas -/

/-- The shape of a `str_concat`-nil. -/
private theorem is_list_nil_cases (y1 : Term)
    (h : __eo_is_list_nil Term.str_concat y1 = Term.Boolean true) :
    y1 = Term.String [] ∨ ∃ A, y1 = Term.UOp1 UserOp1.seq_empty A := by
  cases y1 <;>
    simp_all [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq]
  case UOp1 op A =>
    cases op <;>
      simp_all [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq]

/-- A nil-list left argument collapses `list_concat_rec` to its right argument. -/
private theorem list_concat_rec_nil (y1 z : Term) (hz : z ≠ Term.Stuck)
    (h : __eo_is_list_nil Term.str_concat y1 = Term.Boolean true) :
    __eo_list_concat_rec y1 z = z := by
  rcases is_list_nil_cases y1 h with rfl | ⟨A, rfl⟩ <;>
    (cases z <;> first | exact absurd rfl hz | rfl)

/-- A sequence-typed term evaluates to a canonical `Seq` value with the right element type. -/
private theorem seq_eval_canonical (M : SmtModel) (hM : model_wf M)
    (a : Term) (T : SmtType)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    ∃ s, __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq s ∧
      __smtx_elem_typeof_seq_value s = T := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) = SmtType.Seq T := by
    simpa [haTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a) (by
        unfold term_has_non_none_type; rw [haTy]; simp)
  rcases seq_value_canonical hValTy with ⟨s, hs⟩
  exact ⟨s, hs,
    elem_typeof_seq_value_of_typeof_seq_value (by
      simpa [hs, __smtx_typeof_value] using hValTy)⟩

/-- `str_rev` lifts the value relation through translation. -/
private theorem smt_value_rel_str_rev_term (M : SmtModel) (a b : Term)
    (h : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev a)))
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev b))) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt a)))
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt b)))
  rw [smtx_eval_str_rev_term_eq, smtx_eval_str_rev_term_eq]
  exact smt_value_rel_model_eval_str_rev_of_rel _ _ h

/-- `rev(a ++ (b ++ c)) = rev(c) ++ rev(a ++ b)` at the value level. -/
private theorem eval_rev_concat3 (M : SmtModel) (hM : model_wf M)
    (a b c : Term) (T : SmtType)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hbTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply Term.str_rev (mkConcat a (mkConcat b c)))) =
      __smtx_model_eval M
        (__eo_to_smt (mkConcat (Term.Apply Term.str_rev c)
          (Term.Apply Term.str_rev (mkConcat a b)))) := by
  obtain ⟨sa, hsa, hea⟩ := seq_eval_canonical M hM a T haTy
  obtain ⟨sb, hsb, heb⟩ := seq_eval_canonical M hM b T hbTy
  obtain ⟨sc, hsc, hec⟩ := seq_eval_canonical M hM c T hcTy
  have hL :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_rev (mkConcat a (mkConcat b c)))) =
        SmtValue.Seq (native_pack_seq T
          (List.reverse (native_unpack_seq sa ++
            (native_unpack_seq sb ++ native_unpack_seq sc)))) := by
    change __smtx_model_eval M (SmtTerm.str_rev
      (__eo_to_smt (mkConcat a (mkConcat b c)))) = _
    rw [smtx_eval_str_rev_term_eq, smtx_model_eval_str_concat_term_eq,
      smtx_model_eval_str_concat_term_eq, hsa, hsb, hsc]
    simp only [__smtx_model_eval_str_concat, __smtx_model_eval_str_rev,
      native_seq_concat, native_seq_rev, hea, heb, hec, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq]
  have hR :
      __smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_rev c)
            (Term.Apply Term.str_rev (mkConcat a b)))) =
        SmtValue.Seq (native_pack_seq T
          (List.reverse (native_unpack_seq sc) ++
            List.reverse (native_unpack_seq sa ++ native_unpack_seq sb))) := by
    rw [smtx_model_eval_str_concat_term_eq]
    change __smtx_model_eval_str_concat
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt c)))
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt (mkConcat a b)))) = _
    rw [smtx_eval_str_rev_term_eq, smtx_eval_str_rev_term_eq,
      smtx_model_eval_str_concat_term_eq, hsa, hsb, hsc]
    simp only [__smtx_model_eval_str_concat, __smtx_model_eval_str_rev,
      native_seq_concat, native_seq_rev, hea, heb, hec, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq]
  rw [hL, hR, ← List.append_assoc, List.reverse_append]

/-- `rev(a ++ c) = rev(c) ++ rev(a)` at the value level. -/
private theorem eval_rev_concat2 (M : SmtModel) (hM : model_wf M)
    (a c : Term) (T : SmtType)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev (mkConcat a c))) =
      __smtx_model_eval M
        (__eo_to_smt (mkConcat (Term.Apply Term.str_rev c)
          (Term.Apply Term.str_rev a))) := by
  obtain ⟨sa, hsa, hea⟩ := seq_eval_canonical M hM a T haTy
  obtain ⟨sc, hsc, hec⟩ := seq_eval_canonical M hM c T hcTy
  have hL :
      __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev (mkConcat a c))) =
        SmtValue.Seq (native_pack_seq T
          (List.reverse (native_unpack_seq sa ++ native_unpack_seq sc))) := by
    change __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt (mkConcat a c))) = _
    rw [smtx_eval_str_rev_term_eq, smtx_model_eval_str_concat_term_eq, hsa, hsc]
    simp only [__smtx_model_eval_str_concat, __smtx_model_eval_str_rev,
      native_seq_concat, native_seq_rev, hea, hec, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq]
  have hR :
      __smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_rev c)
            (Term.Apply Term.str_rev a))) =
        SmtValue.Seq (native_pack_seq T
          (List.reverse (native_unpack_seq sc) ++
            List.reverse (native_unpack_seq sa))) := by
    rw [smtx_model_eval_str_concat_term_eq]
    change __smtx_model_eval_str_concat
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt c)))
        (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt a))) = _
    rw [smtx_eval_str_rev_term_eq, smtx_eval_str_rev_term_eq, hsa, hsc]
    simp only [__smtx_model_eval_str_rev, __smtx_model_eval_str_concat,
      native_seq_concat, native_seq_rev, hea, hec, elem_typeof_pack_seq,
      Smtm.native_unpack_pack_seq]
  rw [hL, hR, List.reverse_append]

/-- Bool-typedness of the reduced program. -/
private theorem typed_impl
    (x1 y1 z1 T : Term)
    (hX1Trans : RuleProofs.eo_has_smt_translation x1)
    (hY1Trans : RuleProofs.eo_has_smt_translation y1)
    (hZ1Trans : RuleProofs.eo_has_smt_translation z1)
    (hX1Ty : __eo_typeof x1 = Term.Apply Term.Seq T)
    (hZ1Ty : __eo_typeof z1 = Term.Apply Term.Seq T)
    (hY1List : __eo_is_list Term.str_concat y1 = Term.Boolean true)
    (hElim : __str_nary_elim (mkConcat x1 y1) ≠ Term.Stuck)
    (hY1Case : __eo_is_list_nil Term.str_concat y1 = Term.Boolean true ∨
        __eo_typeof y1 = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_seq_rev_concat x1 y1 z1) := by
  have hX1NS : x1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NS : y1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hZ1NS : z1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation z1 hZ1Trans
  have hX1SmtTy : __smtx_typeof (__eo_to_smt x1) = SmtType.Seq (__eo_to_smt_type T) :=
    smtx_typeof_of_eo_seq x1 T hX1Trans hX1Ty
  have hZ1SmtTy : __smtx_typeof (__eo_to_smt z1) = SmtType.Seq (__eo_to_smt_type T) :=
    smtx_typeof_of_eo_seq z1 T hZ1Trans hZ1Ty
  have hRevZSmtTy : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev z1)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt z1)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_rev_eq, hZ1SmtTy]; simp [__smtx_typeof_seq_op_1]
  have hNILxTy : __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x1))) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq x1 (__eo_to_smt_type T) hX1SmtTy
  have hNILv0Ty : __smtx_typeof
      (__eo_to_smt (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq (Term.Apply Term.str_rev z1) (__eo_to_smt_type T) hRevZSmtTy
  have hTAILTy : __smtx_typeof
      (__eo_to_smt (mkConcat z1 (__seq_empty (__eo_typeof x1)))) = SmtType.Seq (__eo_to_smt_type T) :=
    strConcat_typeof_concat_of_seq z1 (__seq_empty (__eo_typeof x1)) (__eo_to_smt_type T) hZ1SmtTy hNILxTy
  have hRevZTy : __eo_typeof (Term.Apply Term.str_rev z1) = Term.Apply Term.Seq T := by
    show __eo_typeof_str_rev (__eo_typeof z1) = Term.Apply Term.Seq T
    rw [hZ1Ty]; rfl
  -- BIG and SE smt types (case split on whether y1 is a nil).
  have hBigTy : __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y1
      (mkConcat z1 (__seq_empty (__eo_typeof x1))))) = SmtType.Seq (__eo_to_smt_type T) := by
    rcases hY1Case with hnil | hy1ty
    · rw [list_concat_rec_nil y1 _ (by simp [mkConcat]) hnil]; exact hTAILTy
    · exact strConcat_typeof_list_concat_rec_of_seq y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))) (__eo_to_smt_type T) hY1List
        (smtx_typeof_of_eo_seq y1 T hY1Trans hy1ty) hTAILTy
  have hSETy : __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat x1 y1))) =
      SmtType.Seq (__eo_to_smt_type T) := by
    rcases hY1Case with hnil | hy1ty
    · have : __str_nary_elim (mkConcat x1 y1) = x1 := by
        show __eo_list_singleton_elim Term.str_concat (mkConcat x1 y1) = x1
        have hList : __eo_is_list Term.str_concat (mkConcat x1 y1) = Term.Boolean true :=
          strConcat_is_list_cons_true_of_tail_list x1 y1 hY1List
        change __eo_requires (__eo_is_list Term.str_concat (mkConcat x1 y1))
            (Term.Boolean true) (__eo_list_singleton_elim_2 (mkConcat x1 y1)) = x1
        rw [hList]
        have hReqT : __eo_requires (Term.Boolean true) (Term.Boolean true)
            (__eo_list_singleton_elim_2 (mkConcat x1 y1)) =
            __eo_list_singleton_elim_2 (mkConcat x1 y1) := by
          simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
        rw [hReqT]
        change __eo_ite (__eo_is_list_nil Term.str_concat y1) x1 (mkConcat x1 y1) = x1
        rw [hnil]; rfl
      rw [this]; exact hX1SmtTy
    · have hmkTy : __smtx_typeof (__eo_to_smt (mkConcat x1 y1)) = SmtType.Seq (__eo_to_smt_type T) :=
        strConcat_typeof_concat_of_seq x1 y1 (__eo_to_smt_type T) hX1SmtTy
          (smtx_typeof_of_eo_seq y1 T hY1Trans hy1ty)
      exact smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat x1 y1) (__eo_to_smt_type T) hmkTy hElim
  rw [prog_seq_rev_concat_eq x1 y1 z1 T T hX1NS hY1NS hZ1NS hX1Ty hRevZTy hY1List hElim]
  -- types of LHS and RHS
  have hLHSTy : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev
      (mkConcat x1 (__eo_list_concat_rec y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))))))) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt
      (mkConcat x1 (__eo_list_concat_rec y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))))))) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_rev_eq,
      strConcat_typeof_concat_of_seq x1 _ (__eo_to_smt_type T) hX1SmtTy hBigTy]
    simp [__smtx_typeof_seq_op_1]
  have hStrRevSETy : __smtx_typeof
      (__eo_to_smt (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_rev
      (__eo_to_smt (__str_nary_elim (mkConcat x1 y1)))) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_rev_eq, hSETy]; simp [__smtx_typeof_seq_op_1]
  have hInnerTy : __smtx_typeof (__eo_to_smt
      (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
        (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) = SmtType.Seq (__eo_to_smt_type T) :=
    strConcat_typeof_concat_of_seq _ _ (__eo_to_smt_type T) hStrRevSETy hNILv0Ty
  have hRHSTy : __smtx_typeof (__eo_to_smt
      (mkConcat (Term.Apply Term.str_rev z1)
        (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
          (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))))) = SmtType.Seq (__eo_to_smt_type T) :=
    strConcat_typeof_concat_of_seq _ _ (__eo_to_smt_type T) hRevZSmtTy hInnerTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLHSTy, hRHSTy]) (by rw [hLHSTy]; exact seq_ne_none (__eo_to_smt_type T))

/-- Interpretation correctness of the reduced program. -/
private theorem facts_impl
    (M : SmtModel) (hM : model_wf M)
    (x1 y1 z1 T : Term)
    (hX1Trans : RuleProofs.eo_has_smt_translation x1)
    (hY1Trans : RuleProofs.eo_has_smt_translation y1)
    (hZ1Trans : RuleProofs.eo_has_smt_translation z1)
    (hX1Ty : __eo_typeof x1 = Term.Apply Term.Seq T)
    (hZ1Ty : __eo_typeof z1 = Term.Apply Term.Seq T)
    (hY1List : __eo_is_list Term.str_concat y1 = Term.Boolean true)
    (hElim : __str_nary_elim (mkConcat x1 y1) ≠ Term.Stuck)
    (hY1Case : __eo_is_list_nil Term.str_concat y1 = Term.Boolean true ∨
        __eo_typeof y1 = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_seq_rev_concat x1 y1 z1) true := by
  have hX1NS : x1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NS : y1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hZ1NS : z1 ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_smt_translation z1 hZ1Trans
  have hX1SmtTy : __smtx_typeof (__eo_to_smt x1) = SmtType.Seq (__eo_to_smt_type T) :=
    smtx_typeof_of_eo_seq x1 T hX1Trans hX1Ty
  have hZ1SmtTy : __smtx_typeof (__eo_to_smt z1) = SmtType.Seq (__eo_to_smt_type T) :=
    smtx_typeof_of_eo_seq z1 T hZ1Trans hZ1Ty
  have hRevZSmtTy : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev z1)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt z1)) = _
    rw [typeof_str_rev_eq, hZ1SmtTy]; simp [__smtx_typeof_seq_op_1]
  have hRevZTy : __eo_typeof (Term.Apply Term.str_rev z1) = Term.Apply Term.Seq T := by
    show __eo_typeof_str_rev (__eo_typeof z1) = Term.Apply Term.Seq T
    rw [hZ1Ty]; rfl
  have hNILxTy : __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x1))) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq x1 (__eo_to_smt_type T) hX1SmtTy
  have hNILv0Ty : __smtx_typeof
      (__eo_to_smt (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_seq_empty_typeof_of_smt_type_seq (Term.Apply Term.str_rev z1)
      (__eo_to_smt_type T) hRevZSmtTy
  have hTAILTy : __smtx_typeof
      (__eo_to_smt (mkConcat z1 (__seq_empty (__eo_typeof x1)))) =
      SmtType.Seq (__eo_to_smt_type T) :=
    strConcat_typeof_concat_of_seq z1 (__seq_empty (__eo_typeof x1))
      (__eo_to_smt_type T) hZ1SmtTy hNILxTy
  -- empty relations
  have hNILxNil : __eo_is_list_nil Term.str_concat (__seq_empty (__eo_typeof x1)) =
      Term.Boolean true := is_list_nil_seq_empty_seq (__eo_typeof x1) T hX1Ty
  have hNILxRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x1))))
      (SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T))) :=
    smt_value_rel_str_concat_nil_empty M (__seq_empty (__eo_typeof x1))
      (__eo_to_smt_type T) hNILxNil hNILxTy
  have hNILv0Nil : __eo_is_list_nil Term.str_concat
      (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))) = Term.Boolean true :=
    is_list_nil_seq_empty_seq (__eo_typeof (Term.Apply Term.str_rev z1)) T hRevZTy
  have hNILv0Rel : RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))))
      (SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T))) :=
    smt_value_rel_str_concat_nil_empty M
      (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))
      (__eo_to_smt_type T) hNILv0Nil hNILv0Ty
  have hTailDrop : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat z1 (__seq_empty (__eo_typeof x1)))))
      (__smtx_model_eval M (__eo_to_smt z1)) :=
    smt_value_rel_str_concat_right_of_rel_empty M hM z1 (__seq_empty (__eo_typeof x1))
      (__eo_to_smt_type T) hZ1SmtTy hNILxTy hNILxRel
  have hBool := typed_impl x1 y1 z1 T hX1Trans hY1Trans hZ1Trans hX1Ty hZ1Ty hY1List
    hElim hY1Case
  rw [prog_seq_rev_concat_eq x1 y1 z1 T T hX1NS hY1NS hZ1NS hX1Ty hRevZTy hY1List hElim]
    at hBool ⊢
  refine RuleProofs.eo_interprets_eq_of_rel M _ _ hBool ?_
  rcases hY1Case with hnil | hy1ty
  · -- nil case: BIG = TAIL, SE = x1
    have hBigEq : __eo_list_concat_rec y1 (mkConcat z1 (__seq_empty (__eo_typeof x1))) =
        mkConcat z1 (__seq_empty (__eo_typeof x1)) :=
      list_concat_rec_nil y1 _ (by simp [mkConcat]) hnil
    have hSEeq : __str_nary_elim (mkConcat x1 y1) = x1 :=
      nary_elim_eq_self_of_nil x1 y1 hY1List hnil
    rw [hBigEq, hSEeq]
    have hRevX1Ty : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev x1)) =
        SmtType.Seq (__eo_to_smt_type T) := by
      change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x1)) = _
      rw [typeof_str_rev_eq, hX1SmtTy]; simp [__smtx_typeof_seq_op_1]
    have hInnerTy : __smtx_typeof (__eo_to_smt
        (mkConcat (Term.Apply Term.str_rev x1)
          (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) =
        SmtType.Seq (__eo_to_smt_type T) :=
      strConcat_typeof_concat_of_seq _ _ (__eo_to_smt_type T) hRevX1Ty hNILv0Ty
    -- LHS side
    have hX1TailToX1Z : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat x1 (mkConcat z1 (__seq_empty (__eo_typeof x1))))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat x1 z1))) :=
      strConcat_smt_value_rel_right_congr M hM x1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))) z1
        (__eo_to_smt_type T) hX1SmtTy hTAILTy hZ1SmtTy hTailDrop
    have hLHSrel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev
          (mkConcat x1 (mkConcat z1 (__seq_empty (__eo_typeof x1)))))))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev (mkConcat x1 z1)))) :=
      smt_value_rel_str_rev_term M _ _ hX1TailToX1Z
    have heval2 := eval_rev_concat2 M hM x1 z1 (__eo_to_smt_type T) hX1SmtTy hZ1SmtTy
    have hLHStoTarget : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev
          (mkConcat x1 (mkConcat z1 (__seq_empty (__eo_typeof x1)))))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1) (Term.Apply Term.str_rev x1)))) := by
      rw [← heval2]; exact hLHSrel
    -- RHS side
    have hNILv0Drop : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev x1)
            (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev x1))) :=
      smt_value_rel_str_concat_right_of_rel_empty M hM (Term.Apply Term.str_rev x1)
        (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))
        (__eo_to_smt_type T) hRevX1Ty hNILv0Ty hNILv0Rel
    have hRHStoTarget : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1)
            (mkConcat (Term.Apply Term.str_rev x1)
              (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1) (Term.Apply Term.str_rev x1)))) :=
      strConcat_smt_value_rel_right_congr M hM (Term.Apply Term.str_rev z1) _
        (Term.Apply Term.str_rev x1) (__eo_to_smt_type T) hRevZSmtTy hInnerTy hRevX1Ty
        hNILv0Drop
    exact RuleProofs.smt_value_rel_trans _ _ _ hLHStoTarget
      (RuleProofs.smt_value_rel_symm _ _ hRHStoTarget)
  · -- non-nil case
    have hY1SmtTy : __smtx_typeof (__eo_to_smt y1) = SmtType.Seq (__eo_to_smt_type T) :=
      smtx_typeof_of_eo_seq y1 T hY1Trans hy1ty
    have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y1 z1)) =
        SmtType.Seq (__eo_to_smt_type T) :=
      strConcat_typeof_concat_of_seq y1 z1 (__eo_to_smt_type T) hY1SmtTy hZ1SmtTy
    have hBigTy : __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))))) =
        SmtType.Seq (__eo_to_smt_type T) :=
      strConcat_typeof_list_concat_rec_of_seq y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))) (__eo_to_smt_type T) hY1List
        hY1SmtTy hTAILTy
    have hmkXYTy : __smtx_typeof (__eo_to_smt (mkConcat x1 y1)) =
        SmtType.Seq (__eo_to_smt_type T) :=
      strConcat_typeof_concat_of_seq x1 y1 (__eo_to_smt_type T) hX1SmtTy hY1SmtTy
    have hRevMkXYTy : __smtx_typeof
        (__eo_to_smt (Term.Apply Term.str_rev (mkConcat x1 y1))) =
        SmtType.Seq (__eo_to_smt_type T) := by
      change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt (mkConcat x1 y1))) = _
      rw [typeof_str_rev_eq, hmkXYTy]; simp [__smtx_typeof_seq_op_1]
    have hSETyS : __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat x1 y1))) =
        SmtType.Seq (__eo_to_smt_type T) :=
      smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat x1 y1) (__eo_to_smt_type T)
        hmkXYTy hElim
    have hStrRevSETy : __smtx_typeof
        (__eo_to_smt (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))) =
        SmtType.Seq (__eo_to_smt_type T) := by
      change __smtx_typeof
        (SmtTerm.str_rev (__eo_to_smt (__str_nary_elim (mkConcat x1 y1)))) = _
      rw [typeof_str_rev_eq, hSETyS]; simp [__smtx_typeof_seq_op_1]
    have hInnerTy : __smtx_typeof (__eo_to_smt
        (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
          (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))) =
        SmtType.Seq (__eo_to_smt_type T) :=
      strConcat_typeof_concat_of_seq _ _ (__eo_to_smt_type T) hStrRevSETy hNILv0Ty
    -- LHS side
    have hBigRel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec y1
          (mkConcat z1 (__seq_empty (__eo_typeof x1))))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat y1 (mkConcat z1 (__seq_empty (__eo_typeof x1)))))) :=
      strConcat_smt_value_rel_list_concat_rec M hM y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))) (__eo_to_smt_type T) hY1List
        hY1SmtTy hTAILTy
    have hTailDropUnderY : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat y1 (mkConcat z1 (__seq_empty (__eo_typeof x1))))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat y1 z1))) :=
      strConcat_smt_value_rel_right_congr M hM y1
        (mkConcat z1 (__seq_empty (__eo_typeof x1))) z1
        (__eo_to_smt_type T) hY1SmtTy hTAILTy hZ1SmtTy hTailDrop
    have hBigToYZ := RuleProofs.smt_value_rel_trans _ _ _ hBigRel hTailDropUnderY
    have hX1BigToFull : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat x1 (__eo_list_concat_rec y1
          (mkConcat z1 (__seq_empty (__eo_typeof x1)))))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat x1 (mkConcat y1 z1)))) :=
      strConcat_smt_value_rel_right_congr M hM x1 _ (mkConcat y1 z1)
        (__eo_to_smt_type T) hX1SmtTy hBigTy hYZTy hBigToYZ
    have hLHSrel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev
          (mkConcat x1 (__eo_list_concat_rec y1
            (mkConcat z1 (__seq_empty (__eo_typeof x1))))))))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev
          (mkConcat x1 (mkConcat y1 z1))))) :=
      smt_value_rel_str_rev_term M _ _ hX1BigToFull
    have heval3 := eval_rev_concat3 M hM x1 y1 z1 (__eo_to_smt_type T) hX1SmtTy hY1SmtTy
      hZ1SmtTy
    have hLHStoTarget : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_rev
          (mkConcat x1 (__eo_list_concat_rec y1
            (mkConcat z1 (__seq_empty (__eo_typeof x1))))))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1)
            (Term.Apply Term.str_rev (mkConcat x1 y1))))) := by
      rw [← heval3]; exact hLHSrel
    -- RHS side
    have hSERel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim (mkConcat x1 y1))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat x1 y1))) :=
      smt_value_rel_str_nary_elim M hM (mkConcat x1 y1) (__eo_to_smt_type T) hmkXYTy hElim
    have hRevSERel : RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_rev (mkConcat x1 y1)))) :=
      smt_value_rel_str_rev_term M _ _ hSERel
    have hNILv0Drop : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
            (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1))))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1))))) :=
      smt_value_rel_str_concat_right_of_rel_empty M hM
        (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
        (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))
        (__eo_to_smt_type T) hStrRevSETy hNILv0Ty hNILv0Rel
    have hInnerToRevXY := RuleProofs.smt_value_rel_trans _ _ _ hNILv0Drop hRevSERel
    have hRHStoTarget : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1)
            (mkConcat (Term.Apply Term.str_rev (__str_nary_elim (mkConcat x1 y1)))
              (__seq_empty (__eo_typeof (Term.Apply Term.str_rev z1)))))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply Term.str_rev z1)
            (Term.Apply Term.str_rev (mkConcat x1 y1))))) :=
      strConcat_smt_value_rel_right_congr M hM (Term.Apply Term.str_rev z1) _
        (Term.Apply Term.str_rev (mkConcat x1 y1)) (__eo_to_smt_type T) hRevZSmtTy
        hInnerTy hRevMkXYTy hInnerToRevXY
    exact RuleProofs.smt_value_rel_trans _ _ _ hLHStoTarget
      (RuleProofs.smt_value_rel_symm _ _ hRHStoTarget)

/-! ## Wrapper -/

public theorem cmd_step_seq_rev_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_rev_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_rev_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_rev_concat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_rev_concat args premises ≠
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
                      have hA1NS : a1 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                      have hA2NS : a2 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                      have hA3NS : a3 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
                      change __eo_typeof (__eo_prog_seq_rev_concat a1 a2 a3) =
                        Term.Bool at hResultTy
                      obtain ⟨T, hA1Ty, hA3Ty, hY1List, hElim, hY1Case⟩ :=
                        typeof_args_of_prog_bool a1 a2 a3 hA1NS hA2NS hA3NS hResultTy
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_seq_rev_concat a1 a2 a3) := by
                        refine ⟨?_,
                          RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (typed_impl a1 a2 a3 T hA1Trans hA2Trans hA3Trans hA1Ty
                              hA3Ty hY1List hElim hY1Case)⟩
                        intro _hTrue
                        exact facts_impl M hM a1 a2 a3 T hA1Trans hA2Trans hA3Trans
                          hA1Ty hA3Ty hY1List hElim hY1Case
                      change StepRuleProperties M []
                        (__eo_prog_seq_rev_concat a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
