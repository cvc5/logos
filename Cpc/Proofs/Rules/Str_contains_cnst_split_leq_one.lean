module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev cnstSplitLenPremise (c : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len c))
    (Term.Numeral 1)

private abbrev cnstSplitLeqPremise (t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.leq (Term.Apply Term.str_len t))
        (Term.Numeral 1)))
    (Term.Boolean true)

private abbrev cnstSplitTail (d ds : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat d) ds

private abbrev cnstSplitFlatTail (d ds : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
    (cnstSplitTail d ds)

private abbrev cnstSplitWhole (c d ds : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat c) (cnstSplitTail d ds)

private abbrev cnstSplitContains (x w : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) w

private abbrev cnstSplitSelfEq (c t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq c) t

private abbrev cnstSplitRhs (c d ds t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.or (cnstSplitSelfEq c t))
    (Term.Apply
      (Term.Apply Term.or
        (cnstSplitContains (cnstSplitFlatTail d ds) t))
      (Term.Boolean false))

private abbrev cnstSplitConclusion (c d ds t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (cnstSplitContains (cnstSplitWhole c d ds) t))
    (cnstSplitRhs c d ds t)

private abbrev cnstSplitGeneratedContains (d ds t : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.str_contains)
      (cnstSplitFlatTail d ds)) t

private abbrev cnstSplitGeneratedRhs (c d ds t : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.or) (cnstSplitSelfEq c t))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.or)
        (cnstSplitGeneratedContains d ds t))
      (Term.Boolean false))

private abbrev cnstSplitGeneratedConclusion (c d ds t : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (cnstSplitContains (cnstSplitWhole c d ds) t))
    (cnstSplitGeneratedRhs c d ds t)

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem generated_conclusion_eq
    (c d ds t : Term)
    (hFlat : cnstSplitFlatTail d ds ≠ Term.Stuck)
    (hT : t ≠ Term.Stuck) :
    cnstSplitGeneratedConclusion c d ds t =
      cnstSplitConclusion c d ds t := by
  have hContainsHead :
      __eo_mk_apply (Term.UOp UserOp.str_contains)
          (cnstSplitFlatTail d ds) =
        Term.Apply (Term.UOp UserOp.str_contains)
          (cnstSplitFlatTail d ds) :=
    mk_apply_eq _ _ (by simp) hFlat
  have hContains : cnstSplitGeneratedContains d ds t =
      cnstSplitContains (cnstSplitFlatTail d ds) t := by
    rw [cnstSplitGeneratedContains, hContainsHead]
    exact mk_apply_eq _ _ (by simp) hT
  have hOrHead :
      __eo_mk_apply (Term.UOp UserOp.or)
          (cnstSplitGeneratedContains d ds t) =
        Term.Apply (Term.UOp UserOp.or)
          (cnstSplitContains (cnstSplitFlatTail d ds) t) := by
    rw [hContains]
    exact mk_apply_eq _ _ (by simp) (by simp)
  have hInner :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or)
            (cnstSplitGeneratedContains d ds t))
          (Term.Boolean false) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (cnstSplitContains (cnstSplitFlatTail d ds) t))
          (Term.Boolean false) := by
    rw [hOrHead]
    exact mk_apply_eq _ _ (by simp) (by simp)
  have hRhs : cnstSplitGeneratedRhs c d ds t =
      cnstSplitRhs c d ds t := by
    rw [cnstSplitGeneratedRhs, hInner]
    exact mk_apply_eq _ _ (by simp) (by simp)
  rw [cnstSplitGeneratedConclusion, hRhs]
  exact mk_apply_eq _ _ (by simp) (by simp)

private theorem generated_flat_ne_stuck
    (c d ds t : Term)
    (hGenerated :
      cnstSplitGeneratedConclusion c d ds t ≠ Term.Stuck) :
    cnstSplitFlatTail d ds ≠ Term.Stuck := by
  have hRhs : cnstSplitGeneratedRhs c d ds t ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (cnstSplitContains (cnstSplitWhole c d ds) t))
      (cnstSplitGeneratedRhs c d ds t) hGenerated
  have hInner :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or)
            (cnstSplitGeneratedContains d ds t))
          (Term.Boolean false) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.or) (cnstSplitSelfEq c t)) _ hRhs
  have hOrHead :
      __eo_mk_apply (Term.UOp UserOp.or)
          (cnstSplitGeneratedContains d ds t) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ (Term.Boolean false) hInner
  have hContains :
      cnstSplitGeneratedContains d ds t ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.or) _ hOrHead
  have hContainsHead :
      __eo_mk_apply (Term.UOp UserOp.str_contains)
          (cnstSplitFlatTail d ds) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ t hContains
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_contains) _ hContainsHead

private theorem eo_typeof_cnst_split_contains_args_of_ne_stuck
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

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_contains_singleton_singleton
    (x y : SmtValue) :
    native_seq_contains [x] [y] = native_veq x y := by
  by_cases hxy : x = y
  · subst y
    simpa [native_veq] using native_seq_contains_self [x]
  · unfold native_seq_contains
    unfold native_seq_indexof
    have hyx : ¬ y = x := by
      intro hyx
      exact hxy hyx.symm
    simp [native_seq_indexof_rec, native_seq_prefix_eq, native_veq, hxy, hyx]

private theorem native_seq_contains_cnst_split
    (T : SmtType) (cs rest ts : List SmtValue)
    (hC : cs.length = 1) (hT : ts.length ≤ 1) :
    native_seq_contains (cs ++ rest) ts =
      SmtEval.native_or
        (native_veq (SmtValue.Seq (native_pack_seq T cs))
          (SmtValue.Seq (native_pack_seq T ts)))
        (SmtEval.native_or (native_seq_contains rest ts) false) := by
  cases ts with
  | nil =>
      simp [StrEqReplSupport.native_seq_contains_nil, SmtEval.native_or]
  | cons t tsTail =>
      cases tsTail with
      | cons _ _ => simp at hT
      | nil =>
          cases cs with
          | nil => simp at hC
          | cons c csTail =>
              cases csTail with
              | cons _ _ => simp at hC
              | nil =>
                  rw [native_seq_contains_append_of_pattern_length_one
                    [c] rest [t] rfl,
                    native_seq_contains_singleton_singleton c t]
                  by_cases hct : c = t
                  · subst t
                    simp [native_veq, native_pack_seq, SmtEval.native_or]
                  · simp [native_veq, native_pack_seq, SmtEval.native_or, hct]

private theorem prog_str_contains_cnst_split_info
    (c d ds t P₁ P₂ : Term)
    (hProg :
      __eo_prog_str_contains_cnst_split_leq_one c d ds t
          (Proof.pf P₁) (Proof.pf P₂) ≠ Term.Stuck) :
    ∃ c₀ t₀,
      P₁ = cnstSplitLenPremise c₀ ∧ P₂ = cnstSplitLeqPremise t₀ ∧
      c₀ = c ∧ t₀ = t ∧
      __eo_prog_str_contains_cnst_split_leq_one c d ds t
          (Proof.pf P₁) (Proof.pf P₂) =
        cnstSplitGeneratedConclusion c d ds t := by
  unfold __eo_prog_str_contains_cnst_split_leq_one at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ =>
    cases heq₁
    cases heq₂
    have hEqs :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEqs with ⟨hC, hT⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_cnst_split_leq_one, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, cnstSplitGeneratedConclusion,
      cnstSplitGeneratedRhs, cnstSplitGeneratedContains, cnstSplitWhole,
      cnstSplitTail, cnstSplitContains, cnstSplitFlatTail, cnstSplitSelfEq]

private theorem typed___eo_prog_str_contains_cnst_split_impl
    (c d ds t T : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hDTrans : RuleProofs.eo_has_smt_translation d)
    (hDsTrans : RuleProofs.eo_has_smt_translation ds)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hCTy : __eo_typeof c = Term.Apply Term.Seq T)
    (hDTy : __eo_typeof d = Term.Apply Term.Seq T)
    (hDsTy : __eo_typeof ds = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hFlatNe : cnstSplitFlatTail d ds ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (cnstSplitConclusion c d ds t) := by
  let tail := cnstSplitTail d ds
  let flat := cnstSplitFlatTail d ds
  let whole := cnstSplitWhole c d ds
  let lhs := cnstSplitContains whole t
  let ce := cnstSplitSelfEq c t
  let ct := cnstSplitContains flat t
  let rhs := cnstSplitRhs c d ds t
  have hCSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq c T hCTrans hCTy
  have hDSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq d T hDTrans hDTy
  have hDsSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq ds T hDsTrans hDsTy
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq d ds (__eo_to_smt_type T) hDSmtTy hDsSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt flat) =
      SmtType.Seq (__eo_to_smt_type T) := by
    exact smt_typeof_str_nary_elim_of_seq_ne_stuck
      tail (__eo_to_smt_type T) hTailTy hFlatNe
  have hWholeTy : __smtx_typeof (__eo_to_smt whole) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq c tail (__eo_to_smt_type T)
      hCSmtTy hTailTy
  have hContainsTy : ∀ a b : Term,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) →
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type T) →
      RuleProofs.eo_has_bool_type (cnstSplitContains a b) := by
    intro a b hA hB
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hA, hB, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hLhsTy := hContainsTy whole t hWholeTy hTSmtTy
  have hCeTy : RuleProofs.eo_has_bool_type ce :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type c t
      (by rw [hCSmtTy, hTSmtTy]) (by rw [hCSmtTy]; exact seq_ne_none _)
  have hCtTy := hContainsTy flat t hFlatTy hTSmtTy
  have hInnerTy : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.or ct) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args ct (Term.Boolean false)
      hCtTy RuleProofs.eo_has_bool_type_false
  have hRhsTy : RuleProofs.eo_has_bool_type rhs :=
    RuleProofs.eo_has_bool_type_or_of_bool_args ce
      (Term.Apply (Term.Apply Term.or ct) (Term.Boolean false))
      hCeTy hInnerTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_str_contains_cnst_split_impl
    (M : SmtModel) (hM : model_wf M)
    (c d ds t T : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hDTrans : RuleProofs.eo_has_smt_translation d)
    (hDsTrans : RuleProofs.eo_has_smt_translation ds)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hCTy : __eo_typeof c = Term.Apply Term.Seq T)
    (hDTy : __eo_typeof d = Term.Apply Term.Seq T)
    (hDsTy : __eo_typeof ds = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hFlatNe : cnstSplitFlatTail d ds ≠ Term.Stuck)
    (hPrem₁ : eo_interprets M (cnstSplitLenPremise c) true)
    (hPrem₂ : eo_interprets M (cnstSplitLeqPremise t) true) :
    eo_interprets M (cnstSplitConclusion c d ds t) true := by
  let tail := cnstSplitTail d ds
  let flat := cnstSplitFlatTail d ds
  let whole := cnstSplitWhole c d ds
  let lhs := cnstSplitContains whole t
  let rhs := cnstSplitRhs c d ds t
  have hBool : RuleProofs.eo_has_bool_type
      (cnstSplitConclusion c d ds t) :=
    typed___eo_prog_str_contains_cnst_split_impl
      c d ds t T hCTrans hDTrans hDsTrans hTTrans
      hCTy hDTy hDsTy hTTy hFlatNe
  have hCSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq c T hCTrans hCTy
  have hDSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq d T hDTrans hDTy
  have hDsSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq ds T hDsTrans hDsTy
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq d ds (__eo_to_smt_type T) hDSmtTy hDsSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt flat) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      tail (__eo_to_smt_type T) hTailTy hFlatNe
  have hCEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt c)
    (SmtType.Seq (__eo_to_smt_type T)) hCSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hDEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt d)
    (SmtType.Seq (__eo_to_smt_type T)) hDSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hDsEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt ds)
    (SmtType.Seq (__eo_to_smt_type T)) hDsSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hTEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt t)
    (SmtType.Seq (__eo_to_smt_type T)) hTSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hFlatEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt flat)
    (SmtType.Seq (__eo_to_smt_type T)) hFlatTy
    (seq_ne_none _) (type_inhabited_seq _)
  rcases seq_value_canonical hCEvalTy with ⟨sc, hCEval⟩
  rcases seq_value_canonical hDEvalTy with ⟨sd, hDEval⟩
  rcases seq_value_canonical hDsEvalTy with ⟨sds, hDsEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hFlatEvalTy with ⟨sflat, hFlatEval⟩
  have hCSeqTy :
      __smtx_typeof_seq_value sc = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hCEval] using hCEvalTy
  have hTSeqTy :
      __smtx_typeof_seq_value st = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hCElem : __smtx_elem_typeof_seq_value sc = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hCSeqTy
  have hTElem : __smtx_elem_typeof_seq_value st = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  let stail := native_pack_seq (__smtx_elem_typeof_seq_value sd)
    (native_unpack_seq sd ++ native_unpack_seq sds)
  have hTailEval : __smtx_model_eval M (__eo_to_smt tail) =
      SmtValue.Seq stail := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt d) (__eo_to_smt ds)) = _
    rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hDEval, hDsEval]
    rfl
  have hFlatTailRel := smt_value_rel_str_nary_elim M hM tail
    (__eo_to_smt_type T) hTailTy hFlatNe
  have hFlatTailEq : sflat = stail := by
    have hSeqRel : RuleProofs.smt_seq_rel sflat stail := by
      change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt flat))
          (__smtx_model_eval M (__eo_to_smt tail)) at hFlatTailRel
      rw [hFlatEval, hTailEval] at hFlatTailRel
      exact hFlatTailRel
    exact (RuleProofs.smt_seq_rel_iff_eq sflat stail).1 hSeqRel
  have hCLen : (native_unpack_seq sc).length = 1 := by
    have hCLenInt : native_seq_len (native_unpack_seq sc) = 1 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem₁
      cases hPrem₁ with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt c))
                (SmtTerm.Numeral 1)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hCEval,
            StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    have hCast : ((native_unpack_seq sc).length : Int) = 1 := by
      simpa [native_seq_len] using hCLenInt
    omega
  have hTLen : (native_unpack_seq st).length ≤ 1 := by
    have hTLenInt : native_zleq (native_seq_len (native_unpack_seq st)) 1 =
        true := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem₂
      cases hPrem₂ with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq
                (SmtTerm.leq (SmtTerm.str_len (__eo_to_smt t))
                  (SmtTerm.Numeral 1))
                (SmtTerm.Boolean true)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_leq_term_eq,
            smtx_eval_str_len_term_eq, hTEval,
            StrEqReplSupport.smtx_eval_numeral_term_eq,
            StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_leq,
            __smtx_model_eval_eq, native_veq] using hEval
    have hCast : ((native_unpack_seq st).length : Int) ≤ 1 := by
      simpa [native_seq_len, native_zleq] using hTLenInt
    omega
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_concat (__eo_to_smt c)
            (SmtTerm.str_concat (__eo_to_smt d) (__eo_to_smt ds)))
          (__eo_to_smt t)) =
      __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.eq (__eo_to_smt c) (__eo_to_smt t))
          (SmtTerm.or
            (SmtTerm.str_contains (__eo_to_smt flat) (__eo_to_smt t))
            (SmtTerm.Boolean false)))
    rw [StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hCEval, StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hDEval, hDsEval, hTEval, smtx_eval_or_term_eq,
      smtx_eval_eq_term_eq, hCEval, hTEval, smtx_eval_or_term_eq,
      StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
      hFlatEval, hTEval, StrEqReplSupport.smtx_eval_boolean_term_eq]
    simp only [__smtx_model_eval_str_concat, native_seq_concat,
      __smtx_model_eval_str_contains, __smtx_model_eval_or,
      __smtx_model_eval_eq, Smtm.native_unpack_pack_seq]
    rw [hFlatTailEq]
    simp only [stail, Smtm.native_unpack_pack_seq]
    rw [native_seq_contains_cnst_split (__eo_to_smt_type T)
      (native_unpack_seq sc)
      (native_unpack_seq sd ++ native_unpack_seq sds)
      (native_unpack_seq st) hCLen hTLen]
    have hScPack : native_pack_seq (__eo_to_smt_type T)
        (native_unpack_seq sc) = sc := by
      simpa [hCElem] using native_pack_unpack_seq sc
    have hStPack : native_pack_seq (__eo_to_smt_type T)
        (native_unpack_seq st) = st := by
      simpa [hTElem] using native_pack_unpack_seq st
    rw [hScPack, hStPack]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_cnst_split_leq_one_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_cnst_split_leq_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_cnst_split_leq_one args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_cnst_split_leq_one args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_cnst_split_leq_one
          args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons c args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons d args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons ds args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons t args =>
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
  have hCTrans : RuleProofs.eo_has_smt_translation c := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hDTrans : RuleProofs.eo_has_smt_translation d := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
  have hDsTrans : RuleProofs.eo_has_smt_translation ds := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.2.1
  change __eo_typeof
      (__eo_prog_str_contains_cnst_split_leq_one c d ds t
        (Proof.pf P₁) (Proof.pf P₂)) = Term.Bool at hResultTy
  have hRuleProg :
      __eo_prog_str_contains_cnst_split_leq_one c d ds t
          (Proof.pf P₁) (Proof.pf P₂) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases prog_str_contains_cnst_split_info c d ds t P₁ P₂ hRuleProg with
    ⟨c₀, t₀, hP₁, hP₂, hc₀, ht₀, hProgGenerated⟩
  subst c₀
  subst t₀
  have hGeneratedNe :
      cnstSplitGeneratedConclusion c d ds t ≠ Term.Stuck := by
    rw [← hProgGenerated]
    exact hRuleProg
  have hFlatNe := generated_flat_ne_stuck c d ds t hGeneratedNe
  have hTNe : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq :
      __eo_prog_str_contains_cnst_split_leq_one c d ds t
          (Proof.pf P₁) (Proof.pf P₂) =
        cnstSplitConclusion c d ds t := by
    rw [hProgGenerated, generated_conclusion_eq c d ds t hFlatNe hTNe]
  change __eo_typeof
      (__eo_prog_str_contains_cnst_split_leq_one c d ds t
        (Proof.pf P₁) (Proof.pf P₂)) = Term.Bool at hResultTy
  rw [hProgEq] at hResultTy
  have hOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (cnstSplitContains (cnstSplitWhole c d ds) t))
      (__eo_typeof (cnstSplitRhs c d ds t)) hResultTy
  have hLhsNN := hOps.1
  change __eo_typeof_str_contains
      (__eo_typeof (cnstSplitWhole c d ds)) (__eo_typeof t) ≠
    Term.Stuck at hLhsNN
  rcases eo_typeof_cnst_split_contains_args_of_ne_stuck
      (__eo_typeof (cnstSplitWhole c d ds)) (__eo_typeof t) hLhsNN with
    ⟨T, hWholeTy, hTTy⟩
  have hWholeArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      c (cnstSplitTail d ds) T hWholeTy
  have hTailArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      d ds T hWholeArgs.2
  change StepRuleProperties M [P₁, P₂]
    (__eo_prog_str_contains_cnst_split_leq_one c d ds t
      (Proof.pf P₁) (Proof.pf P₂))
  rw [hProgEq]
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hPrem₁Raw : eo_interprets M P₁ true :=
      hTrue P₁ (by simp)
    have hPrem₂Raw : eo_interprets M P₂ true :=
      hTrue P₂ (by simp)
    have hPrem₁ : eo_interprets M (cnstSplitLenPremise c) true := by
      simpa [hP₁] using hPrem₁Raw
    have hPrem₂ : eo_interprets M (cnstSplitLeqPremise t) true := by
      simpa [hP₂] using hPrem₂Raw
    exact facts___eo_prog_str_contains_cnst_split_impl
      M hM c d ds t T hCTrans hDTrans hDsTrans hTTrans
      hWholeArgs.1 hTailArgs.1 hTailArgs.2 hTTy hFlatNe hPrem₁ hPrem₂
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed___eo_prog_str_contains_cnst_split_impl
        c d ds t T hCTrans hDTrans hDsTrans hTTrans
        hWholeArgs.1 hTailArgs.1 hTailArgs.2 hTTy hFlatNe)
