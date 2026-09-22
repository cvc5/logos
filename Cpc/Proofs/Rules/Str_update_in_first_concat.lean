module

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev updateFirstNonnegPremise (n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq n) (Term.Numeral 0)))
    (Term.Boolean true)

private abbrev updateFirstStart (n s : Term) : Term :=
  Term.Apply (Term.Apply Term.plus n)
    (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len s))
      (Term.Numeral 0))

private abbrev updateFirstBoundPremise (t s n : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.leq (updateFirstStart n s))
        (Term.Apply Term.str_len t)))
    (Term.Boolean true)

private abbrev updateFirstPrePremise (t n pre : Term) : Term :=
  Term.Apply (Term.Apply Term.eq pre)
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr t)
      (Term.Numeral 0)) n)

private abbrev updateFirstPostPremise
    (t s n post : Term) : Term :=
  Term.Apply (Term.Apply Term.eq post)
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr t)
      (updateFirstStart n s)) (Term.Apply Term.str_len t))

private abbrev updateFirstSource (t tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t) tail

private abbrev updateFirstLeft (t tail s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_update
    (updateFirstSource t tail)) n) s

private abbrev updateFirstRight
    (pre s post tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat pre)
    (Term.Apply (Term.Apply Term.str_concat s)
      (Term.Apply (Term.Apply Term.str_concat post) tail))

private abbrev updateFirstConclusion
    (t tail s n pre post : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (updateFirstLeft t tail s n))
    (updateFirstRight pre s post tail)

private theorem prog_str_update_in_first_concat_info
    (t tail s n pre post P1 P2 P3 P4 : Term)
    (hProg :
      __eo_prog_str_update_in_first_concat t tail s n pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) ≠
        Term.Stuck) :
    P1 = updateFirstNonnegPremise n ∧
      P2 = updateFirstBoundPremise t s n ∧
      P3 = updateFirstPrePremise t n pre ∧
      P4 = updateFirstPostPremise t s n post ∧
      __eo_prog_str_update_in_first_concat t tail s n pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) =
        updateFirstConclusion t tail s n pre post := by
  unfold __eo_prog_str_update_in_first_concat at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 heq3 heq4 =>
    cases heq1
    cases heq2
    cases heq3
    cases heq4
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
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_update_in_first_concat, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, updateFirstConclusion, updateFirstLeft,
      updateFirstRight, updateFirstSource]

private theorem eo_typeof_str_update_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int ∧
      C = Term.Apply Term.Seq T := by
  cases A <;> try simp [__eo_typeof_str_update] at h
  case Apply fA aA =>
    cases fA <;> try simp at h
    case UOp opA =>
      cases opA <;> try simp at h
      case Seq =>
        cases B <;> try simp at h
        case UOp opB =>
          cases opB <;> try simp at h
          case Int =>
            cases C <;> try simp at h
            case Apply fC aC =>
              cases fC <;> try simp at h
              case UOp opC =>
                cases opC <;> try simp at h
                case Seq =>
                  have hCond : __eo_eq aA aC = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hCA : aC = aA :=
                    support_eq_of_eo_eq_true aA aC hCond
                  subst aC
                  simp

private theorem smtx_eval_str_update_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y z) =
      __smtx_model_eval_str_update
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_str_update_in_first_concat_impl
    (t tail s n pre post P1 P2 P3 P4 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_update_in_first_concat t tail s n pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) =
        updateFirstConclusion t tail s n pre post) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_update_in_first_concat t tail s n pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)) := by
  let source := updateFirstSource t tail
  let lhs := updateFirstLeft t tail s n
  let postTail := Term.Apply (Term.Apply Term.str_concat post) tail
  let sPostTail := Term.Apply (Term.Apply Term.str_concat s) postTail
  let rhs := updateFirstRight pre s post tail
  have hTSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
  have hSSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy :=
    StrSubstrContainsSupport.smtx_typeof_of_eo_int n hNTrans hNTy
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
        (SmtTerm.str_update (__eo_to_smt source) (__eo_to_smt n)
          (__eo_to_smt s)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_update_eq]
    simp [hSourceTy, hNSmtTy, hSSmtTy, __smtx_typeof_str_update,
      native_ite, native_Teq]
  have hPostTailTy : __smtx_typeof (__eo_to_smt postTail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt post) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPostSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hSPostTailTy : __smtx_typeof (__eo_to_smt sPostTail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt postTail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hSSmtTy, hPostTailTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt pre)
          (__eo_to_smt sPostTail)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPreSmtTy, hSPostTailTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (updateFirstConclusion t tail s n pre post) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_update_in_first_concat_impl
    (M : SmtModel) (hM : model_wf M)
    (t tail s n pre post P1 P2 P3 P4 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (updateFirstNonnegPremise n) true)
    (hPrem2 : eo_interprets M (updateFirstBoundPremise t s n) true)
    (hPrem3 : eo_interprets M (updateFirstPrePremise t n pre) true)
    (hPrem4 : eo_interprets M (updateFirstPostPremise t s n post) true)
    (hProgEq :
      __eo_prog_str_update_in_first_concat t tail s n pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) =
        updateFirstConclusion t tail s n pre post) :
    eo_interprets M
      (__eo_prog_str_update_in_first_concat t tail s n pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)) true := by
  let source := updateFirstSource t tail
  let lhs := updateFirstLeft t tail s n
  let rhs := updateFirstRight pre s post tail
  have hBool : RuleProofs.eo_has_bool_type
      (updateFirstConclusion t tail s n pre post) := by
    simpa [hProgEq] using
      typed___eo_prog_str_update_in_first_concat_impl
        t tail s n pre post P1 P2 P3 P4 T hTTrans hTailTrans hSTrans
        hNTrans hPreTrans hPostTrans hTTy hTailTy hSTy hNTy hPreTy
        hPostTy hProgEq
  have hTSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
  have hSSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy :=
    StrSubstrContainsSupport.smtx_typeof_of_eo_int n hNTrans hNTy
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
  have hSEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hNEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hNSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
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
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases seq_value_canonical hPreEvalTy with ⟨spre, hPreEval⟩
  rcases seq_value_canonical hPostEvalTy with ⟨spost, hPostEval⟩
  have hNonneg : 0 ≤ ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrSubstrContainsSupport.smtx_eval_geq_term_eq, hNEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 ni = true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, native_veq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  have hFit :
      ni + Int.ofNat (native_unpack_seq ss).length ≤
        Int.ofNat (native_unpack_seq st).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.leq
                (SmtTerm.plus (__eo_to_smt n)
                  (SmtTerm.plus
                    (SmtTerm.str_len (__eo_to_smt s))
                    (SmtTerm.Numeral 0)))
                (SmtTerm.str_len (__eo_to_smt t)))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_leq_term_eq,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
          hNEval, hSEval, hTEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, __smtx_model_eval_leq,
          __smtx_model_eval_plus, __smtx_model_eval_str_len,
          native_veq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_seq_len] using hEval
  let unpackValue : SmtValue -> List SmtValue
    | SmtValue.Seq xs => native_unpack_seq xs
    | _ => []
  have hPreExtract :
      native_unpack_seq spre =
        native_seq_extract (native_unpack_seq st) 0 ni := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt pre)
              (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                (__eo_to_smt n))) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPreEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hTEval, StrEqReplSupport.smtx_eval_numeral_term_eq,
          hNEval] at hEval
        have hBool :
            decide
              (SmtValue.Seq spre =
                SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value st)
                    (native_seq_extract (native_unpack_seq st) 0 ni))) =
              true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_str_substr,
            native_veq] using hEval
        have hValueEq := of_decide_eq_true hBool
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hPostExtract :
      native_unpack_seq spost =
        native_seq_extract (native_unpack_seq st)
          (ni + Int.ofNat (native_unpack_seq ss).length)
          (native_seq_len (native_unpack_seq st)) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem4
    cases hPrem4 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt post)
              (SmtTerm.str_substr (__eo_to_smt t)
                (SmtTerm.plus (__eo_to_smt n)
                  (SmtTerm.plus
                    (SmtTerm.str_len (__eo_to_smt s))
                    (SmtTerm.Numeral 0)))
                (SmtTerm.str_len (__eo_to_smt t)))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPostEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hTEval, StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          hNEval, smtx_eval_str_len_term_eq, hSEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          smtx_eval_str_len_term_eq, hTEval] at hEval
        have hBool :
            decide
              (SmtValue.Seq spost =
                SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value st)
                    (native_seq_extract (native_unpack_seq st)
                      (ni + Int.ofNat (native_unpack_seq ss).length)
                      (native_seq_len (native_unpack_seq st))))) = true := by
          simpa [__smtx_model_eval_eq, __smtx_model_eval_str_substr,
            __smtx_model_eval_plus, __smtx_model_eval_str_len,
            native_veq, native_zplus, SmtEval.native_zplus,
            native_seq_len] using hEval
        have hValueEq := of_decide_eq_true hBool
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hIdxCast : (Int.toNat ni : Int) = ni :=
    Int.toNat_of_nonneg hNonneg
  have hFitNat :
      Int.toNat ni + (native_unpack_seq ss).length ≤
        (native_unpack_seq st).length := by
    have hFitCast := hFit
    rw [← hIdxCast] at hFitCast
    apply Int.ofNat_le.mp
    simpa using hFitCast
  have hIdxLe : Int.toNat ni ≤ (native_unpack_seq st).length := by omega
  have hPreList :
      native_unpack_seq spre =
        (native_unpack_seq st).take (Int.toNat ni) := by
    rw [hPreExtract, ← hIdxCast]
    exact native_seq_extract_zero_nat _ _ hIdxLe
  have hStartNonneg :
      0 ≤ ni + Int.ofNat (native_unpack_seq ss).length :=
    Int.add_nonneg hNonneg (Int.natCast_nonneg _)
  have hStartLe :
      ni + Int.ofNat (native_unpack_seq ss).length ≤
        native_seq_len (native_unpack_seq st) := by
    simpa [native_seq_len] using hFit
  have hToNatStart :
      Int.toNat (ni + Int.ofNat (native_unpack_seq ss).length) =
        Int.toNat ni + (native_unpack_seq ss).length := by
    simpa using
      (Int.toNat_add hNonneg
        (Int.natCast_nonneg (native_unpack_seq ss).length))
  have hPostList :
      native_unpack_seq spost =
        (native_unpack_seq st).drop
          (Int.toNat ni + (native_unpack_seq ss).length) := by
    rw [hPostExtract,
      native_seq_extract_len_tail_of_bounds _ _ hStartNonneg hStartLe,
      hToNatStart]
  have hNativeUpdate :
      native_seq_update
          (native_unpack_seq st ++ native_unpack_seq stail) ni
          (native_unpack_seq ss) =
        native_unpack_seq spre ++ native_unpack_seq ss ++
          native_unpack_seq spost ++ native_unpack_seq stail := by
    have hUpdate := native_seq_update_append_of_fit
      (native_unpack_seq st) (native_unpack_seq stail)
      (native_unpack_seq ss) ni hNonneg hFit
    rw [← hPreList, ← hPostList] at hUpdate
    exact hUpdate
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
  have hSSeqTy : __smtx_typeof_seq_value ss =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hSEvalTy
    try simp [hSEval] at hsimpa ⊢
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
  have hTElem : __smtx_elem_typeof_seq_value st = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hTailElem : __smtx_elem_typeof_seq_value stail = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hPreElem : __smtx_elem_typeof_seq_value spre = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hPreSeqTy
  have hPostElem : __smtx_elem_typeof_seq_value spost = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hPostSeqTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_update
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail))
          (__eo_to_smt n) (__eo_to_smt s)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt pre)
          (SmtTerm.str_concat (__eo_to_smt s)
            (SmtTerm.str_concat (__eo_to_smt post) (__eo_to_smt tail))))
    rw [smtx_eval_str_update_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hTEval, hTailEval, hNEval, hSEval, hPreEval, hPostEval]
    simp [__smtx_model_eval_str_update, __smtx_model_eval_str_concat,
      native_seq_concat, Smtm.native_unpack_pack_seq, hTElem, hTailElem,
      hSElem, hPreElem, hPostElem, elem_typeof_pack_seq, hNativeUpdate]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_update_in_first_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_in_first_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_update_in_first_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_update_in_first_concat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_update_in_first_concat args premises ≠
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
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | nil => exact absurd rfl hProg
                  | cons a5 args =>
                      cases args with
                      | nil => exact absurd rfl hProg
                      | cons a6 args =>
                          cases args with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              cases premises with
                              | nil => exact absurd rfl hProg
                              | cons p1 premises =>
                                  cases premises with
                                  | nil => exact absurd rfl hProg
                                  | cons p2 premises =>
                                      cases premises with
                                      | nil => exact absurd rfl hProg
                                      | cons p3 premises =>
                                          cases premises with
                                          | nil => exact absurd rfl hProg
                                          | cons p4 premises =>
                                              cases premises with
                                              | cons _ _ => exact absurd rfl hProg
                                              | nil =>
                                                  let P1 := __eo_state_proven_nth s p1
                                                  let P2 := __eo_state_proven_nth s p2
                                                  let P3 := __eo_state_proven_nth s p3
                                                  let P4 := __eo_state_proven_nth s p4
                                                  have hA1Trans :
                                                      RuleProofs.eo_has_smt_translation a1 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.1
                                                  have hA2Trans :
                                                      RuleProofs.eo_has_smt_translation a2 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.2.1
                                                  have hA3Trans :
                                                      RuleProofs.eo_has_smt_translation a3 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.2.2.1
                                                  have hA4Trans :
                                                      RuleProofs.eo_has_smt_translation a4 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.2.2.2.1
                                                  have hA5Trans :
                                                      RuleProofs.eo_has_smt_translation a5 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.2.2.2.2.1
                                                  have hA6Trans :
                                                      RuleProofs.eo_has_smt_translation a6 := by
                                                    simpa [cmdTranslationOk,
                                                      cArgListTranslationOk] using
                                                        hCmdTrans.2.2.2.2.2.1
                                                  change __eo_typeof
                                                      (__eo_prog_str_update_in_first_concat
                                                        a1 a2 a3 a4 a5 a6
                                                        (Proof.pf P1) (Proof.pf P2)
                                                        (Proof.pf P3) (Proof.pf P4)) =
                                                    Term.Bool at hResultTy
                                                  have hRuleProg :
                                                      __eo_prog_str_update_in_first_concat
                                                          a1 a2 a3 a4 a5 a6
                                                          (Proof.pf P1) (Proof.pf P2)
                                                          (Proof.pf P3) (Proof.pf P4) ≠
                                                        Term.Stuck :=
                                                    term_ne_stuck_of_typeof_bool hResultTy
                                                  rcases
                                                      prog_str_update_in_first_concat_info
                                                        a1 a2 a3 a4 a5 a6
                                                        P1 P2 P3 P4 hRuleProg with
                                                    ⟨hP1, hP2, hP3, hP4,
                                                      hProgEq⟩
                                                  rw [hProgEq] at hResultTy
                                                  have hOps :=
                                                    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                                      (__eo_typeof
                                                        (updateFirstLeft a1 a2 a3 a4))
                                                      (__eo_typeof
                                                        (updateFirstRight a5 a3 a6 a2))
                                                      hResultTy
                                                  have hLeftNN := hOps.1
                                                  have hRightNN := hOps.2
                                                  change __eo_typeof_str_update
                                                      (__eo_typeof
                                                        (updateFirstSource a1 a2))
                                                      (__eo_typeof a4)
                                                      (__eo_typeof a3) ≠
                                                    Term.Stuck at hLeftNN
                                                  rcases
                                                      eo_typeof_str_update_args_of_ne_stuck
                                                        (__eo_typeof
                                                          (updateFirstSource a1 a2))
                                                        (__eo_typeof a4)
                                                        (__eo_typeof a3) hLeftNN with
                                                    ⟨T, hSourceTy, hA4Ty, hA3Ty⟩
                                                  have hSourceArgs :=
                                                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                      a1 a2 T hSourceTy
                                                  have hA1Ty := hSourceArgs.1
                                                  have hA2Ty := hSourceArgs.2
                                                  change __eo_typeof_str_concat
                                                      (__eo_typeof a5)
                                                      (__eo_typeof
                                                        (Term.Apply
                                                          (Term.Apply Term.str_concat a3)
                                                          (Term.Apply
                                                            (Term.Apply Term.str_concat a6)
                                                            a2))) ≠
                                                    Term.Stuck at hRightNN
                                                  rcases
                                                      StrSubstrContainsSupport.eo_typeof_str_concat_args_of_ne_stuck
                                                        (__eo_typeof a5)
                                                        (__eo_typeof
                                                          (Term.Apply
                                                            (Term.Apply Term.str_concat a3)
                                                            (Term.Apply
                                                              (Term.Apply Term.str_concat a6)
                                                              a2))) hRightNN with
                                                    ⟨U, hA5TyU, hInnerTyU⟩
                                                  have hInnerArgs :=
                                                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                      a3
                                                      (Term.Apply
                                                        (Term.Apply Term.str_concat a6) a2)
                                                      U hInnerTyU
                                                  have hPostTailArgs :=
                                                    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                                      a6 a2 U hInnerArgs.2
                                                  have hUT : U = T := by
                                                    have hSeq :
                                                        Term.Apply Term.Seq U =
                                                          Term.Apply Term.Seq T := by
                                                      rw [← hInnerArgs.1, hA3Ty]
                                                    injection hSeq
                                                  subst U
                                                  have hA5Ty := hA5TyU
                                                  have hA6Ty := hPostTailArgs.1
                                                  refine ⟨?_, ?_⟩
                                                  · intro hTrue
                                                    have hPrem1Raw :
                                                        eo_interprets M P1 true :=
                                                      hTrue P1 (by
                                                        simp [P1, premiseTermList])
                                                    have hPrem2Raw :
                                                        eo_interprets M P2 true :=
                                                      hTrue P2 (by
                                                        simp [P2, premiseTermList])
                                                    have hPrem3Raw :
                                                        eo_interprets M P3 true :=
                                                      hTrue P3 (by
                                                        simp [P3, premiseTermList])
                                                    have hPrem4Raw :
                                                        eo_interprets M P4 true :=
                                                      hTrue P4 (by
                                                        simp [P4, premiseTermList])
                                                    have hPrem1 : eo_interprets M
                                                        (updateFirstNonnegPremise a4)
                                                        true := by
                                                      simpa [hP1] using hPrem1Raw
                                                    have hPrem2 : eo_interprets M
                                                        (updateFirstBoundPremise
                                                          a1 a3 a4) true := by
                                                      simpa [hP2] using hPrem2Raw
                                                    have hPrem3 : eo_interprets M
                                                        (updateFirstPrePremise
                                                          a1 a4 a5) true := by
                                                      simpa [hP3] using hPrem3Raw
                                                    have hPrem4 : eo_interprets M
                                                        (updateFirstPostPremise
                                                          a1 a3 a4 a6) true := by
                                                      simpa [hP4] using hPrem4Raw
                                                    exact
                                                      facts___eo_prog_str_update_in_first_concat_impl
                                                        M hM a1 a2 a3 a4 a5 a6
                                                        P1 P2 P3 P4 T hA1Trans
                                                        hA2Trans hA3Trans hA4Trans
                                                        hA5Trans hA6Trans hA1Ty hA2Ty
                                                        hA3Ty hA4Ty hA5Ty hA6Ty
                                                        hPrem1 hPrem2 hPrem3 hPrem4
                                                        hProgEq
                                                  · exact
                                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _
                                                        (typed___eo_prog_str_update_in_first_concat_impl
                                                          a1 a2 a3 a4 a5 a6
                                                          P1 P2 P3 P4 T hA1Trans
                                                          hA2Trans hA3Trans hA4Trans
                                                          hA5Trans hA6Trans hA1Ty hA2Ty
                                                          hA3Ty hA4Ty hA5Ty hA6Ty
                                                          hProgEq)
