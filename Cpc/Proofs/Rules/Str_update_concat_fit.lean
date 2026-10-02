module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm
open StrConcatClashSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_update_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧ B = Term.Int ∧ C = Term.Apply Term.Seq T := by
  cases A <;> simp [__eo_typeof_str_update] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_update] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_update] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_update] at h ⊢
        case UOp opB =>
          cases opB <;> simp [__eo_typeof_str_update] at h ⊢
          case Int =>
            cases C <;>
              simp [__eo_typeof_str_update] at h ⊢
            case Apply g y =>
              cases g <;>
                simp [__eo_typeof_str_update] at h ⊢
              case UOp opC =>
                cases opC <;>
                  simp [__eo_typeof_str_update] at h ⊢
                case Seq =>
                  have hReqNe :
                      __eo_requires (__eo_eq x y) (Term.Boolean true)
                          (Term.Apply Term.Seq x) ≠ Term.Stuck := by
                    intro hReq
                    apply h
                    rw [hReq]
                  exact RuleProofs.eq_of_requires_eq_true_not_stuck x y
                    (Term.Apply Term.Seq x) hReqNe

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

private theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simpa [TranslationProofs.eo_to_smt_type_int] using hTyRaw

private theorem smtx_eval_str_update_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_update x y n) =
      __smtx_model_eval_str_update
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_seq (M : SmtModel) (hM : model_wf M) (a : Term) (T : SmtType)
    (h : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    ∃ xs, __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq xs := by
  apply seq_value_canonical
  simpa [h] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
    (term_has_non_none_of_type_eq h (by simp))


private theorem eval_concat (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat a b) =
      __smtx_model_eval_str_concat (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]


private abbrev tail (ps r qs : Term) :=
  __eo_list_concat Term.str_concat ps (mkConcat r qs)
private abbrev source (p ps r qs : Term) := mkConcat p (tail ps r qs)
private abbrev lhs (p ps r qs n x : Term) :=
  Term.Apply (Term.Apply (Term.Apply Term.str_update (source p ps r qs)) n) x
private abbrev conclusion (p ps r qs n x : Term) :=
  Term.Apply (Term.Apply Term.eq (lhs p ps r qs n x)) (source p ps x qs)

-- The generated premise places n after both parts of the prefix.
private abbrev indexPremise (p ps n : Term) :=
  Term.Apply (Term.Apply Term.eq
    (Term.Apply Term.str_len (mkConcat p (mkConcat p ps))))
    (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len p))
      (Term.Apply (Term.Apply Term.plus n) (Term.Numeral 0)))
private abbrev lengthPremise (r x : Term) :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len r)) (Term.Apply Term.str_len x)

private theorem program_info (p ps r qs n x P Q : Term)
    (hp : p ≠ Term.Stuck) (hps : ps ≠ Term.Stuck) (hr : r ≠ Term.Stuck)
    (hqs : qs ≠ Term.Stuck) (hn : n ≠ Term.Stuck) (hx : x ≠ Term.Stuck)
    (h : __eo_prog_str_update_concat_fit p ps r qs n x (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    P = indexPremise p ps n ∧ Q = lengthPremise r x ∧
    __eo_prog_str_update_concat_fit p ps r qs n x (Proof.pf P) (Proof.pf Q) =
      conclusion p ps r qs n x := by
  unfold __eo_prog_str_update_concat_fit at h
  split at h <;> try contradiction
  next heP heQ =>
    cases heP
    cases heQ
    have hg := support_eo_requires_cond_eq_of_non_stuck h
    have hx' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hr' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hn' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hp4 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hps' := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hg := StrEqReplSupport.eo_and_eq_true_left hg
    have hp3 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_right hg)
    have hp2 := RuleProofs.eq_of_eo_eq_true _ _ (StrEqReplSupport.eo_and_eq_true_left hg)
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp_all [__eo_prog_str_update_concat_fit, __eo_requires, __eo_eq, __eo_and,
      native_ite, native_teq, native_and, SmtEval.native_not, __eo_mk_apply,
      conclusion, lhs, source, tail, mkConcat]
    all_goals repeat (first | (split <;> simp_all [__eo_mk_apply]) | assumption)

private theorem indexPremise_types (p ps n : Term)
    (hBool : RuleProofs.eo_has_bool_type (indexPremise p ps n)) :
    ∃ T, __smtx_typeof (__eo_to_smt p) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.eq
    (SmtTerm.str_len (__eo_to_smt (mkConcat p (mkConcat p ps))))
    (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt p))
      (SmtTerm.plus (__eo_to_smt n) (SmtTerm.Numeral 0)))) = SmtType.Bool at hBool
  rw [typeof_eq_eq] at hBool
  have hNN := fun he => (by decide : SmtType.Bool ≠ SmtType.None) (hBool.symm.trans he)
  have hLeft := (TranslationProofs.smtx_typeof_eq_non_none hNN).2
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (R := SmtType.Int)
    (typeof_str_len_eq _) hLeft with ⟨T, hSeq⟩
  rcases str_concat_args_of_seq_type p (mkConcat p ps) T hSeq with ⟨hp, hps⟩
  exact ⟨T, hp, (str_concat_args_of_seq_type p ps T hps).2⟩

private theorem tail_type (ps r qs : Term) (T : SmtType)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hNe : tail ps r qs ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (tail ps r qs)) = SmtType.Seq T := by
  have hList := (concat_clash_rev_list_concat_facts ps (mkConcat r qs) hNe).1
  rw [show tail ps r qs = __eo_list_concat_rec ps (mkConcat r qs) from
    concat_clash_rev_list_concat_eq_rec ps (mkConcat r qs) hNe]
  exact smt_typeof_list_concat_rec_str_concat_of_seq ps (mkConcat r qs) T hList hps
    (smt_typeof_str_concat_of_seq r qs T hr hqs)

private theorem source_type (p ps r qs : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hNe : tail ps r qs ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (source p ps r qs)) = SmtType.Seq T :=
  smt_typeof_str_concat_of_seq p (tail ps r qs) T hp (tail_type ps r qs T hps hr hqs hNe)

private theorem conclusion_typed (p ps r qs n x : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNeR : tail ps r qs ≠ Term.Stuck) (hNeX : tail ps x qs ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (conclusion p ps r qs n x) := by
  have hl : __smtx_typeof (__eo_to_smt (lhs p ps r qs n x)) = SmtType.Seq T := by
    change __smtx_typeof (SmtTerm.str_update (__eo_to_smt (source p ps r qs))
      (__eo_to_smt n) (__eo_to_smt x)) = _
    rw [typeof_str_update_eq, source_type p ps r qs T hp hps hr hqs hNeR, hn, hx]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hl.trans (source_type p ps x qs T hp hps hx hqs hNeX).symm) (by rw [hl]; simp)

private theorem eval_tail (M : SmtModel) (hM : model_wf M)
    (ps r qs : Term) (T : SmtType)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hNe : tail ps r qs ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (tail ps r qs)) =
      __smtx_model_eval M (__eo_to_smt (mkConcat ps (mkConcat r qs))) := by
  have hList := (concat_clash_rev_list_concat_facts ps (mkConcat r qs) hNe).1
  have hRec := concat_clash_rev_list_concat_eq_rec ps (mkConcat r qs) hNe
  have hZ := smt_typeof_str_concat_of_seq r qs T hr hqs
  have hRel := smt_value_rel_list_concat_rec_str_concat M hM ps (mkConcat r qs) T hList hps hZ
  rw [← hRec] at hRel
  rcases eval_seq M hM (mkConcat ps (mkConcat r qs)) T
    (smt_typeof_str_concat_of_seq ps (mkConcat r qs) T hps hZ) with ⟨v, hv⟩
  rw [hv] at hRel ⊢
  exact (RuleProofs.smt_value_rel_iff_eq _ _ (by rintro ⟨r1, r2, _, h⟩; cases h)).mp hRel

private theorem eval_plus (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus a b) =
      __smtx_model_eval_plus (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def]

private theorem conclusion_facts (M : SmtModel) (hM : model_wf M)
    (p ps r qs n x : Term) (T : SmtType)
    (hp : __smtx_typeof (__eo_to_smt p) = SmtType.Seq T)
    (hps : __smtx_typeof (__eo_to_smt ps) = SmtType.Seq T)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.Seq T)
    (hqs : __smtx_typeof (__eo_to_smt qs) = SmtType.Seq T)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNeR : tail ps r qs ≠ Term.Stuck) (hNeX : tail ps x qs ≠ Term.Stuck)
    (hIndex : eo_interprets M (indexPremise p ps n) true)
    (hLength : eo_interprets M (lengthPremise r x) true) :
    eo_interprets M (conclusion p ps r qs n x) true := by
  rcases eval_seq M hM p T hp with ⟨sp, hpe⟩
  rcases eval_seq M hM ps T hps with ⟨sps, hpse⟩
  rcases eval_seq M hM r T hr with ⟨rs, hre⟩
  rcases eval_seq M hM qs T hqs with ⟨qss, hqse⟩
  rcases eval_seq M hM x T hx with ⟨xs, hxe⟩
  have hnVal : __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) = SmtType.Int := by
    simpa [hn] using smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (term_has_non_none_of_type_eq hn (by simp))
  rcases int_value_canonical hnVal with ⟨ni, hne⟩
  have hi : ni = ((native_unpack_seq sp ++ native_unpack_seq sps).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hIndex
    cases hIndex with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq
        (SmtTerm.str_len (SmtTerm.str_concat (__eo_to_smt p)
          (SmtTerm.str_concat (__eo_to_smt p) (__eo_to_smt ps))))
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt p))
          (SmtTerm.plus (__eo_to_smt n) (SmtTerm.Numeral 0)))) = SmtValue.Boolean true at he
      have hZero : __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
        rw [__smtx_model_eval.eq_def]
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, eval_concat,
        eval_plus, hpe, hpse, hne, hZero] at he
      simp [__smtx_model_eval_eq, __smtx_model_eval_str_len, __smtx_model_eval_str_concat,
        __smtx_model_eval_plus, native_seq_concat, native_seq_len,
        Smtm.native_unpack_pack_seq, native_veq, native_zplus, native_nat_to_int,
        List.length_append] at he ⊢
      exact he.symm
  have hLen : (native_unpack_seq rs).length = (native_unpack_seq xs).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hLength
    cases hLength with
    | intro_true _ he =>
      change __smtx_model_eval M (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt r))
        (SmtTerm.str_len (__eo_to_smt x))) = SmtValue.Boolean true at he
      simp only [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hre, hxe] at he
      apply Int.ofNat.inj
      simpa [__smtx_model_eval_eq, __smtx_model_eval_str_len, native_seq_len, native_veq] using he
  have hu := native_seq_update_replace_middle (native_unpack_seq sp ++ native_unpack_seq sps)
    (native_unpack_seq rs) (native_unpack_seq qss) (native_unpack_seq xs) hLen
  have hFlatR := eval_tail M hM ps r qs T hps hr hqs hNeR
  have hFlatX := eval_tail M hM ps x qs T hps hx hqs hNeX
  have heq : __smtx_model_eval M (__eo_to_smt (lhs p ps r qs n x)) =
      __smtx_model_eval M (__eo_to_smt (source p ps x qs)) := by
    change __smtx_model_eval M (SmtTerm.str_update
      (SmtTerm.str_concat (__eo_to_smt p) (__eo_to_smt (tail ps r qs)))
      (__eo_to_smt n) (__eo_to_smt x)) =
      __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt p) (__eo_to_smt (tail ps x qs)))
    simp only [smtx_eval_str_update_term_eq, eval_concat, hFlatR, hFlatX]
    change __smtx_model_eval_str_update
      (__smtx_model_eval_str_concat (__smtx_model_eval M (__eo_to_smt p))
        (__smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt ps)
          (SmtTerm.str_concat (__eo_to_smt r) (__eo_to_smt qs)))))
      (__smtx_model_eval M (__eo_to_smt n)) (__smtx_model_eval M (__eo_to_smt x)) =
      __smtx_model_eval_str_concat (__smtx_model_eval M (__eo_to_smt p))
        (__smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt ps)
          (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt qs))))
    simp only [eval_concat, hpe, hpse, hre, hqse, hxe, hne, hi]
    simp [__smtx_model_eval_str_update, __smtx_model_eval_str_concat, native_seq_concat,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, ← List.append_assoc]
    simpa only [List.length_append, Int.ofNat_eq_natCast, Int.natCast_add] using
      congrArg (native_pack_seq (__smtx_elem_typeof_seq_value sp)) hu
  exact RuleProofs.eo_interprets_eq_of_rel M _ _
    (conclusion_typed p ps r qs n x T hp hps hr hqs hn hx hNeR hNeX)
    (by rw [heq]; exact RuleProofs.smt_value_rel_refl _)

public theorem cmd_step_str_update_concat_fit_properties
    (M : SmtModel) (hM : model_wf M)
    (state : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_concat_fit args premises) ->
  AllHaveBoolType (premiseTermList state premises) ->
  __eo_typeof (__eo_cmd_step_proven state CRule.str_update_concat_fit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList state premises)
    (__eo_cmd_step_proven state CRule.str_update_concat_fit args premises) := by
  intro hCmd hBools hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons p args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons ps args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons r args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons qs args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons n args =>
            cases args with
            | nil => exact False.elim (hProg rfl)
            | cons x args =>
              cases args with
              | cons _ _ => exact False.elim (hProg rfl)
              | nil =>
                cases premises with
                | nil => exact False.elim (hProg rfl)
                | cons i premises =>
                  cases premises with
                  | nil => exact False.elim (hProg rfl)
                  | cons j premises =>
                    cases premises with
                    | cons _ _ => exact False.elim (hProg rfl)
                    | nil =>
                      let P := __eo_state_proven_nth state i
                      let Q := __eo_state_proven_nth state j
                      have hpTrans : RuleProofs.eo_has_smt_translation p := hCmd.1
                      have hpsTrans : RuleProofs.eo_has_smt_translation ps := hCmd.2.1
                      have hrTrans : RuleProofs.eo_has_smt_translation r := hCmd.2.2.1
                      have hqsTrans : RuleProofs.eo_has_smt_translation qs := hCmd.2.2.2.1
                      have hnTrans : RuleProofs.eo_has_smt_translation n := hCmd.2.2.2.2.1
                      have hxTrans : RuleProofs.eo_has_smt_translation x := hCmd.2.2.2.2.2.1
                      change __eo_typeof (__eo_prog_str_update_concat_fit p ps r qs n x
                        (Proof.pf P) (Proof.pf Q)) = Term.Bool at hTy
                      rcases program_info p ps r qs n x P Q
                        (RuleProofs.term_ne_stuck_of_has_smt_translation p hpTrans)
                        (RuleProofs.term_ne_stuck_of_has_smt_translation ps hpsTrans)
                        (RuleProofs.term_ne_stuck_of_has_smt_translation r hrTrans)
                        (RuleProofs.term_ne_stuck_of_has_smt_translation qs hqsTrans)
                        (RuleProofs.term_ne_stuck_of_has_smt_translation n hnTrans)
                        (RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans)
                        (term_ne_stuck_of_typeof_bool hTy) with ⟨hP, hQ, he⟩
                      change StepRuleProperties M _ (__eo_prog_str_update_concat_fit p ps r qs n x
                        (Proof.pf P) (Proof.pf Q))
                      rw [he] at hTy ⊢
                      have hl : __eo_typeof (lhs p ps r qs n x) ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
                      rcases eo_typeof_str_update_args_of_ne_stuck _ _ _ hl with ⟨T, hsource, hn, hx⟩
                      rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                        p (tail ps r qs) T hsource with ⟨hp, hinner⟩
                      have hNeR : tail ps r qs ≠ Term.Stuck := by
                        intro he
                        rw [he] at hinner
                        cases hinner
                      have hList := (concat_clash_rev_list_concat_facts ps (mkConcat r qs) hNeR).1
                      have hRec := concat_clash_rev_list_concat_eq_rec ps (mkConcat r qs) hNeR
                      have hZTy := StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
                        ps (mkConcat r qs) T hList (by rw [← hRec]; exact hinner)
                      rcases StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                        r qs T hZTy with ⟨hr, hqs⟩
                      have hlTy : __eo_typeof (lhs p ps r qs n x) = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_update _ _ _ = _
                        rw [hsource, hn, hx]
                        by_cases hT : T = Term.Stuck
                        · change __eo_typeof_str_update _ _ _ ≠ Term.Stuck at hl
                          rw [hsource, hn, hx, hT] at hl
                          simp [__eo_typeof_str_update, __eo_requires, __eo_eq,
                            native_ite, native_teq, SmtEval.native_not] at hl
                        · simp [__eo_typeof_str_update, RuleProofs.eo_eq_self_of_ne_stuck T hT,
                            __eo_requires, native_ite, native_teq, SmtEval.native_not]
                      have hRhsTy := (RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy).symm.trans hlTy
                      have hXTail := (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                        p (tail ps x qs) T hRhsTy).2
                      have hNeX : tail ps x qs ≠ Term.Stuck := by
                        intro he
                        rw [he] at hXTail
                        cases hXTail
                      have hpS := smtx_typeof_of_eo_seq p T hpTrans hp
                      have hrS := smtx_typeof_of_eo_seq r T hrTrans hr
                      have hqsS := smtx_typeof_of_eo_seq qs T hqsTrans hqs
                      have hnS := smtx_typeof_of_eo_int n hnTrans hn
                      have hxS := smtx_typeof_of_eo_seq x T hxTrans hx
                      have hPBool := hBools P (by simp [P, premiseTermList])
                      rw [hP] at hPBool
                      rcases indexPremise_types p ps n hPBool with ⟨V, hpV, hpsV⟩
                      have hV : V = __eo_to_smt_type T := SmtType.Seq.inj (hpV.symm.trans hpS)
                      rw [hV] at hpsV
                      refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                        (conclusion_typed p ps r qs n x _ hpS hpsV hrS hqsS hnS hxS hNeR hNeX)⟩
                      intro hTrue
                      apply conclusion_facts M hM p ps r qs n x _ hpS hpsV hrS hqsS hnS hxS hNeR hNeX
                      · have h := hTrue P (by simp [P, premiseTermList])
                        simpa [hP] using h
                      · have h := hTrue Q (by simp [Q, premiseTermList])
                        simpa [hQ] using h
