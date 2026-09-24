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

private abbrev containsSplitCharPremise (w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len w))
    (Term.Numeral 1)

private abbrev containsSplitCharTail (y z : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat y) z

private abbrev containsSplitCharFlatTail (y z : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
    (containsSplitCharTail y z)

private abbrev containsSplitCharWhole (x y z : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat x)
    (containsSplitCharTail y z)

private abbrev containsSplitCharContains (x w : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) w

private abbrev containsSplitCharRhs (x y z w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.or (containsSplitCharContains x w))
    (Term.Apply
      (Term.Apply Term.or
        (containsSplitCharContains (containsSplitCharFlatTail y z) w))
      (Term.Boolean false))

private abbrev containsSplitCharConclusion
    (x y z w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (containsSplitCharContains (containsSplitCharWhole x y z) w))
    (containsSplitCharRhs x y z w)

private abbrev containsSplitCharGeneratedContains
    (y z w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.str_contains)
      (containsSplitCharFlatTail y z)) w

private abbrev containsSplitCharGeneratedRhs
    (x y z w : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.or)
      (containsSplitCharContains x w))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.or)
        (containsSplitCharGeneratedContains y z w))
      (Term.Boolean false))

private abbrev containsSplitCharGeneratedConclusion
    (x y z w : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (containsSplitCharContains (containsSplitCharWhole x y z) w))
    (containsSplitCharGeneratedRhs x y z w)

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem generated_conclusion_eq
    (x y z w : Term)
    (hFlat : containsSplitCharFlatTail y z ≠ Term.Stuck)
    (hW : w ≠ Term.Stuck) :
    containsSplitCharGeneratedConclusion x y z w =
      containsSplitCharConclusion x y z w := by
  have hContainsHead :
      __eo_mk_apply (Term.UOp UserOp.str_contains)
          (containsSplitCharFlatTail y z) =
        Term.Apply (Term.UOp UserOp.str_contains)
          (containsSplitCharFlatTail y z) :=
    mk_apply_eq _ _ (by simp) hFlat
  have hContains : containsSplitCharGeneratedContains y z w =
      containsSplitCharContains (containsSplitCharFlatTail y z) w := by
    rw [containsSplitCharGeneratedContains, hContainsHead]
    exact mk_apply_eq _ _ (by simp) hW
  have hOrHead :
      __eo_mk_apply (Term.UOp UserOp.or)
          (containsSplitCharGeneratedContains y z w) =
        Term.Apply (Term.UOp UserOp.or)
          (containsSplitCharContains (containsSplitCharFlatTail y z) w) := by
    rw [hContains]
    exact mk_apply_eq _ _ (by simp) (by simp)
  have hInner :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or)
            (containsSplitCharGeneratedContains y z w))
          (Term.Boolean false) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.or)
            (containsSplitCharContains (containsSplitCharFlatTail y z) w))
          (Term.Boolean false) := by
    rw [hOrHead]
    exact mk_apply_eq _ _ (by simp) (by simp)
  have hRhs : containsSplitCharGeneratedRhs x y z w =
      containsSplitCharRhs x y z w := by
    rw [containsSplitCharGeneratedRhs, hInner]
    exact mk_apply_eq _ _ (by simp) (by simp)
  rw [containsSplitCharGeneratedConclusion, hRhs]
  exact mk_apply_eq _ _ (by simp) (by simp)

private theorem generated_flat_ne_stuck
    (x y z w : Term)
    (hGenerated :
      containsSplitCharGeneratedConclusion x y z w ≠ Term.Stuck) :
    containsSplitCharFlatTail y z ≠ Term.Stuck := by
  have hRhs : containsSplitCharGeneratedRhs x y z w ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (containsSplitCharContains (containsSplitCharWhole x y z) w))
      (containsSplitCharGeneratedRhs x y z w) hGenerated
  have hInner :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.or)
            (containsSplitCharGeneratedContains y z w))
          (Term.Boolean false) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.or)
        (containsSplitCharContains x w)) _ hRhs
  have hOrHead :
      __eo_mk_apply (Term.UOp UserOp.or)
          (containsSplitCharGeneratedContains y z w) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ (Term.Boolean false) hInner
  have hContains :
      containsSplitCharGeneratedContains y z w ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.or) _ hOrHead
  have hContainsHead :
      __eo_mk_apply (Term.UOp UserOp.str_contains)
          (containsSplitCharFlatTail y z) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ w hContains
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_contains) _ hContainsHead

private theorem eo_typeof_contains_split_char_args_of_ne_stuck
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

private theorem smtx_typeof_contains_split_char_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  exact StrEqReplSupport.smtx_typeof_of_eo_seq a T hTrans hTy

private theorem prog_str_contains_split_char_info
    (x y z w P : Term)
    (hProg :
      __eo_prog_str_contains_split_char x y z w (Proof.pf P) ≠
        Term.Stuck) :
    ∃ w₀,
      P = containsSplitCharPremise w₀ ∧ w₀ = w ∧
      __eo_prog_str_contains_split_char x y z w (Proof.pf P) =
        containsSplitCharGeneratedConclusion x y z w := by
  unfold __eo_prog_str_contains_split_char at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hW := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_split_char, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      containsSplitCharGeneratedConclusion,
      containsSplitCharGeneratedRhs,
      containsSplitCharGeneratedContains, containsSplitCharWhole,
      containsSplitCharTail, containsSplitCharContains,
      containsSplitCharFlatTail]

private theorem typed___eo_prog_str_contains_split_char_impl
    (x y z w P T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hFlatNe : containsSplitCharFlatTail y z ≠ Term.Stuck)
    (hProgEq :
      __eo_prog_str_contains_split_char x y z w (Proof.pf P) =
        containsSplitCharConclusion x y z w) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_contains_split_char x y z w (Proof.pf P)) := by
  let tail := containsSplitCharTail y z
  let flat := containsSplitCharFlatTail y z
  let whole := containsSplitCharWhole x y z
  let lhs := containsSplitCharContains whole w
  let cx := containsSplitCharContains x w
  let ct := containsSplitCharContains flat w
  let rhs := containsSplitCharRhs x y z w
  have hXSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq x T hXTrans hXTy
  have hYSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq y T hYTrans hYTy
  have hZSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq z T hZTrans hZTy
  have hWSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq w T hWTrans hWTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq y z (__eo_to_smt_type T) hYSmtTy hZSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt flat) =
      SmtType.Seq (__eo_to_smt_type T) := by
    exact smt_typeof_str_nary_elim_of_seq_ne_stuck
      tail (__eo_to_smt_type T) hTailTy hFlatNe
  have hWholeTy : __smtx_typeof (__eo_to_smt whole) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq x tail (__eo_to_smt_type T)
      hXSmtTy hTailTy
  have hContainsTy : ∀ a b : Term,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) →
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq (__eo_to_smt_type T) →
      RuleProofs.eo_has_bool_type (containsSplitCharContains a b) := by
    intro a b hA hB
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hA, hB, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hLhsTy := hContainsTy whole w hWholeTy hWSmtTy
  have hCxTy := hContainsTy x w hXSmtTy hWSmtTy
  have hCtTy := hContainsTy flat w hFlatTy hWSmtTy
  have hInnerTy : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.or ct) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args ct (Term.Boolean false)
      hCtTy RuleProofs.eo_has_bool_type_false
  have hRhsTy : RuleProofs.eo_has_bool_type rhs :=
    RuleProofs.eo_has_bool_type_or_of_bool_args cx
      (Term.Apply (Term.Apply Term.or ct) (Term.Boolean false))
      hCxTy hInnerTy
  have hBool : RuleProofs.eo_has_bool_type
      (containsSplitCharConclusion x y z w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_contains_split_char_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z w P T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hFlatNe : containsSplitCharFlatTail y z ≠ Term.Stuck)
    (hPrem : eo_interprets M (containsSplitCharPremise w) true)
    (hProgEq :
      __eo_prog_str_contains_split_char x y z w (Proof.pf P) =
        containsSplitCharConclusion x y z w) :
    eo_interprets M
      (__eo_prog_str_contains_split_char x y z w (Proof.pf P)) true := by
  let tail := containsSplitCharTail y z
  let flat := containsSplitCharFlatTail y z
  let whole := containsSplitCharWhole x y z
  let lhs := containsSplitCharContains whole w
  let rhs := containsSplitCharRhs x y z w
  have hBool : RuleProofs.eo_has_bool_type
      (containsSplitCharConclusion x y z w) := by
    simpa [hProgEq] using
      typed___eo_prog_str_contains_split_char_impl
        x y z w P T hXTrans hYTrans hZTrans hWTrans
        hXTy hYTy hZTy hWTy hFlatNe hProgEq
  have hXSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq x T hXTrans hXTy
  have hYSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq y T hYTrans hYTy
  have hZSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq z T hZTrans hZTy
  have hWSmtTy :=
    smtx_typeof_contains_split_char_of_eo_seq w T hWTrans hWTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq y z (__eo_to_smt_type T) hYSmtTy hZSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt flat) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      tail (__eo_to_smt_type T) hTailTy hFlatNe
  have hXEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq (__eo_to_smt_type T)) hXSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hYEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq (__eo_to_smt_type T)) hYSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hZEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq (__eo_to_smt_type T)) hZSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hWEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt w)
    (SmtType.Seq (__eo_to_smt_type T)) hWSmtTy
    (seq_ne_none _) (type_inhabited_seq _)
  have hFlatEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt flat)
    (SmtType.Seq (__eo_to_smt_type T)) hFlatTy
    (seq_ne_none _) (type_inhabited_seq _)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  rcases seq_value_canonical hFlatEvalTy with ⟨sflat, hFlatEval⟩
  let stail := native_pack_seq (__smtx_elem_typeof_seq_value sy)
    (native_unpack_seq sy ++ native_unpack_seq sz)
  have hTailEval : __smtx_model_eval M (__eo_to_smt tail) =
      SmtValue.Seq stail := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt y) (__eo_to_smt z)) = _
    rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hYEval, hZEval]
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
  have hWLen : (native_unpack_seq sw).length = 1 := by
    have hWLenInt : native_seq_len (native_unpack_seq sw) = 1 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
      cases hPrem with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt w))
                (SmtTerm.Numeral 1)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hWEval,
            StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    have hCast : ((native_unpack_seq sw).length : Int) = 1 := by
      simpa [native_seq_len] using hWLenInt
    omega
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_concat (__eo_to_smt x)
            (SmtTerm.str_concat (__eo_to_smt y) (__eo_to_smt z)))
          (__eo_to_smt w)) =
      __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w))
          (SmtTerm.or
            (SmtTerm.str_contains (__eo_to_smt flat) (__eo_to_smt w))
            (SmtTerm.Boolean false)))
    rw [StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hXEval, StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hYEval, hZEval, hWEval, smtx_eval_or_term_eq,
      StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
      hXEval, hWEval, smtx_eval_or_term_eq,
      StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
      hFlatEval, hWEval, StrEqReplSupport.smtx_eval_boolean_term_eq]
    simp only [__smtx_model_eval_str_concat, native_seq_concat,
      __smtx_model_eval_str_contains, __smtx_model_eval_or,
      Smtm.native_unpack_pack_seq]
    rw [hFlatTailEq]
    simp only [stail, Smtm.native_unpack_pack_seq]
    rw [native_seq_contains_append_of_pattern_length_one
      (native_unpack_seq sx)
      (native_unpack_seq sy ++ native_unpack_seq sz)
      (native_unpack_seq sw) hWLen]
    simp [SmtEval.native_or]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_split_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_split_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_split_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_split_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_split_char args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons x args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons y args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons z args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons w args =>
                  cases args with
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons i premises =>
                          cases premises with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              let P := __eo_state_proven_nth s i
                              have hXTrans :
                                  RuleProofs.eo_has_smt_translation x := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.1
                              have hYTrans :
                                  RuleProofs.eo_has_smt_translation y := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.2.1
                              have hZTrans :
                                  RuleProofs.eo_has_smt_translation z := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              have hWTrans :
                                  RuleProofs.eo_has_smt_translation w := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_contains_split_char
                                    x y z w (Proof.pf P)) = Term.Bool
                                at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_contains_split_char
                                      x y z w (Proof.pf P) ≠ Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_contains_split_char_info
                                  x y z w P hRuleProg with
                                ⟨w₀, hP, hw₀, hProgGenerated⟩
                              subst w₀
                              have hGeneratedNe :
                                  containsSplitCharGeneratedConclusion
                                      x y z w ≠ Term.Stuck := by
                                rw [← hProgGenerated]
                                exact hRuleProg
                              have hFlatNe := generated_flat_ne_stuck
                                x y z w hGeneratedNe
                              have hWNe : w ≠ Term.Stuck :=
                                RuleProofs.term_ne_stuck_of_has_smt_translation
                                  w hWTrans
                              have hGeneratedEq :=
                                generated_conclusion_eq x y z w hFlatNe hWNe
                              have hProgEq :
                                  __eo_prog_str_contains_split_char
                                      x y z w (Proof.pf P) =
                                    containsSplitCharConclusion x y z w := by
                                rw [hProgGenerated, hGeneratedEq]
                              rw [hProgEq] at hResultTy
                              have hOps :=
                                RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof
                                    (containsSplitCharContains
                                      (containsSplitCharWhole x y z) w))
                                  (__eo_typeof
                                    (containsSplitCharRhs x y z w))
                                  hResultTy
                              have hLhsNN := hOps.1
                              change __eo_typeof_str_contains
                                  (__eo_typeof (containsSplitCharWhole x y z))
                                  (__eo_typeof w) ≠ Term.Stuck at hLhsNN
                              rcases eo_typeof_contains_split_char_args_of_ne_stuck
                                  (__eo_typeof (containsSplitCharWhole x y z))
                                  (__eo_typeof w) hLhsNN with
                                ⟨T, hWholeTy, hWTy⟩
                              have hWholeArgs :=
                                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                  x (containsSplitCharTail y z) T hWholeTy
                              have hTailArgs :=
                                StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
                                  y z T hWholeArgs.2
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem : eo_interprets M
                                    (containsSplitCharPremise w) true := by
                                  simpa [hP] using hPremRaw
                                exact
                                  facts___eo_prog_str_contains_split_char_impl
                                    M hM x y z w P T hXTrans hYTrans
                                    hZTrans hWTrans hWholeArgs.1 hTailArgs.1
                                    hTailArgs.2 hWTy hFlatNe hPrem hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_contains_split_char_impl
                                      x y z w P T hXTrans hYTrans hZTrans
                                      hWTrans hWholeArgs.1 hTailArgs.1
                                      hTailArgs.2 hWTy hFlatNe hProgEq)
