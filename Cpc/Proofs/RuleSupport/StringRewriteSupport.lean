module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport
public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrReplaceFindSupport
import all Cpc.Proofs.RuleSupport.StrReplaceFindSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatNarySupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StringRewriteSupport

theorem list_nil_of_list_not_cons (a : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hNotCons :
      ¬ ∃ head tail,
        a = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) a =
      Term.Boolean true := by
  cases a <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
      __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at haList ⊢
  all_goals try exact haList.1
  case Apply f x =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at haList ⊢
    all_goals try exact haList.1
    case Apply g y =>
      have hg : g = Term.UOp UserOp.str_concat := haList.1.symm
      subst g
      exact False.elim (hNotCons ⟨y, x, rfl⟩)

theorem typeof_seq_of_str_concat_nil_ne_stuck (A : Term)
    (h : __eo_nil (Term.UOp UserOp.str_concat) A ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T := by
  cases A <;>
    simp [__eo_nil, __eo_nil_str_concat, Term.Seq] at h ⊢
  case Apply f x =>
    cases f <;>
      simp [__eo_nil, __eo_nil_str_concat] at h ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_nil, __eo_nil_str_concat, Term.Seq] at h ⊢

theorem eo_typeof_seq_empty_seq_of_ne_stuck
    (T : Term)
    (h : __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) ≠
      Term.Stuck) :
    __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) =
      Term.Apply Term.Seq T := by
  by_cases hChar : T = Term.Char
  · subst T
    rfl
  · have hDefault :
        __seq_empty (Term.Apply Term.Seq T) =
          Term.seq_empty (Term.Apply Term.Seq T) := by
      cases T <;> simp [__seq_empty] at hChar ⊢
      case UOp op => cases op <;> simp [__seq_empty] at hChar ⊢
    rw [hDefault] at h ⊢
    change __eo_typeof_seq_empty
        (__eo_typeof_Seq (__eo_typeof T)) (Term.Apply Term.Seq T) ≠
      Term.Stuck at h
    change __eo_typeof_seq_empty
        (__eo_typeof_Seq (__eo_typeof T)) (Term.Apply Term.Seq T) =
      Term.Apply Term.Seq T
    cases hTy : __eo_typeof T <;>
      simp [__eo_typeof_Seq, __eo_typeof_seq_empty,
        __eo_disamb_type_seq_empty, hTy] at h ⊢

theorem source_typeof_eq_seq_of_str_concat_nil_typeof_eq_seq
    (x U : Term)
    (hNilTy :
      __eo_typeof
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)) =
        Term.Apply Term.Seq U) :
    __eo_typeof x = Term.Apply Term.Seq U := by
  have hNilNe :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) ≠
        Term.Stuck := by
    intro h
    rw [h] at hNilTy
    change Term.Stuck = Term.Apply Term.Seq U at hNilTy
    cases hNilTy
  rcases typeof_seq_of_str_concat_nil_ne_stuck
      (__eo_typeof x) hNilNe with ⟨V, hXTy⟩
  have hNilEq :
      __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) =
        __seq_empty (__eo_typeof x) := by
    rw [hXTy]
    rfl
  have hNilTy' := hNilTy
  rw [hNilEq, hXTy] at hNilTy'
  have hEmptyNe :
      __eo_typeof (__seq_empty (Term.Apply Term.Seq V)) ≠ Term.Stuck := by
    rw [hNilTy']
    intro h
    cases h
  have hEmptyTy := eo_typeof_seq_empty_seq_of_ne_stuck V hEmptyNe
  rw [hNilEq, hXTy, hEmptyTy] at hNilTy
  have hVU : V = U := by
    injection hNilTy
  simpa [hVU] using hXTy

theorem eo_typeof_str_indexof_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    ∃ T, A = Term.Apply Term.Seq T ∧
      B = Term.Apply Term.Seq T ∧ C = Term.Int := by
  cases A <;> simp [__eo_typeof_str_indexof] at h ⊢
  case Apply fA aA =>
    cases fA <;> simp at h ⊢
    case UOp opA =>
      cases opA <;> simp at h ⊢
      case Seq =>
        cases B <;> simp at h ⊢
        case Apply fB aB =>
          cases fB <;> simp at h ⊢
          case UOp opB =>
            cases opB <;> simp at h ⊢
            case Seq =>
              cases C <;> simp at h ⊢
              case UOp opC =>
                cases opC <;> simp at h ⊢
                case Int =>
                  have hCond : __eo_eq aA aB = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hBA : aB = aA :=
                    support_eq_of_eo_eq_true aA aB hCond
                  subst aB
                  simp

theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smt_typeof_str_indexof_of_seq
    (x y n : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) y) n)) =
      SmtType.Int := by
  change __smtx_typeof
      (SmtTerm.str_indexof (__eo_to_smt x) (__eo_to_smt y)
        (__eo_to_smt n)) = SmtType.Int
  rw [typeof_str_indexof_eq]
  simp [hxTy, hyTy, hnTy, __smtx_typeof_str_indexof,
    native_ite, native_Teq]

theorem list_concat_reduce (a z : Term)
    (ha : __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hz : __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  simp [__eo_list_concat, ha, hz, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

theorem list_concat_has_seq_type
    (a z : Term) (T : SmtType)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hzList :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
      SmtType.Seq T := by
  rw [list_concat_reduce a z haList hzList]
  exact strConcat_typeof_list_concat_rec_of_seq a z T haList haTy hzTy

theorem list_concat_is_list
    (a z : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hzList :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_list_concat (Term.UOp UserOp.str_concat) a z) =
      Term.Boolean true := by
  rw [list_concat_reduce a z haList hzList]
  exact strConcat_is_list_concat_rec_of_lists a z haList hzList

theorem list_concat_rec_cons_right_is_not_nil
    (a head tail : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
        (__eo_list_concat_rec a
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) tail)) =
      Term.Boolean false := by
  have go : ∀ (p z : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) p = Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true →
      __eo_is_list_nil (Term.UOp UserOp.str_concat) z =
        Term.Boolean false →
      __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__eo_list_concat_rec p z) = Term.Boolean false := by
    intro p z
    induction p, z using __eo_list_concat_rec.induct with
    | case1 z => intro hp; simp [__eo_is_list] at hp
    | case2 p hP =>
        intro _ hz
        simp [__eo_is_list] at hz
    | case3 g x y z hZ ih =>
        intro hp _ _
        have hg : g = Term.UOp UserOp.str_concat :=
          eo_is_list_cons_head_eq_of_true
            (Term.UOp UserOp.str_concat) g x y hp
        subst g
        have hyList :
            __eo_is_list (Term.UOp UserOp.str_concat) y =
              Term.Boolean true :=
          eo_is_list_tail_true_of_cons_self
            (Term.UOp UserOp.str_concat) x y hp
        have hRecNe := eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) y z hyList hZ
        rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x y z hRecNe]
        simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
          __eo_eq, native_teq]
    | case4 nil z hNil hZ hNot =>
        intro hp _ hzNotNil
        have hNilTrue :
            __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
              Term.Boolean true :=
          list_nil_of_list_not_cons nil hp (by
            intro h
            rcases h with ⟨x, y, hxy⟩
            exact hNot (Term.UOp UserOp.str_concat) x y hxy)
        rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
          nil z hNilTrue]
        exact hzNotNil
  apply go a
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.str_concat) head) tail)
    haList
  · exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head tail (by simp) hTailList
  · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq]

theorem list_concat_eval
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (T : SmtType) (sa sz : SmtSeq)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hzList :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz) :
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value sa)
          (native_unpack_seq sa ++ native_unpack_seq sz)) := by
  have hRel := strConcat_smt_value_rel_list_concat_rec_eval
    M hM a z T haList haTy hzTy
  rw [← list_concat_reduce a z haList hzList] at hRel
  rw [smtx_model_eval_str_concat_term_eq, haEval, hzEval] at hRel
  change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)))
      (SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value sa)
          (native_unpack_seq sa ++ native_unpack_seq sz))) at hRel
  have hConcatTy := list_concat_has_seq_type
    a z T haList hzList haTy hzTy
  have hValTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_concat (Term.UOp UserOp.str_concat) a z))) =
        SmtType.Seq T := by
    simpa [hConcatTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt
          (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) (by
          unfold term_has_non_none_type
          rw [hConcatTy]
          simp)
  rcases seq_value_canonical hValTy with ⟨actual, hEval⟩
  have hSeq : RuleProofs.smt_seq_rel actual
      (native_pack_seq (__smtx_elem_typeof_seq_value sa)
        (native_unpack_seq sa ++ native_unpack_seq sz)) := by
    have hsimpa := hRel
    try simp [hEval, RuleProofs.smt_value_rel] at hsimpa ⊢
    exact hsimpa
  have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 hSeq
  exact hEval.trans (congrArg SmtValue.Seq hEq)

noncomputable def listEvalPrefix (M : SmtModel) : Term -> List SmtValue
  | Term.Apply
      (Term.Apply (Term.UOp UserOp.str_concat) head) tail =>
      (match __smtx_model_eval M (__eo_to_smt head) with
        | SmtValue.Seq s => native_unpack_seq s
        | _ => []) ++ listEvalPrefix M tail
  | _ => []

theorem listEvalPrefix_eq_nil_of_not_cons
    (M : SmtModel) (a : Term)
    (hNotCons :
      ¬ ∃ head tail,
        a = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail) :
    listEvalPrefix M a = [] := by
  cases a <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case str_concat => exact False.elim (hNotCons ⟨y, x, rfl⟩)

theorem list_eval_prefix
    (M : SmtModel) (hM : model_wf M) :
    ∀ (a : Term) (T : SmtType),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true →
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T →
      ∃ sa,
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa ∧
        native_unpack_seq sa = listEvalPrefix M a
  | a, T, haList, haTy => by
      by_cases hCons :
          ∃ head tail,
            a = Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) head) tail
      · rcases hCons with ⟨head, tail, rfl⟩
        have hTailList :
            __eo_is_list (Term.UOp UserOp.str_concat) tail =
              Term.Boolean true :=
          eo_is_list_tail_true_of_cons_self
            (Term.UOp UserOp.str_concat) head tail haList
        have hTypes := strConcat_args_of_seq_type head tail T haTy
        rcases list_eval_prefix M hM tail T hTailList hTypes.2 with
          ⟨stail, hTailEval, hTailUnpack⟩
        have hHeadValTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt head)) =
              SmtType.Seq T := by
          simpa [hTypes.1] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt head) (by
                unfold term_has_non_none_type
                rw [hTypes.1]
                simp)
        rcases seq_value_canonical hHeadValTy with ⟨shead, hHeadEval⟩
        refine ⟨native_pack_seq (__smtx_elem_typeof_seq_value shead)
            (native_unpack_seq shead ++ native_unpack_seq stail), ?_, ?_⟩
        · rw [smtx_model_eval_str_concat_term_eq,
            hHeadEval, hTailEval]
          rfl
        · simp [listEvalPrefix, hHeadEval,
            Smtm.native_unpack_pack_seq, hTailUnpack]
      · have hNil := list_nil_of_list_not_cons a haList hCons
        have hValTy :
            __smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt a)) =
              SmtType.Seq T := by
          simpa [haTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt a) (by
                unfold term_has_non_none_type
                rw [haTy]
                simp)
        rcases seq_value_canonical hValTy with ⟨sa, haEval⟩
        have hRel := smt_value_rel_str_concat_nil_empty M a T hNil haTy
        rw [haEval] at hRel
        have hSeq : RuleProofs.smt_seq_rel sa (SmtSeq.empty T) := by
          have hsimpa := hRel
          try simp [RuleProofs.smt_value_rel] at hsimpa ⊢
          exact hsimpa
        have hEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 hSeq
        refine ⟨sa, haEval, ?_⟩
        rw [hEq, listEvalPrefix_eq_nil_of_not_cons M a hCons]
        rfl

theorem list_concat_eval_prefix
    (M : SmtModel) (hM : model_wf M) :
    ∀ (a z : Term) (T : SmtType) (sz : SmtSeq),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true ->
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
        SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz ->
      ∃ out,
        __smtx_model_eval M
            (__eo_to_smt
              (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
          SmtValue.Seq out ∧
        native_unpack_seq out =
          listEvalPrefix M a ++ native_unpack_seq sz
  | a, z, T, sz, haList, hzList, hRecTy, hzEval => by
      rw [list_concat_reduce a z haList hzList] at hRecTy ⊢
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          simp [__eo_is_list] at haList
      | case2 a hA =>
          simp [__eo_is_list] at hzList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.str_concat) g x y haList
          subst g
          have hyList :
              __eo_is_list (Term.UOp UserOp.str_concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.str_concat) x y haList
          have hTailNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.str_concat) y z hyList hZ
          rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
            x y z hTailNe] at hRecTy ⊢
          have hTypes := strConcat_args_of_seq_type
            x (__eo_list_concat_rec y z) T hRecTy
          rcases ih hyList hzList hTypes.2 hzEval with
            ⟨tailOut, hTailEval, hTailUnpack⟩
          have hXValTy :
              __smtx_typeof_value
                  (__smtx_model_eval M (__eo_to_smt x)) =
                SmtType.Seq T := by
            simpa [hTypes.1] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt x) (by
                  unfold term_has_non_none_type
                  rw [hTypes.1]
                  simp)
          rcases seq_value_canonical hXValTy with ⟨sx, hxEval⟩
          have hxSeqTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
            simpa [hxEval, __smtx_typeof_value] using hXValTy
          have hxElem : __smtx_elem_typeof_seq_value sx = T :=
            elem_typeof_seq_value_of_typeof_seq_value hxSeqTy
          refine ⟨native_pack_seq T
              (native_unpack_seq sx ++ native_unpack_seq tailOut), ?_, ?_⟩
          · rw [smtx_model_eval_str_concat_term_eq, hxEval]
            change __smtx_model_eval_str_concat (SmtValue.Seq sx)
                (__smtx_model_eval M
                  (__eo_to_smt (__eo_list_concat_rec y z))) = _
            rw [hTailEval]
            simp [__smtx_model_eval_str_concat, native_seq_concat, hxElem]
          · simp [listEvalPrefix, hxEval, Smtm.native_unpack_pack_seq,
              hTailUnpack, List.append_assoc]
      | case4 nil z hNil hZ hNot =>
          have hRecEq : __eo_list_concat_rec nil z = z := by
            unfold __eo_list_concat_rec
            split <;> simp_all
          rw [hRecEq]
          exact ⟨sz, hzEval, by
            have hNotShape :
                ¬ ∃ head tail,
                  nil = Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) head) tail := by
              intro h
              rcases h with ⟨head, tail, h⟩
              exact (hNot (Term.UOp UserOp.str_concat) head tail) h
            cases nil <;> simp [listEvalPrefix] at hNotShape ⊢
            case Apply f x =>
              cases f <;> simp [listEvalPrefix] at hNotShape ⊢
              case Apply g y =>
                cases g <;> simp [listEvalPrefix] at hNotShape ⊢
                case UOp op =>
                  cases op <;> simp [listEvalPrefix] at hNotShape ⊢
            ⟩

theorem list_concat_eval_prefix_of_translation
    (M : SmtModel) (hM : model_wf M) :
    ∀ (a z : Term) (sz : SmtSeq),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true ->
      RuleProofs.eo_has_smt_translation a ->
      __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz ->
      ∃ out,
        __smtx_model_eval M
            (__eo_to_smt
              (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
          SmtValue.Seq out ∧
        native_unpack_seq out =
          listEvalPrefix M a ++ native_unpack_seq sz
  | a, z, sz, haList, hzList, haTrans, hzEval => by
      rw [list_concat_reduce a z haList hzList]
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z => simp [__eo_is_list] at haList
      | case2 a hA => simp [__eo_is_list] at hzList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.str_concat) g x y haList
          subst g
          have hyList :
              __eo_is_list (Term.UOp UserOp.str_concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.str_concat) x y haList
          have haNN :
              __smtx_typeof
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) x) y)) ≠
                SmtType.None := by
            simpa [RuleProofs.eo_has_smt_translation] using haTrans
          rcases str_concat_args_of_non_none x y haNN with
            ⟨T, hxTy, hyTy⟩
          have hyTrans : RuleProofs.eo_has_smt_translation y := by
            unfold RuleProofs.eo_has_smt_translation
            rw [hyTy]
            exact seq_ne_none T
          rcases ih hyList hzList hyTrans hzEval with
            ⟨tailOut, hTailEval, hTailUnpack⟩
          have hxValTy :
              __smtx_typeof_value
                  (__smtx_model_eval M (__eo_to_smt x)) =
                SmtType.Seq T := by
            simpa [hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM
                (__eo_to_smt x) (by
                  unfold term_has_non_none_type
                  rw [hxTy]
                  simp)
          rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
          refine ⟨native_pack_seq (__smtx_elem_typeof_seq_value sx)
              (native_unpack_seq sx ++ native_unpack_seq tailOut), ?_, ?_⟩
          · rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
              x y z (eo_list_concat_rec_ne_stuck_of_list
                (Term.UOp UserOp.str_concat) y z hyList hZ)]
            rw [smtx_model_eval_str_concat_term_eq, hxEval, hTailEval]
            rfl
          · simp [listEvalPrefix, hxEval, Smtm.native_unpack_pack_seq,
              hTailUnpack, List.append_assoc]
      | case4 nil z hNil hZ hNot =>
          have hRecEq : __eo_list_concat_rec nil z = z := by
            unfold __eo_list_concat_rec
            split <;> simp_all
          rw [hRecEq]
          refine ⟨sz, hzEval, ?_⟩
          have hNotShape :
              ¬ ∃ head tail,
                nil = Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) tail := by
            intro h
            rcases h with ⟨head, tail, h⟩
            exact (hNot (Term.UOp UserOp.str_concat) head tail) h
          cases nil <;> simp [listEvalPrefix] at hNotShape ⊢
          case Apply f x =>
            cases f <;> simp [listEvalPrefix] at hNotShape ⊢
            case Apply g y =>
              cases g <;> simp [listEvalPrefix] at hNotShape ⊢
              case UOp op =>
                cases op <;> simp [listEvalPrefix] at hNotShape ⊢

theorem list_type_eval_of_translation
    (M : SmtModel) (hM : model_wf M) (a : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTrans : RuleProofs.eo_has_smt_translation a) :
    ∃ T sa,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ∧
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa := by
  have haNN : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    haTrans
  have haTy : ∃ T, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
    by_cases hCons :
        ∃ head tail,
          a = Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) tail
    · rcases hCons with ⟨head, tail, rfl⟩
      exact smt_typeof_str_concat_seq_of_non_none head tail haNN
    · have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) a =
            Term.Boolean true := by
        cases a <;>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
            __eo_requires, native_ite, native_teq, native_not,
            SmtEval.native_not] at haList ⊢
        all_goals try exact haList.1
        case Apply f x =>
          cases f <;>
            simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
              __eo_requires, native_ite, native_teq, native_not,
              SmtEval.native_not] at haList ⊢
          all_goals try exact haList.1
          case Apply g y =>
            have hg : g = Term.UOp UserOp.str_concat := haList.1.symm
            subst g
            exact False.elim (hCons ⟨y, x, rfl⟩)
      exact smt_typeof_seq_of_str_concat_list_nil_non_none a hNil haNN
  rcases haTy with ⟨T, haTy⟩
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Seq T := by
    simpa [haTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a) (by
        unfold term_has_non_none_type
        rw [haTy]
        simp)
  rcases seq_value_canonical hValTy with ⟨sa, haEval⟩
  exact ⟨T, sa, haTy, haEval⟩

private theorem term_ne_stuck_of_smt_seq_type
    {t : Term} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    t ≠ Term.Stuck := by
  intro h
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

theorem singleton_elim_has_seq_type
    (c : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)) =
      SmtType.Seq T := by
  change __smtx_typeof
    (__eo_to_smt
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
        (Term.Boolean true) (__eo_list_singleton_elim_2 c))) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact hcTy
            · exact hTypes.1
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
            case UOp1 op A => cases op <;> simp at hNil
      | _ => simpa [__eo_list_singleton_elim_2] using hcTy
  | _ => simpa [__eo_list_singleton_elim_2] using hcTy

theorem singleton_elim_rel
    (M : SmtModel) (hM : model_wf M) (c : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt
                  (Term.Apply (Term.Apply
                    (Term.UOp UserOp.str_concat) head) tail)))
            · exact RuleProofs.smt_value_rel_symm _ _
                (strConcat_smt_value_rel_list_nil_right_empty M hM
                  head tail T hTypes.1 hNil hTypes.2)
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
            case UOp1 op A => cases op <;> simp at hNil
      | _ => simpa [__eo_list_singleton_elim_2] using
          RuleProofs.smt_value_rel_refl _
  | _ => simpa [__eo_list_singleton_elim_2] using
      RuleProofs.smt_value_rel_refl _

theorem singleton_elim_eval
    (M : SmtModel) (hM : model_wf M) (c : Term) (T : SmtType)
    (sc : SmtSeq)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true)
    (hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T)
    (hcEval : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq sc) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)) =
      SmtValue.Seq sc := by
  have hRel := singleton_elim_rel M hM c T hList hcTy
  rw [hcEval] at hRel
  have hTy := singleton_elim_has_seq_type c T hList hcTy
  have hValTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim
                (Term.UOp UserOp.str_concat) c))) =
        SmtType.Seq T := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)) (by
          unfold term_has_non_none_type
          rw [hTy]
          simp)
  rcases seq_value_canonical hValTy with ⟨actual, hEval⟩
  have hSeq : RuleProofs.smt_seq_rel actual sc := by
    have hsimpa := hRel
    try simp [hEval, RuleProofs.smt_value_rel] at hsimpa ⊢
    exact hsimpa
  exact hEval.trans
    (congrArg SmtValue.Seq ((RuleProofs.smt_seq_rel_iff_eq _ _).1 hSeq))

abbrev prefixPatternNil (a : Term) : Term :=
  __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof a)

abbrev prefixPatternTail (a pat : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_concat) pat)
    (prefixPatternNil a)

abbrev prefixPatternJoined (a pat : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.str_concat) a
    (prefixPatternTail a pat)

abbrev prefixPatternSource (a pat : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
    (prefixPatternJoined a pat)

abbrev prefixListTail (pat suffix : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_concat) pat) suffix

abbrev prefixListJoined (a pat suffix : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.str_concat) a
    (prefixListTail pat suffix)

abbrev prefixListSource (a pat suffix : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
    (prefixListJoined a pat suffix)

theorem prefix_list_source_eq_joined_of_left_cons
    (head rest pat suffix : Term)
    (hRestList :
      __eo_is_list (Term.UOp UserOp.str_concat) rest = Term.Boolean true)
    (hSuffixList :
      __eo_is_list (Term.UOp UserOp.str_concat) suffix =
        Term.Boolean true) :
    prefixListSource
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
        pat suffix =
      prefixListJoined
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
        pat suffix := by
  let a := Term.Apply
    (Term.Apply (Term.UOp UserOp.str_concat) head) rest
  have haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head rest (by simp) hRestList
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (prefixListTail pat suffix) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) pat suffix (by simp) hSuffixList
  have hRestRecNe := eo_list_concat_rec_ne_stuck_of_list
    (Term.UOp UserOp.str_concat) rest (prefixListTail pat suffix)
    hRestList (by simp)
  have hRecEq :
      __eo_list_concat_rec a (prefixListTail pat suffix) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head)
          (__eo_list_concat_rec rest (prefixListTail pat suffix)) := by
    exact eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
      head rest (prefixListTail pat suffix) hRestRecNe
  have hRestNotNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__eo_list_concat_rec rest (prefixListTail pat suffix)) =
        Term.Boolean false :=
    list_concat_rec_cons_right_is_not_nil rest pat suffix
      hRestList hSuffixList
  have hJoinedList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (prefixListJoined a pat suffix) = Term.Boolean true :=
    list_concat_is_list a (prefixListTail pat suffix) haList hTailList
  have hRecList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            (__eo_list_concat_rec rest (prefixListTail pat suffix))) =
        Term.Boolean true := by
    simpa [prefixListJoined,
      list_concat_reduce a (prefixListTail pat suffix) haList hTailList,
      hRecEq] using hJoinedList
  unfold prefixListSource prefixListJoined
  rw [list_concat_reduce a (prefixListTail pat suffix) haList hTailList,
    hRecEq]
  simp [__eo_list_singleton_elim, hJoinedList, hRecList,
    __eo_list_singleton_elim_2, hRestNotNil, __eo_ite, native_ite,
    native_teq, __eo_requires, native_not, SmtEval.native_not]

theorem prefix_list_source_eq_pattern_of_both_not_cons
    (a pat suffix : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hSuffixList :
      __eo_is_list (Term.UOp UserOp.str_concat) suffix =
        Term.Boolean true)
    (haNotCons :
      ¬ ∃ head tail,
        a = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail)
    (hSuffixNotCons :
      ¬ ∃ head tail,
        suffix = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail) :
    prefixListSource a pat suffix = pat := by
  have haNil := list_nil_of_list_not_cons a haList haNotCons
  have hSuffixNil :=
    list_nil_of_list_not_cons suffix hSuffixList hSuffixNotCons
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (prefixListTail pat suffix) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) pat suffix (by simp) hSuffixList
  have hRecEq :
      __eo_list_concat_rec a (prefixListTail pat suffix) =
        prefixListTail pat suffix :=
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true
      a (prefixListTail pat suffix) haNil
  unfold prefixListSource prefixListJoined
  rw [list_concat_reduce a (prefixListTail pat suffix) haList hTailList,
    hRecEq]
  simp [__eo_list_singleton_elim, hTailList,
    __eo_list_singleton_elim_2, hSuffixNil, __eo_ite, native_ite,
    native_teq, __eo_requires, native_not, SmtEval.native_not]

theorem prefix_pattern_source_eq_pattern_of_not_cons
    (a pat : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hNotCons :
      ¬ ∃ head tail,
        a = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail)
    (hNilNe : prefixPatternNil a ≠ Term.Stuck) :
    prefixPatternSource a pat = pat := by
  have haNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) a =
        Term.Boolean true :=
    list_nil_of_list_not_cons a haList hNotCons
  rcases typeof_seq_of_str_concat_nil_ne_stuck
      (__eo_typeof a) hNilNe with ⟨U, haEoTy⟩
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (prefixPatternNil a) = Term.Boolean true := by
    change __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof a)) =
        Term.Boolean true
    rw [haEoTy]
    cases U <;>
      simp [prefixPatternNil, __eo_nil, __eo_nil_str_concat,
        __seq_empty, __eo_is_list_nil, __eo_is_list_nil_str_concat,
        __eo_eq, native_teq] at hNilNe ⊢
    case UOp uop => cases uop <;> simp at hNilNe ⊢
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (prefixPatternNil a) = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true _ hNilNil
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (prefixPatternTail a pat) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) pat (prefixPatternNil a)
      (by simp) hNilList
  have hRecA :
      __eo_list_concat_rec a (prefixPatternTail a pat) =
        prefixPatternTail a pat :=
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true a
      (prefixPatternTail a pat) haNil
  unfold prefixPatternSource prefixPatternJoined
  rw [list_concat_reduce a (prefixPatternTail a pat) haList hTailList,
    hRecA]
  simp [__eo_list_singleton_elim, hTailList,
    __eo_list_singleton_elim_2, hNilNil, __eo_ite, native_ite,
    native_teq, __eo_requires, native_not, SmtEval.native_not]

theorem prefix_pattern_source_type_eval
    (M : SmtModel) (hM : model_wf M)
    (a pat z U : Term) (spat : SmtSeq)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTrans : RuleProofs.eo_has_smt_translation a)
    (hPatTy : __smtx_typeof (__eo_to_smt pat) =
      SmtType.Seq (__eo_to_smt_type U))
    (hPatEval : __smtx_model_eval M (__eo_to_smt pat) =
      SmtValue.Seq spat)
    (hRecEoTy : __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply Term.Seq U)
    (hzNe : z ≠ Term.Stuck)
    (hNilNe : prefixPatternNil a ≠ Term.Stuck) :
    ∃ out,
      __smtx_typeof (__eo_to_smt (prefixPatternSource a pat)) =
        SmtType.Seq (__eo_to_smt_type U) ∧
      __smtx_model_eval M (__eo_to_smt (prefixPatternSource a pat)) =
        SmtValue.Seq out ∧
      native_unpack_seq out = listEvalPrefix M a ++ native_unpack_seq spat := by
  let T := __eo_to_smt_type U
  by_cases hCons :
      ∃ head tail,
        a = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail
  · rcases hCons with ⟨head, rest, rfl⟩
    have hRestList :
        __eo_is_list (Term.UOp UserOp.str_concat) rest =
          Term.Boolean true :=
      eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.str_concat) head rest haList
    have hRestRecNe := eo_list_concat_rec_ne_stuck_of_list
      (Term.UOp UserOp.str_concat) rest z hRestList hzNe
    have hRecEq :
        __eo_list_concat_rec
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) head) rest) z =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            (__eo_list_concat_rec rest z) :=
      eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head rest z hRestRecNe
    have hHeadEoTy : __eo_typeof head = Term.Apply Term.Seq U := by
      rw [hRecEq] at hRecEoTy
      exact (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
        head (__eo_list_concat_rec rest z) U hRecEoTy).1
    have haNN :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) ≠
          SmtType.None := haTrans
    rcases str_concat_args_of_non_none head rest haNN with
      ⟨V, hHeadTyV, hRestTyV⟩
    have hHeadTrans : RuleProofs.eo_has_smt_translation head := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hHeadTyV]
      exact seq_ne_none V
    have hHeadTyT :
        __smtx_typeof (__eo_to_smt head) = SmtType.Seq T := by
      simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
        head U hHeadTrans hHeadEoTy
    have hVT : V = T := by
      have hEq : SmtType.Seq V = SmtType.Seq T := by
        rw [← hHeadTyV, hHeadTyT]
      injection hEq
    have haTy :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq head rest T hHeadTyT
        (by simpa [hVT] using hRestTyV)
    have hNilTy :
        __smtx_typeof
            (__eo_to_smt
              (prefixPatternNil
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest))) =
          SmtType.Seq T :=
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq _ T haTy
    have hNilEval :
        __smtx_model_eval M
            (__eo_to_smt
              (prefixPatternNil
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest))) =
          SmtValue.Seq (SmtSeq.empty T) :=
      eval_nil_str_concat_typeof_of_smt_type_seq M _ T haTy
    have hNilNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (prefixPatternNil
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          Term.Boolean true := by
      have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest) (by
          rw [haTy]
          exact seq_ne_none T)
      have hTy :
          __eo_to_smt_type
              (__eo_typeof
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
            SmtType.Seq T := by rw [← hMatch, haTy]
      exact strConcat_nil_is_list_nil_of_type hTy
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (prefixPatternNil
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          Term.Boolean true :=
      eo_is_list_str_concat_nil_true_of_nil_true _ hNilNil
    have hTailList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (prefixPatternTail
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) pat _ (by simp) hNilList
    have hTailTy :
        __smtx_typeof
            (__eo_to_smt
              (prefixPatternTail
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq pat _ T (by simpa [T] using hPatTy)
        hNilTy
    have hTailEval :
        __smtx_model_eval M
            (__eo_to_smt
              (prefixPatternTail
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)) =
          SmtValue.Seq
            (native_pack_seq (__smtx_elem_typeof_seq_value spat)
              (native_unpack_seq spat)) := by
      rw [smtx_model_eval_str_concat_term_eq, hPatEval, hNilEval]
      change SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value spat)
            (native_unpack_seq spat ++ [])) = _
      rw [List.append_nil]
    let tailOut := native_pack_seq (__smtx_elem_typeof_seq_value spat)
      (native_unpack_seq spat)
    rcases list_concat_eval_prefix_of_translation M hM
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
        (prefixPatternTail
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)
        tailOut haList hTailList haTrans hTailEval with
      ⟨joinedOut, hJoinedEval, hJoinedUnpack⟩
    have hJoinedTy :
        __smtx_typeof
            (__eo_to_smt
              (prefixPatternJoined
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)) =
          SmtType.Seq T :=
      list_concat_has_seq_type _ _ T haList hTailList haTy hTailTy
    have hJoinedList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (prefixPatternJoined
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat) =
          Term.Boolean true :=
      list_concat_is_list _ _ haList hTailList
    have hSourceTy := singleton_elim_has_seq_type
      (prefixPatternJoined
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)
      T hJoinedList hJoinedTy
    have hSourceEval := singleton_elim_eval M hM
      (prefixPatternJoined
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest) pat)
      T joinedOut hJoinedList hJoinedTy hJoinedEval
    refine ⟨joinedOut, by simpa [T] using hSourceTy,
      hSourceEval, ?_⟩
    simpa [tailOut, Smtm.native_unpack_pack_seq] using hJoinedUnpack
  · have hSourceEq := prefix_pattern_source_eq_pattern_of_not_cons
      a pat haList hCons hNilNe
    refine ⟨spat, ?_, ?_, ?_⟩
    · rwa [hSourceEq]
    · rwa [hSourceEq]
    · rw [listEvalPrefix_eq_nil_of_not_cons M a hCons]
      simp

theorem prefix_list_source_type_eval
    (M : SmtModel) (hM : model_wf M)
    (a pat suffix z U : Term) (spat : SmtSeq)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hSuffixList :
      __eo_is_list (Term.UOp UserOp.str_concat) suffix =
        Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) =
      SmtType.Seq (__eo_to_smt_type U))
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hPatTy : __smtx_typeof (__eo_to_smt pat) =
      SmtType.Seq (__eo_to_smt_type U))
    (hPatEval : __smtx_model_eval M (__eo_to_smt pat) =
      SmtValue.Seq spat)
    (hSuffixRecEoTy :
      __eo_typeof (__eo_list_concat_rec suffix z) =
        Term.Apply Term.Seq U)
    (hzNe : z ≠ Term.Stuck)
    (hSourceEoTy : __eo_typeof (prefixListSource a pat suffix) =
      Term.Apply Term.Seq U) :
    ∃ out,
      __smtx_typeof (__eo_to_smt (prefixListSource a pat suffix)) =
        SmtType.Seq (__eo_to_smt_type U) ∧
      __smtx_model_eval M (__eo_to_smt (prefixListSource a pat suffix)) =
        SmtValue.Seq out ∧
      native_unpack_seq out =
        (listEvalPrefix M a ++ native_unpack_seq spat) ++
          listEvalPrefix M suffix := by
  let T := __eo_to_smt_type U
  have haTrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    exact seq_ne_none T
  by_cases hSuffixCons :
      ∃ head tail,
        suffix = Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) tail
  · rcases hSuffixCons with ⟨head, rest, rfl⟩
    have hRestList :
        __eo_is_list (Term.UOp UserOp.str_concat) rest =
          Term.Boolean true :=
      eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.str_concat) head rest hSuffixList
    have hRestRecNe := eo_list_concat_rec_ne_stuck_of_list
      (Term.UOp UserOp.str_concat) rest z hRestList hzNe
    have hRecEq :
        __eo_list_concat_rec
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) head) rest) z =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head)
            (__eo_list_concat_rec rest z) :=
      eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head rest z hRestRecNe
    have hHeadEoTy : __eo_typeof head = Term.Apply Term.Seq U := by
      rw [hRecEq] at hSuffixRecEoTy
      exact (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
        head (__eo_list_concat_rec rest z) U hSuffixRecEoTy).1
    have hSuffixNN :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) ≠
          SmtType.None := hSuffixTrans
    rcases str_concat_args_of_non_none head rest hSuffixNN with
      ⟨V, hHeadTyV, hRestTyV⟩
    have hHeadTrans : RuleProofs.eo_has_smt_translation head := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hHeadTyV]
      exact seq_ne_none V
    have hHeadTyT : __smtx_typeof (__eo_to_smt head) =
        SmtType.Seq T := by
      simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
        head U hHeadTrans hHeadEoTy
    have hVT : V = T := by
      have hEq : SmtType.Seq V = SmtType.Seq T := by
        rw [← hHeadTyV, hHeadTyT]
      injection hEq
    have hSuffixTy :
        __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq head rest T hHeadTyT
        (by simpa [hVT] using hRestTyV)
    rcases list_eval_prefix M hM
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
        T hSuffixList hSuffixTy with
      ⟨ssuffix, hSuffixEval, hSuffixUnpack⟩
    have hTailList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (prefixListTail pat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) pat _ (by simp) hSuffixList
    have hTailTy :
        __smtx_typeof
            (__eo_to_smt
              (prefixListTail pat
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest))) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq pat _ T (by simpa [T] using hPatTy)
        hSuffixTy
    let tailOut := native_pack_seq (__smtx_elem_typeof_seq_value spat)
      (native_unpack_seq spat ++ native_unpack_seq ssuffix)
    have hTailEval :
        __smtx_model_eval M
            (__eo_to_smt
              (prefixListTail pat
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest))) =
          SmtValue.Seq tailOut := by
      rw [smtx_model_eval_str_concat_term_eq, hPatEval, hSuffixEval]
      rfl
    rcases list_concat_eval_prefix_of_translation M hM a
        (prefixListTail pat
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) rest))
        tailOut haList hTailList haTrans hTailEval with
      ⟨joinedOut, hJoinedEval, hJoinedUnpack⟩
    have hJoinedTy :
        __smtx_typeof
            (__eo_to_smt
              (prefixListJoined a pat
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest))) =
          SmtType.Seq T :=
      list_concat_has_seq_type a _ T haList hTailList haTy hTailTy
    have hJoinedList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (prefixListJoined a pat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) head) rest)) =
          Term.Boolean true :=
      list_concat_is_list a _ haList hTailList
    have hSourceTy := singleton_elim_has_seq_type _ T
      hJoinedList hJoinedTy
    have hSourceEval := singleton_elim_eval M hM _ T joinedOut
      hJoinedList hJoinedTy hJoinedEval
    refine ⟨joinedOut, by simpa [T] using hSourceTy,
      hSourceEval, ?_⟩
    rw [hJoinedUnpack]
    simp [tailOut, Smtm.native_unpack_pack_seq,
      hSuffixUnpack, List.append_assoc]
  · by_cases haCons :
        ∃ head tail,
          a = Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) tail
    · rcases haCons with ⟨head, rest, rfl⟩
      have hRestList :
          __eo_is_list (Term.UOp UserOp.str_concat) rest =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) head rest haList
      have hSourceEq := prefix_list_source_eq_joined_of_left_cons
        head rest pat suffix hRestList hSuffixList
      have hJoinedEoTy :
          __eo_typeof
              (prefixListJoined
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
                pat suffix) = Term.Apply Term.Seq U := by
        rwa [← hSourceEq]
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (prefixListTail pat suffix) = Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) pat suffix (by simp) hSuffixList
      have hJoinedRecEoTy :
          __eo_typeof
              (__eo_list_concat_rec
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
                (prefixListTail pat suffix)) =
            Term.Apply Term.Seq U := by
        rw [← list_concat_reduce _ _ haList hTailList]
        exact hJoinedEoTy
      have hTailEoTy :=
        StrConcatUnifySupport.eo_typeof_list_concat_rec_right_type_eq_seq
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
          (prefixListTail pat suffix) U haList hJoinedRecEoTy
      have hSuffixEoTy :=
        (StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
          pat suffix U hTailEoTy).2
      have hSuffixTy :
          __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
        simpa [T] using StrEqReplSupport.smtx_typeof_of_eo_seq
          suffix U hSuffixTrans hSuffixEoTy
      rcases list_eval_prefix M hM suffix T hSuffixList hSuffixTy with
        ⟨ssuffix, hSuffixEval, hSuffixUnpack⟩
      have hTailTy :
          __smtx_typeof (__eo_to_smt (prefixListTail pat suffix)) =
            SmtType.Seq T :=
        smt_typeof_str_concat_of_seq pat suffix T
          (by simpa [T] using hPatTy) hSuffixTy
      let tailOut := native_pack_seq (__smtx_elem_typeof_seq_value spat)
        (native_unpack_seq spat ++ native_unpack_seq ssuffix)
      have hTailEval :
          __smtx_model_eval M
              (__eo_to_smt (prefixListTail pat suffix)) =
            SmtValue.Seq tailOut := by
        rw [smtx_model_eval_str_concat_term_eq, hPatEval, hSuffixEval]
        rfl
      rcases list_concat_eval_prefix_of_translation M hM
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
          (prefixListTail pat suffix) tailOut haList hTailList
          haTrans hTailEval with ⟨joinedOut, hJoinedEval, hJoinedUnpack⟩
      have hJoinedTy :
          __smtx_typeof
              (__eo_to_smt
                (prefixListJoined
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
                  pat suffix)) = SmtType.Seq T :=
        list_concat_has_seq_type _ _ T haList hTailList haTy hTailTy
      have hJoinedList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (prefixListJoined
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) head) rest)
                pat suffix) = Term.Boolean true :=
        list_concat_is_list _ _ haList hTailList
      have hSourceTy := singleton_elim_has_seq_type _ T
        hJoinedList hJoinedTy
      have hSourceEval := singleton_elim_eval M hM _ T joinedOut
        hJoinedList hJoinedTy hJoinedEval
      refine ⟨joinedOut, by simpa [T] using hSourceTy,
        hSourceEval, ?_⟩
      rw [hJoinedUnpack]
      simp [tailOut, Smtm.native_unpack_pack_seq,
        hSuffixUnpack, List.append_assoc]
    · have hSourceEq := prefix_list_source_eq_pattern_of_both_not_cons
        a pat suffix haList hSuffixList haCons hSuffixCons
      refine ⟨spat, ?_, ?_, ?_⟩
      · rwa [hSourceEq]
      · rwa [hSourceEq]
      · rw [listEvalPrefix_eq_nil_of_not_cons M a haCons,
          listEvalPrefix_eq_nil_of_not_cons M suffix hSuffixCons]
        simp

theorem native_seq_prefix_eq_append_self
    (pat suffix : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ suffix) = true := by
  exact native_seq_prefix_eq_append_of_eq_true pat pat suffix
    (native_seq_prefix_eq_self pat)

theorem native_seq_indexof_rec_le_of_prefix_at
    (pat : List SmtValue) :
    ∀ (xs : List SmtValue) (i fuel offset : Nat),
      offset < fuel →
      native_seq_prefix_eq pat (xs.drop offset) = true →
      ∃ found : Nat,
        found ≤ offset ∧
          native_seq_indexof_rec xs pat i fuel = Int.ofNat (i + found) := by
  intro xs i fuel
  induction fuel generalizing xs i with
  | zero =>
      intro offset hOffset
      omega
  | succ fuel ih =>
      intro offset hOffset hPrefix
      unfold native_seq_indexof_rec
      by_cases hHere : native_seq_prefix_eq pat xs = true
      · rw [if_pos hHere]
        exact ⟨0, Nat.zero_le _, by simp⟩
      · rw [if_neg hHere]
        cases offset with
        | zero =>
            simp at hPrefix
            exact False.elim (hHere hPrefix)
        | succ offset =>
            cases xs with
            | nil =>
                have hNil : native_seq_prefix_eq pat [] = true := by
                  simpa using hPrefix
                exact False.elim (hHere hNil)
            | cons x xs =>
                have hTailPrefix :
                    native_seq_prefix_eq pat (xs.drop offset) = true := by
                  simpa using hPrefix
                rcases ih xs (i + 1) offset (by omega) hTailPrefix with
                  ⟨found, hFoundLe, hRec⟩
                refine ⟨found + 1, by omega, ?_⟩
                change native_seq_indexof_rec xs pat (i + 1) fuel =
                  Int.ofNat (i + (found + 1))
                rw [hRec]
                congr 1
                omega

theorem native_seq_indexof_zero_le_of_prefix_at
    (xs pat : List SmtValue) (offset : Nat)
    (hFit : offset + pat.length ≤ xs.length)
    (hPrefix : native_seq_prefix_eq pat (xs.drop offset) = true) :
    0 ≤ native_seq_indexof xs pat 0 ∧
      native_seq_indexof xs pat 0 ≤ Int.ofNat offset := by
  have hPatFit : pat.length ≤ xs.length := by omega
  have hOffsetFuel : offset < xs.length - pat.length + 1 := by omega
  rcases native_seq_indexof_rec_le_of_prefix_at pat xs 0
      (xs.length - pat.length + 1) offset hOffsetFuel hPrefix with
    ⟨found, hFoundLe, hRec⟩
  rw [native_seq_indexof_eq_rec]
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
  simp only [List.drop_zero]
  rw [dif_pos hPatFit, hRec]
  constructor
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_le.mpr
    simpa using hFoundLe

theorem native_seq_prefix_eq_at_index_of_nonneg
    (xs pat : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_prefix_eq pat
        (xs.drop (Int.toNat (native_seq_indexof xs pat 0))) = true := by
  let k := Int.toNat (native_seq_indexof xs pat 0)
  have hBound := StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
    xs pat hNonneg
  have hKLe : k ≤ xs.length := by omega
  have hDecomp := StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
    xs pat hNonneg
  have hDropped := congrArg (List.drop k) hDecomp
  have hTakeLen : (xs.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left hKLe]
  have hDropEq :
      pat ++ xs.drop (k + pat.length) = xs.drop k := by
    simpa [k, hTakeLen] using hDropped
  rw [← hDropEq]
  exact native_seq_prefix_eq_append_self pat _

theorem native_seq_prefix_eq_drop_add_of_prefixes
    (xs whole pat : List SmtValue) (start offset : Nat)
    (hWhole :
      native_seq_prefix_eq whole (xs.drop start) = true)
    (hPat : native_seq_prefix_eq pat (whole.drop offset) = true)
    (hOffset : offset ≤ whole.length) :
    native_seq_prefix_eq pat (xs.drop (start + offset)) = true := by
  have hWholeEq := native_seq_prefix_eq_append_drop
    whole (xs.drop start) hWhole
  have hDropEq :
      whole.drop offset ++ (xs.drop start).drop whole.length =
        xs.drop (start + offset) := by
    calc
      whole.drop offset ++ (xs.drop start).drop whole.length =
          (whole ++ (xs.drop start).drop whole.length).drop offset := by
            rw [list_drop_append_of_le_length whole
              ((xs.drop start).drop whole.length) offset hOffset]
      _ = (xs.drop start).drop offset := by rw [hWholeEq]
      _ = xs.drop (start + offset) := by
        rw [List.drop_drop]
  have hPatEq := native_seq_prefix_eq_append_drop
    pat (whole.drop offset) hPat
  rw [← hDropEq, ← hPatEq]
  simpa [List.append_assoc] using
    native_seq_prefix_eq_append_self pat
      ((whole.drop offset).drop pat.length ++
        (xs.drop start).drop whole.length)

theorem native_seq_indexof_take_index_append_self
    (xs pat : List SmtValue)
    (hNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    let k := Int.toNat (native_seq_indexof xs pat 0)
    native_seq_indexof (xs.take k ++ xs) xs 0 = Int.ofNat k := by
  let k := Int.toNat (native_seq_indexof xs pat 0)
  let pref := xs.take k
  let expanded := pref ++ xs
  have hCast : Int.ofNat k = native_seq_indexof xs pat 0 :=
    Int.toNat_of_nonneg hNonneg
  have hPatBound :=
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
      xs pat hNonneg
  have hKLe : k ≤ xs.length := by omega
  have hPrefLen : pref.length = k := by
    simp [pref, List.length_take, Nat.min_eq_left hKLe]
  have hExpandedDropK : expanded.drop k = xs := by
    dsimp [expanded]
    rw [list_drop_append_of_le_length pref xs k (by simp [hPrefLen])]
    simp [hPrefLen]
  have hXsAtK :
      native_seq_prefix_eq xs (expanded.drop k) = true := by
    rw [hExpandedDropK]
    exact native_seq_prefix_eq_self xs
  have hExpandedFit : k + xs.length ≤ expanded.length := by
    simp [expanded, hPrefLen]
  have hExpandedBounds := native_seq_indexof_zero_le_of_prefix_at
    expanded xs k hExpandedFit hXsAtK
  have hExpandedNonneg := hExpandedBounds.1
  have hExpandedLe := hExpandedBounds.2
  apply Int.le_antisymm hExpandedLe
  apply Int.le_of_not_gt
  intro hExpandedLt
  let j := Int.toNat (native_seq_indexof expanded xs 0)
  have hExpandedCast :
      Int.ofNat j = native_seq_indexof expanded xs 0 :=
    Int.toNat_of_nonneg hExpandedNonneg
  have hJLtK : j < k := by
    apply Int.ofNat_lt.mp
    calc
      Int.ofNat j = native_seq_indexof expanded xs 0 := hExpandedCast
      _ < Int.ofNat k := hExpandedLt
  have hXsPrefixAtJ :
      native_seq_prefix_eq xs (expanded.drop j) = true := by
    simpa [j] using native_seq_prefix_eq_at_index_of_nonneg
      expanded xs hExpandedNonneg
  have hPatPrefixAtK :
      native_seq_prefix_eq pat (xs.drop k) = true := by
    simpa [k] using native_seq_prefix_eq_at_index_of_nonneg
      xs pat hNonneg
  have hPatPrefixExpanded :
      native_seq_prefix_eq pat (expanded.drop (j + k)) = true :=
    native_seq_prefix_eq_drop_add_of_prefixes expanded xs pat j k
      hXsPrefixAtJ hPatPrefixAtK hKLe
  have hExpandedDropJK : expanded.drop (j + k) = xs.drop j := by
    rw [Nat.add_comm, ← List.drop_drop, hExpandedDropK]
  rw [hExpandedDropJK] at hPatPrefixExpanded
  have hJFit : j + pat.length ≤ xs.length := by omega
  have hSourceLeJ :=
    (native_seq_indexof_zero_le_of_prefix_at xs pat j hJFit
      hPatPrefixExpanded).2
  rw [← hCast] at hSourceLeJ
  have hKLeJ : k ≤ j := Int.ofNat_le.mp hSourceLeJ
  omega

theorem native_seq_replace_reinsert_source_of_contains
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = true) :
    native_seq_replace (native_seq_replace xs pat xs) xs repl =
      native_seq_replace xs pat repl := by
  have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    exact of_decide_eq_true hContains
  let k := Int.toNat (native_seq_indexof xs pat 0)
  let before := xs.take k
  let after := xs.drop (k + pat.length)
  let core := before ++ xs
  have hKLe : k ≤ xs.length := by
    have hBound := StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
      xs pat hNonneg
    omega
  have hBeforeLen : before.length = k := by
    simp [before, List.length_take, Nat.min_eq_left hKLe]
  have hInnerSource :
      native_seq_replace xs pat xs = before ++ xs ++ after := by
    simpa [before, after, k] using
      StrEqReplSupport.native_seq_replace_of_indexof_nonneg
        xs pat xs hNonneg
  have hInnerRepl :
      native_seq_replace xs pat repl = before ++ repl ++ after := by
    simpa [before, after, k] using
      StrEqReplSupport.native_seq_replace_of_indexof_nonneg
        xs pat repl hNonneg
  rw [hInnerSource, hInnerRepl]
  have hCoreIndex :
      native_seq_indexof core xs 0 = Int.ofNat k := by
    simpa [core, before, k] using
      native_seq_indexof_take_index_append_self xs pat hNonneg
  have hCoreNonneg : 0 ≤ native_seq_indexof core xs 0 := by
    rw [hCoreIndex]
    exact Int.natCast_nonneg _
  have hAppend :=
    StrEqReplSupport.native_seq_replace_append_of_indexof_nonneg
      core xs repl after hCoreNonneg
  change native_seq_replace (core ++ after) xs repl =
    before ++ repl ++ after
  rw [hAppend,
    StrEqReplSupport.native_seq_replace_of_indexof_nonneg
      core xs repl hCoreNonneg,
    hCoreIndex]
  simp [core, hBeforeLen]

theorem native_seq_replace_result_source_id_of_contains
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = true)
    (hPatRepl : pat ≠ repl)
    (hReplLe : repl.length ≤ pat.length) :
    native_seq_replace (native_seq_replace xs pat repl) xs repl =
      native_seq_replace xs pat repl := by
  let result := native_seq_replace xs pat repl
  have hResultLe : result.length ≤ xs.length := by
    exact StrEqReplSupport.native_seq_replace_length_le_of_repl_length_le
      xs pat repl hReplLe
  have hResultAbsent : native_seq_contains result xs = false := by
    cases hResultContains : native_seq_contains result xs with
    | false => rfl
    | true =>
        have hSourceLeResult :=
          StrContainsReplCharSupport.native_seq_length_le_of_contains
            result xs hResultContains
        have hLengths : result.length = xs.length := by omega
        have hResultEq : result = xs :=
          StrEqReplSupport.eq_of_native_seq_contains_of_same_len
            result xs hResultContains hLengths
        have hPatternAbsent :=
          (StrEqReplSupport.native_seq_replace_eq_self_iff_contains_false
            xs pat repl hPatRepl).1 hResultEq
        rw [hContains] at hPatternAbsent
        contradiction
  exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    result xs repl hResultAbsent

theorem native_seq_replace_lookahead_id
    (xs pat repl : List SmtValue)
    (hPatRepl : pat ≠ repl)
    (hReplLe : repl.length ≤ pat.length) :
    native_seq_replace (native_seq_replace xs pat xs) xs repl =
      native_seq_replace (native_seq_replace xs pat repl) xs repl := by
  cases hContains : native_seq_contains xs pat with
  | false =>
      rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
        xs pat xs hContains]
      rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
        xs pat repl hContains]
  | true =>
      rw [native_seq_replace_reinsert_source_of_contains
        xs pat repl hContains]
      rw [native_seq_replace_result_source_id_of_contains
        xs pat repl hContains hPatRepl hReplLe]

theorem native_seq_indexof_append_after_present
    (before pat suffix : List SmtValue) :
    native_seq_indexof ((before ++ pat) ++ suffix) pat 0 =
      native_seq_indexof (before ++ pat) pat 0 := by
  have hContains : native_seq_contains (before ++ pat) pat = true := by
    simpa using
      StrContainsReplCharSupport.native_seq_contains_of_decomp
        before pat []
  have hNonneg : 0 ≤ native_seq_indexof (before ++ pat) pat 0 := by
    unfold native_seq_contains at hContains
    exact of_decide_eq_true hContains
  exact native_seq_indexof_append_of_nonneg
    (before ++ pat) pat suffix 0 hNonneg

theorem native_seq_replace_append_after_present
    (before pat suffix repl : List SmtValue) :
    native_seq_replace ((before ++ pat) ++ suffix) pat repl =
      native_seq_replace (before ++ pat) pat repl ++ suffix := by
  have hContains : native_seq_contains (before ++ pat) pat = true := by
    simpa using
      StrContainsReplCharSupport.native_seq_contains_of_decomp
        before pat []
  have hNonneg : 0 ≤ native_seq_indexof (before ++ pat) pat 0 := by
    unfold native_seq_contains at hContains
    exact of_decide_eq_true hContains
  exact StrEqReplSupport.native_seq_replace_append_of_indexof_nonneg
    (before ++ pat) pat repl suffix hNonneg

theorem native_seq_replace_duplicate_suffix_of_pattern_length_one
    (before duplicate middle pat repl : List SmtValue)
    (hLen : pat.length = 1) :
    native_seq_replace
        (((before ++ duplicate) ++ middle) ++ duplicate) pat repl =
      native_seq_replace ((before ++ duplicate) ++ middle) pat repl ++
        duplicate := by
  let core := (before ++ duplicate) ++ middle
  by_cases hCore : native_seq_contains core pat = true
  · have hNonneg : 0 ≤ native_seq_indexof core pat 0 := by
      unfold native_seq_contains at hCore
      exact of_decide_eq_true hCore
    exact StrEqReplSupport.native_seq_replace_append_of_indexof_nonneg
      core pat repl duplicate hNonneg
  · have hCoreFalse : native_seq_contains core pat = false := by
      cases h : native_seq_contains core pat
      · rfl
      · exact False.elim (hCore h)
    have hDuplicateFalse : native_seq_contains duplicate pat = false := by
      cases hDup : native_seq_contains duplicate pat
      · rfl
      · have hBeforeDup :
            native_seq_contains (before ++ duplicate) pat = true := by
          rw [StrContainsReplCharSupport.native_seq_contains_append_of_pattern_length_one
            before duplicate pat hLen]
          simp [SmtEval.native_or, hDup]
        have hCoreTrue : native_seq_contains core pat = true := by
          dsimp [core]
          rw [StrContainsReplCharSupport.native_seq_contains_append_of_pattern_length_one
            (before ++ duplicate) middle pat hLen]
          simp [SmtEval.native_or, hBeforeDup]
        exact False.elim (hCore hCoreTrue)
    have hAppendFalse : native_seq_contains (core ++ duplicate) pat = false := by
      rw [StrContainsReplCharSupport.native_seq_contains_append_of_pattern_length_one
        core duplicate pat hLen]
      simp [SmtEval.native_or, hCoreFalse, hDuplicateFalse]
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      core pat repl hCoreFalse]
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      (core ++ duplicate) pat repl hAppendFalse]

end StringRewriteSupport
