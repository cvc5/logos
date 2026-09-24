module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem strConcat_args_of_seq_type (x y : Term) (T : SmtType)
    (hTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
          SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  simpa [mkConcat] using str_concat_args_of_seq_type x y T hTy

theorem strConcat_typeof_concat_of_seq (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
      SmtType.Seq T := by
  simpa [mkConcat] using smt_typeof_str_concat_of_seq x y T hxTy hyTy

theorem strConcat_is_list_nil_true_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true :=
  eo_is_list_str_concat_nil_true_of_nil_true nil hNil

theorem strConcat_is_list_cons_true_of_tail_list (x y : Term)
    (hTail :
      __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
      Term.Boolean true :=
  eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.str_concat) x y (by decide) hTail

theorem strConcat_is_list_cons_head_eq_of_true (g x y : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) =
        Term.Boolean true) :
    g = Term.UOp UserOp.str_concat :=
  eo_is_list_cons_head_eq_of_true
    (Term.UOp UserOp.str_concat) g x y hList

theorem strConcat_is_list_tail_true_of_cons_self (x y : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
        Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
  eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y hList

theorem strConcat_is_list_concat_rec_of_lists (a z : Term)
    (haList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hzList :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__eo_list_concat_rec a z) =
      Term.Boolean true :=
  eo_list_concat_rec_is_list_true_of_lists
    (Term.UOp UserOp.str_concat) a z haList hzList

theorem strConcat_typeof_list_concat_rec_of_seq (a z : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.Seq T :=
  smt_typeof_list_concat_rec_str_concat_of_seq a z T hList haTy hzTy

theorem strConcat_smt_value_rel_list_nil_right_empty
    (M : SmtModel) (hM : model_wf M) (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_list_nil_right_empty M hM x nil T
      hxTy hNil hNilTy

theorem strConcat_smt_value_rel_left_congr
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hxy : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) z)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) z))) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_left_congr M hM x y z T hxTy hyTy hzTy hxy

theorem strConcat_smt_value_rel_right_congr
    (M : SmtModel) (hM : model_wf M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hyz : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) z))) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_right_congr M hM x y z T hxTy hyTy hzTy hyz

theorem strConcat_smt_value_rel_list_concat_rec
    (M : SmtModel) (hM : model_wf M) (a z : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) z))) := by
  simpa [mkConcat] using
    smt_value_rel_list_concat_rec_str_concat M hM a z T hList haTy hzTy

theorem strConcat_eval_seq_empty_typeof
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) :=
  eval_seq_empty_typeof M x T hxTy

theorem strConcat_is_list_nil_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty (__eo_typeof x)) = Term.Boolean true :=
  have hEmpty : __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  by
    cases hA : __eo_typeof x <;>
      simp [hA, __seq_empty, __eo_is_list_nil, __eo_is_list_nil_str_concat,
        __eo_eq, native_teq] at hEmpty ⊢
    case Apply f a =>
      cases f with
      | UOp op =>
          cases op <;> try rfl
          case Seq =>
            cases a <;> try rfl
            case UOp op =>
              cases op <;> try rfl
      | _ =>
          rfl

theorem strConcat_smt_value_rel_right_empty_typeof
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_right_empty M hM x T hxTy

theorem strConcat_smt_value_rel_left_empty_typeof
    (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x))) x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_left_empty M hM x T hxTy

theorem strConcat_smt_value_rel_right_eval_empty
    (M : SmtModel) (hM : model_wf M) (x empty : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyEval :
      __smtx_model_eval M (__eo_to_smt empty) =
        SmtValue.Seq (SmtSeq.empty T)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmptyEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  rw [List.append_nil, hsxElem]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx hsxElem)

theorem strConcat_smt_value_rel_left_eval_empty
    (M : SmtModel) (hM : model_wf M) (empty x : Term)
    (T : SmtType)
    (hEmptyEval :
      __smtx_model_eval M (__eo_to_smt empty) =
        SmtValue.Seq (SmtSeq.empty T))
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) empty) x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hEmptyEval, hxEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value
      (SmtSeq.empty T)) ([] ++ native_unpack_seq sx))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  simp [__smtx_elem_typeof_seq_value]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx hsxElem)

theorem smt_value_rel_seq_right {v : SmtValue} {s : SmtSeq} :
    RuleProofs.smt_value_rel v (SmtValue.Seq s) ->
    ∃ s', v = SmtValue.Seq s' ∧ RuleProofs.smt_seq_rel s' s := by
  intro hRel
  cases v <;>
    simp [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
      __smtx_model_eval_eq, native_veq] at hRel ⊢
  case Seq s' =>
    exact hRel

theorem smt_value_rel_seq_left {s : SmtSeq} {v : SmtValue} :
    RuleProofs.smt_value_rel (SmtValue.Seq s) v ->
    ∃ s', v = SmtValue.Seq s' ∧ RuleProofs.smt_seq_rel s s' := by
  intro hRel
  rcases smt_value_rel_seq_right
      (RuleProofs.smt_value_rel_symm (SmtValue.Seq s) v hRel) with
    ⟨s', hv, hs'⟩
  exact ⟨s', hv, RuleProofs.smt_seq_rel_symm s' s hs'⟩

theorem smt_seq_rel_pack_append_both (T : SmtType)
    (sx sx' sy sy' : SmtSeq)
    (hx : RuleProofs.smt_seq_rel sx sx')
    (hy : RuleProofs.smt_seq_rel sy sy') :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sx' ++ native_unpack_seq sy')) := by
  have hxEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 hx
  have hyEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 hy
  exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by rw [hxEq, hyEq])

theorem smt_value_rel_str_concat_congr_of_seq_eval
    (M : SmtModel) (x x' y y' : Term) (sx' sy' : SmtSeq)
    (hx'Eval :
      __smtx_model_eval M (__eo_to_smt x') = SmtValue.Seq sx')
    (hy'Eval :
      __smtx_model_eval M (__eo_to_smt y') = SmtValue.Seq sy')
    (hxx : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt x')))
    (hyy : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt y'))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x' y'))) := by
  rcases smt_value_rel_seq_right (by simpa [hx'Eval] using hxx) with
    ⟨sx, hxEval, hxRel⟩
  rcases smt_value_rel_seq_right (by simpa [hy'Eval] using hyy) with
    ⟨sy, hyEval, hyRel⟩
  let T := __smtx_elem_typeof_seq_value sx'
  have hLeftPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ native_unpack_seq sy))
        (native_pack_seq T
          (native_unpack_seq sx ++ native_unpack_seq sy)) := by
    have hxEq := (RuleProofs.smt_seq_rel_iff_eq _ _).1 hxRel
    exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 (by
      change
        native_pack_seq (__smtx_elem_typeof_seq_value sx)
            (native_unpack_seq sx ++ native_unpack_seq sy) =
          native_pack_seq (__smtx_elem_typeof_seq_value sx')
            (native_unpack_seq sx ++ native_unpack_seq sy)
      rw [hxEq])
  have hBoth :
      RuleProofs.smt_seq_rel
        (native_pack_seq T
          (native_unpack_seq sx ++ native_unpack_seq sy))
        (native_pack_seq T
          (native_unpack_seq sx' ++ native_unpack_seq sy')) :=
    smt_seq_rel_pack_append_both T sx sx' sy sy' hxRel hyRel
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
  rw [hxEval, hyEval, hx'Eval, hy'Eval]
  change __smtx_model_eval_eq
    (SmtValue.Seq
      (native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq
      (native_pack_seq (__smtx_elem_typeof_seq_value sx')
        (native_unpack_seq sx' ++ native_unpack_seq sy'))) =
      SmtValue.Boolean true
  exact RuleProofs.smt_seq_rel_trans
    (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy))
    (native_pack_seq T
      (native_unpack_seq sx ++ native_unpack_seq sy))
    (native_pack_seq T
      (native_unpack_seq sx' ++ native_unpack_seq sy'))
    hLeftPack hBoth

theorem smt_value_rel_str_concat_assoc_of_seq_eval
    (M : SmtModel) (x y z : Term) (sx sy sz : SmtSeq)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z)))) := by
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq M (mkConcat x y) z]
  rw [smtx_model_eval_str_concat_term_eq M x y]
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, List.append_assoc,
    RuleProofs.smtx_model_eval_eq_refl]

theorem smt_value_rel_str_concat_list_nil_left_empty_eval
    (M : SmtModel) (hM : model_wf M) (nil x : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat nil x)))
      (__smtx_model_eval M (__eo_to_smt x)) :=
  smt_value_rel_str_concat_list_nil_left_empty M hM nil x T
    hNil hNilTy hxTy

theorem smt_value_rel_str_concat_list_nil_right_empty_eval
    (M : SmtModel) (x nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hxSeq :
      ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hNilSeq :
      ∃ snil, __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Seq snil) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases hxSeq with ⟨sx, hxEval⟩
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq] at hNil
  case UOp1 op A =>
    cases op <;>
      simp at hNil
    case seq_empty =>
      rcases hNilSeq with ⟨snil, hNilEval⟩
      unfold RuleProofs.smt_value_rel
      rw [smtx_model_eval_str_concat_term_eq, hxEval]
      change __smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
        SmtValue.Seq snil at hNilEval
      change __smtx_model_eval_eq
        (__smtx_model_eval_str_concat (SmtValue.Seq sx)
          (__smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A))))
        (SmtValue.Seq sx) = SmtValue.Boolean true
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA] at hNilEval ⊢
      case Seq U =>
        rw [__smtx_model_eval.eq_79] at hNilEval ⊢
        simp [__smtx_model_eval_str_concat, native_seq_concat]
        rw [native_unpack_seq, List.append_nil]
        change RuleProofs.smt_seq_rel
          (native_pack_seq (__smtx_elem_typeof_seq_value sx)
            (native_unpack_seq sx)) sx
        exact RuleProofs.smt_seq_rel_symm sx
          (native_pack_seq (__smtx_elem_typeof_seq_value sx)
            (native_unpack_seq sx))
          (smt_seq_rel_pack_unpack (__smtx_elem_typeof_seq_value sx) sx rfl)
      all_goals
        simp [__smtx_model_eval] at hNilEval
  case String s =>
    subst s
    unfold RuleProofs.smt_value_rel
    rw [smtx_model_eval_str_concat_term_eq, hxEval]
    change __smtx_model_eval_eq
      (__smtx_model_eval_str_concat (SmtValue.Seq sx)
        (__smtx_model_eval M (SmtTerm.String (native_string_lit "")))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
    rw [__smtx_model_eval.eq_4]
    simp [native_pack_string,
      __smtx_model_eval_str_concat, native_pack_seq, native_unpack_seq,
      native_seq_concat, native_string_lit, List.append_nil]
    change RuleProofs.smt_seq_rel
      (native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx)) sx
    exact RuleProofs.smt_seq_rel_symm sx
      (native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx))
      (smt_seq_rel_pack_unpack (__smtx_elem_typeof_seq_value sx) sx rfl)

theorem smtx_model_eval_none (M : SmtModel) :
    __smtx_model_eval M SmtTerm.None = SmtValue.NotValue := by
  simp [__smtx_model_eval]

theorem term_ne_stuck_of_seq_eval
    {M : SmtModel} {t : Term} :
    (∃ s, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq s) ->
    t ≠ Term.Stuck := by
  intro hSeq hStuck
  subst t
  rcases hSeq with ⟨s, hEval⟩
  change __smtx_model_eval M SmtTerm.None = SmtValue.Seq s at hEval
  rw [smtx_model_eval_none] at hEval
  cases hEval

theorem strConcat_args_seq_eval_of_concat_seq_eval
    (M : SmtModel) (x y : Term) :
    (∃ sxy,
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy) ->
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ∧
      (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) := by
  intro hSeq
  rcases hSeq with ⟨sxy, hEval⟩
  rw [smtx_model_eval_str_concat_term_eq] at hEval
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    simp [hx, __smtx_model_eval_str_concat] at hEval
  case Seq sx =>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
      simp [hy] at hEval
    case Seq sy =>
      exact ⟨⟨sx, rfl⟩, ⟨sy, rfl⟩⟩

theorem strConcat_concat_seq_eval_of_args_seq_eval
    (M : SmtModel) (x y : Term) :
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ->
    (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) ->
    ∃ sxy,
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy := by
  intro hxSeq hySeq
  rcases hxSeq with ⟨sx, hxEval⟩
  rcases hySeq with ⟨sy, hyEval⟩
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hyEval]
  exact ⟨native_pack_seq (__smtx_elem_typeof_seq_value sx)
    (native_unpack_seq sx ++ native_unpack_seq sy), rfl⟩

theorem smt_value_rel_list_concat_rec_str_concat_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ a z,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      ∀ T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
  | a, z, hList, T, haTy, hzTy =>
      smt_value_rel_list_concat_rec_str_concat M hM a z T hList haTy hzTy

theorem strConcat_args_eval_seq_of_concat_eval_seq
    (M : SmtModel) (x y : Term) :
    (∃ sxy,
      __smtx_model_eval M (__eo_to_smt (Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq sxy) ->
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ∧
      (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) := by
  simpa [mkConcat] using strConcat_args_seq_eval_of_concat_seq_eval M x y

theorem strConcat_eval_concat_seq_of_args_eval_seq
    (M : SmtModel) (x y : Term) :
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ->
    (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) ->
    ∃ sxy,
      __smtx_model_eval M (__eo_to_smt (Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq sxy := by
  simpa [mkConcat] using strConcat_concat_seq_eval_of_args_seq_eval M x y

theorem strConcat_smt_value_rel_congr_eval
    (M : SmtModel) (x x' y y' : Term) (sx' sy' : SmtSeq)
    (hx'Eval :
      __smtx_model_eval M (__eo_to_smt x') = SmtValue.Seq sx')
    (hy'Eval :
      __smtx_model_eval M (__eo_to_smt y') = SmtValue.Seq sy')
    (hxx : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt x')))
    (hyy : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt y'))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x') y'))) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_congr_of_seq_eval M x x' y y'
      sx' sy' hx'Eval hy'Eval hxx hyy

theorem strConcat_smt_value_rel_list_nil_right_empty_eval
    (M : SmtModel) (x nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hxSeq :
      ∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hNilSeq :
      ∃ snil, __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Seq snil) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  simpa [mkConcat] using
    smt_value_rel_str_concat_list_nil_right_empty_eval M x nil
      hNil hxSeq hNilSeq

theorem strConcat_smt_value_rel_list_concat_rec_eval
    (M : SmtModel) (hM : model_wf M) (a z : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) z))) := by
  simpa [mkConcat] using
    smt_value_rel_list_concat_rec_str_concat_eval M hM a z hList T haTy hzTy
