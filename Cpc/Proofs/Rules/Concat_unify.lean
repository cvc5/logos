module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatUnifyNormalize (rev x : Term) : Term :=
  __eo_ite rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
    (__str_nary_intro x)

private abbrev concatUnifyHead (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatUnifyNormalize rev x)
    (Term.Numeral 0)

private abbrev concatUnifyBody (rev s t s1 t1 : Term) : Term :=
  __eo_requires (concatUnifyHead rev s) s1
    (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1))

private abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

private theorem smt_seq_rel_pack_prefix_of_eq_length (T : SmtType) :
    ∀ xs ys xs' ys' : List SmtValue,
      xs.length = ys.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ xs'))
        (native_pack_seq T (ys ++ ys')) ->
      RuleProofs.smt_seq_rel (native_pack_seq T xs)
        (native_pack_seq T ys)
  | [], [], xs', ys', _hLen, _hRel => by
      exact (RuleProofs.smt_seq_rel_iff_eq _ _).2 rfl
  | [], _ :: _, xs', ys', hLen, _hRel => by
      cases hLen
  | _ :: _, [], xs', ys', hLen, _hRel => by
      cases hLen
  | x :: xs, y :: ys, xs', ys', hLen, hRel => by
      have hTailLen : xs.length = ys.length := by
        simpa using Nat.succ.inj hLen
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq] at hRel ⊢
      have hTailRel :=
        smt_seq_rel_pack_prefix_of_eq_length T xs ys xs' ys' hTailLen
          ((RuleProofs.smt_seq_rel_iff_eq _ _).2 hRel.2)
      exact ⟨hRel.1, (RuleProofs.smt_seq_rel_iff_eq _ _).1 hTailRel⟩

private theorem smt_seq_rel_pack_suffix_of_eq_length (T : SmtType) :
    ∀ xs ys sx sy : List SmtValue,
      sx.length = sy.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ sx))
        (native_pack_seq T (ys ++ sy)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T sx)
        (native_pack_seq T sy)
  | [], [], sx, sy, _hLen, hRel => by
      simpa using hRel
  | [], y :: ys, sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T sx ((y :: ys) ++ sy) hRel
      simp at hTotal
      omega
  | x :: xs, [], sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T ((x :: xs) ++ sx) sy hRel
      simp at hTotal
      omega
  | x :: xs, y :: ys, sx, sy, hLen, hRel => by
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq] at hRel
      exact smt_seq_rel_pack_suffix_of_eq_length T xs ys sx sy hLen
        ((RuleProofs.smt_seq_rel_iff_eq _ _).2 hRel.2)

private theorem seq_unpack_length_eq_of_str_len_eq
    (M : SmtModel) (hM : model_wf M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true) :
    ∃ sx sy : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hLenRel := RuleProofs.eo_interprets_eq_rel M (mkStrLen x)
    (mkStrLen y) hLen
  have hLenEq :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    have hxLenTranslate :
        __eo_to_smt (mkStrLen x) = SmtTerm.str_len (__eo_to_smt x) := by
      rfl
    have hyLenTranslate :
        __eo_to_smt (mkStrLen y) = SmtTerm.str_len (__eo_to_smt y) := by
      rfl
    rw [hxLenTranslate, hyLenTranslate] at hLenRel
    rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq] at hLenRel
    unfold RuleProofs.smt_value_rel at hLenRel
    simp [hxEval, hyEval, __smtx_model_eval_str_len, __smtx_model_eval_eq,
      native_seq_len] at hLenRel
    unfold native_veq at hLenRel
    simp at hLenRel
    exact_mod_cast hLenRel
  exact ⟨sx, sy, hxEval, hyEval, hLenEq⟩

private theorem smt_value_rel_str_concat_heads_of_len_eq
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxEval, hxsEval, hyEval, hysEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxs)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxs))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  have hHeadPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) (native_unpack_seq sxs)
      (native_unpack_seq sys) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

private theorem smt_value_rel_str_concat_tails_of_len_eq
    (M : SmtModel) (hM : model_wf M) (xs x ys y : Term)
    (T : SmtType)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat xs x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hsxsTy : __smtx_typeof_seq_value sxs = SmtType.Seq T := by
    simpa [hxsEval, __smtx_typeof_value] using hxsValTy
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsysTy : __smtx_typeof_seq_value sys = SmtType.Seq T := by
    simpa [hysEval, __smtx_typeof_value] using hysValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxsElem : __smtx_elem_typeof_seq_value sxs = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxsTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsysElem : __smtx_elem_typeof_seq_value sys = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsysTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxsEval, hxEval, hysEval, hyEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sxs)
      (native_unpack_seq sxs ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sys)
      (native_unpack_seq sys ++ native_unpack_seq sy))) =
      SmtValue.Boolean true at hRel
  rw [hsxsElem, hsysElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sxs ++ native_unpack_seq sx))
    (native_pack_seq T (native_unpack_seq sys ++ native_unpack_seq sy)) at hRel
  have hTailPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_suffix_of_eq_length T (native_unpack_seq sxs)
      (native_unpack_seq sys) (native_unpack_seq sx)
      (native_unpack_seq sy) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx hsxElem)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hTailPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy hsyElem)))

private theorem eo_interprets_str_concat_heads_of_len_eq_of_seq
    (M : SmtModel) (hM : model_wf M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true)
    (hEq : eo_interprets M (mkEq (mkConcat x xs) (mkConcat y ys)) true) :
    eo_interprets M (mkEq x y) true := by
  rcases seq_unpack_length_eq_of_str_len_eq M hM x y T hxTy hyTy hLen with
    ⟨sx0, sy0, hxEval0, hyEval0, hLen0⟩
  have hLenEval :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    intro sx sy hxEval hyEval
    rw [hxEval] at hxEval0
    injection hxEval0 with hsx
    rw [hyEval] at hyEval0
    injection hyEval0 with hsy
    subst sx0
    subst sy0
    exact hLen0
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat x xs) (mkConcat y ys) hEq
  have hXYRel :=
    smt_value_rel_str_concat_heads_of_len_eq M hM x xs y ys T hxTy
      hxsTy hyTy hysTy hLenEval hRel
  have hXYBool : RuleProofs.eo_has_bool_type (mkEq x y) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hxTy, hyTy]
    · rw [hxTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M x y hXYBool hXYRel

private theorem eo_interprets_str_concat_tails_of_len_eq_of_seq
    (M : SmtModel) (hM : model_wf M) (xs x ys y : Term)
    (T : SmtType)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true)
    (hEq : eo_interprets M (mkEq (mkConcat xs x) (mkConcat ys y)) true) :
    eo_interprets M (mkEq x y) true := by
  rcases seq_unpack_length_eq_of_str_len_eq M hM x y T hxTy hyTy hLen with
    ⟨sx0, sy0, hxEval0, hyEval0, hLen0⟩
  have hLenEval :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    intro sx sy hxEval hyEval
    rw [hxEval] at hxEval0
    injection hxEval0 with hsx
    rw [hyEval] at hyEval0
    injection hyEval0 with hsy
    subst sx0
    subst sy0
    exact hLen0
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat xs x) (mkConcat ys y) hEq
  have hXYRel :=
    smt_value_rel_str_concat_tails_of_len_eq M hM xs x ys y T hxsTy
      hxTy hysTy hyTy hLenEval hRel
  have hXYBool : RuleProofs.eo_has_bool_type (mkEq x y) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hxTy, hyTy]
    · rw [hxTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M x y hXYBool hXYRel

private theorem list_nth_zero_eq_cons_of_ne_stuck (f a x : Term)
    (hNthEq : __eo_list_nth f a (Term.Numeral 0) = x)
    (hNthNe : __eo_list_nth f a (Term.Numeral 0) ≠ Term.Stuck) :
    ∃ tail,
      a = Term.Apply (Term.Apply f x) tail ∧
        __eo_is_list f tail = Term.Boolean true := by
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) ≠ Term.Stuck := by
    simpa [__eo_list_nth] using hNthNe
  have hList : __eo_is_list f a = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecNe : __eo_list_nth_rec a (Term.Numeral 0) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) =
        __eo_list_nth_rec a (Term.Numeral 0) :=
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecEq : __eo_list_nth_rec a (Term.Numeral 0) = x := by
    rw [__eo_list_nth] at hNthEq
    rw [hReqEq] at hNthEq
    exact hNthEq
  cases a with
  | Stuck =>
      simp [__eo_list_nth_rec] at hRecNe
  | Apply g tail =>
      cases g with
      | Apply f' head =>
          have hHead : head = x := by
            simpa [__eo_list_nth_rec] using hRecEq
          have hFEq : f' = f :=
            eo_is_list_cons_head_eq_of_true f f' head tail hList
          subst head
          subst f'
          exact ⟨tail, rfl,
            eo_is_list_tail_true_of_cons_self f x tail hList⟩
      | _ =>
          simp [__eo_list_nth_rec] at hRecNe
  | _ =>
      simp [__eo_list_nth_rec] at hRecNe

private theorem eo_prog_concat_unify_eq_of_ne_stuck
    (rev s t s1 t1 : Term)
    (hProg :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck) :
    __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
        (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) =
      mkEq s1 t1 ∧
      concatUnifyHead rev s = s1 ∧ concatUnifyHead rev t = t1 := by
  have hProgBody :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) =
        concatUnifyBody rev s t s1 t1 := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals
      simp [__eo_prog_concat_unify, concatUnifyBody, concatUnifyHead,
        concatUnifyNormalize, mkEq]
  have hBodyNe : concatUnifyBody rev s t s1 t1 ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadS :
      concatUnifyHead rev s = s1 :=
    eo_requires_eq_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hInnerNe :
      __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) ≠
        Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hHeadT :
      concatUnifyHead rev t = t1 :=
    eo_requires_eq_of_ne_stuck (concatUnifyHead rev t) t1
      (mkEq s1 t1) hInnerNe
  have hOuterEq :
      concatUnifyBody rev s t s1 t1 =
        __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) :=
    eo_requires_eq_result_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hInnerEq :
      __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) =
        mkEq s1 t1 :=
    eo_requires_eq_result_of_ne_stuck (concatUnifyHead rev t) t1
      (mkEq s1 t1) hInnerNe
  exact ⟨by rw [hProgBody, hOuterEq, hInnerEq], hHeadS, hHeadT⟩

private theorem len_eq_seq_types_of_bool (x y : Term)
    (hLenBool : RuleProofs.eo_has_bool_type (mkEq (mkStrLen x) (mkStrLen y))) :
    ∃ T U,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq U := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen x) (mkStrLen y) hLenBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkStrLen y)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hLeftTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using hLeftNN
  have hRightTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using hRightNN
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt x)) hLeftTerm with
    ⟨T, hxTy⟩
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt y)) hRightTerm with
    ⟨U, hyTyU⟩
  exact ⟨T, U, hxTy, hyTyU⟩

private theorem str_nary_intro_cons_seq_types_of_head_seq
    (x head tail : Term) (T : SmtType)
    (hIntroEq : __str_nary_intro x = mkConcat head tail)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
  have hIntroNe : __str_nary_intro x ≠ Term.Stuck := by
    rw [hIntroEq]
    simp [mkConcat]
  by_cases hConcat : ∃ h tl : Term, x = mkConcat h tl
  · rcases hConcat with ⟨h, tl, rfl⟩
    rcases str_concat_args_of_non_none h tl hxNN with ⟨U, hhTy, htlTy⟩
    have hxTyU :
        __smtx_typeof (__eo_to_smt (mkConcat h tl)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq h tl U hhTy htlTy
    have hIntroNN :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) ≠
          SmtType.None :=
      str_nary_intro_concat_has_smt_translation h tl hxNN
    have hIntroTyU :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) =
          SmtType.Seq U :=
      smt_typeof_str_nary_intro_of_seq (mkConcat h tl) U hxTyU hIntroNN
    have hResultTyU :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
          SmtType.Seq U := by
      simpa [hIntroEq] using hIntroTyU
    rcases str_concat_args_of_seq_type head tail U hResultTyU with
      ⟨hHeadTyU, hTailTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hHeadTyU, hHeadTy]
      injection hSeq
    exact ⟨by simpa [hUT] using hxTyU, by simpa [hUT] using hTailTyU⟩
  · rcases str_nary_intro_not_str_concat_cases_typeof_empty x hConcat hIntroNe with
      hIntroSelf | ⟨hIntroCons, _hEmptyNil⟩
    · rw [hIntroSelf] at hIntroEq
      exact False.elim (hConcat ⟨head, tail, hIntroEq⟩)
    · rw [hIntroCons] at hIntroEq
      injection hIntroEq with hFun hTailEq
      injection hFun with _ hHeadEq
      subst head
      subst tail
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := hHeadTy
      rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T
          hxTy with
        ⟨hTInh, hTWf⟩
      have hEmptyNN :
          __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
            SmtType.None :=
        seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
          hTInh hTWf
      exact ⟨hxTy,
        by
          simpa using smt_typeof_seq_empty_typeof x T hxTy hEmptyNN⟩

private theorem eo_is_list_nil_str_concat_of_list_true_not_concat
    (x : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
      Term.Boolean true := by
  cases x with
  | Stuck =>
      simp [__eo_is_list] at hList
  | Apply f a =>
      cases f with
      | Apply g b =>
          by_cases hg : g = Term.UOp UserOp.str_concat
          · subst g
            exact False.elim (hNotConcat ⟨b, a, rfl⟩)
          · simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
              __eo_requires, native_ite, SmtEval.native_not, native_teq] at hList
            exact False.elim (hg hList.1.symm)
      | _ =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
            __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
            native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList
  | String s =>
      simpa [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] using hList
  | UOp1 op A =>
      cases op <;>
        simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
          __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
          native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢
  | _ =>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_ok,
        __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_requires,
        native_ite, SmtEval.native_not, native_teq, __eo_eq] at hList ⊢

private theorem str_nary_intro_rev_cons_seq_types_of_head_seq
    (x head tail : Term) (T : SmtType)
    (hRevIntroEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        mkConcat head tail)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
  have hRevIntroNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck := by
    rw [hRevIntroEq]
    simp [mkConcat]
  have hIntroNe : __str_nary_intro x ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntroNe
  by_cases hConcat : ∃ h tl : Term, x = mkConcat h tl
  · rcases hConcat with ⟨h, tl, rfl⟩
    rcases str_concat_args_of_non_none h tl hxNN with ⟨U, hhTy, htlTy⟩
    have hxTyU :
        __smtx_typeof (__eo_to_smt (mkConcat h tl)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq h tl U hhTy htlTy
    have hIntroNN :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) ≠
          SmtType.None :=
      str_nary_intro_concat_has_smt_translation h tl hxNN
    have hIntroTyU :
        __smtx_typeof
            (__eo_to_smt (__str_nary_intro (mkConcat h tl))) =
          SmtType.Seq U :=
      smt_typeof_str_nary_intro_of_seq (mkConcat h tl) U hxTyU hIntroNN
    have hIntroList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_nary_intro (mkConcat h tl)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__str_nary_intro (mkConcat h tl)) hRevIntroNe
    have hRevIntroTyU :
        __smtx_typeof
            (__eo_to_smt
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat h tl)))) =
          SmtType.Seq U :=
      smt_typeof_list_rev_str_concat_of_seq
        (__str_nary_intro (mkConcat h tl)) U hIntroList hIntroTyU
        hRevIntroNe
    have hResultTyU :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
          SmtType.Seq U := by
      simpa [hRevIntroEq] using hRevIntroTyU
    rcases str_concat_args_of_seq_type head tail U hResultTyU with
      ⟨hHeadTyU, hTailTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hHeadTyU, hHeadTy]
      injection hSeq
    exact ⟨by simpa [hUT] using hxTyU, by simpa [hUT] using hTailTyU⟩
  · rcases str_nary_intro_not_str_concat_cases_typeof_empty x hConcat hIntroNe with
      hIntroSelf | ⟨hIntroCons, _hEmptyNil⟩
    · have hRevEq :
          __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
            __str_nary_intro x :=
        eo_list_rev_str_nary_intro_eq_of_not_str_concat x hConcat
          hIntroNe hRevIntroNe
      rw [hRevEq, hIntroSelf] at hRevIntroEq
      exact False.elim (hConcat ⟨head, tail, hRevIntroEq⟩)
    · have hRevEq :
          __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
            __str_nary_intro x :=
        eo_list_rev_str_nary_intro_eq_of_not_str_concat x hConcat
          hIntroNe hRevIntroNe
      rw [hRevEq, hIntroCons] at hRevIntroEq
      injection hRevIntroEq with hFun hTailEq
      injection hFun with _ hHeadEq
      subst head
      subst tail
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := hHeadTy
      rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T
          hxTy with
        ⟨hTInh, hTWf⟩
      have hEmptyNN :
          __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
            SmtType.None :=
        seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
          hTInh hTWf
      exact ⟨hxTy,
        by
          simpa using smt_typeof_seq_empty_typeof x T hxTy hEmptyNN⟩

private theorem eo_interprets_concat_unify_false
    (M : SmtModel) (hM : model_wf M)
    (s t s1 t1 : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen s1) (mkStrLen t1)))
    (hFinalBool : RuleProofs.eo_has_bool_type (mkEq s1 t1))
    (hProg :
      __eo_prog_concat_unify (Term.Boolean false) (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck)
    (hST : eo_interprets M (mkEq s t) true)
    (hLen : eo_interprets M (mkEq (mkStrLen s1) (mkStrLen t1)) true) :
    eo_interprets M (mkEq s1 t1) true := by
  rcases eo_prog_concat_unify_eq_of_ne_stuck
      (Term.Boolean false) s t s1 t1 hProg with
    ⟨_, hHeadS, hHeadT⟩
  rcases len_eq_seq_types_of_bool s1 t1 hLenBool with
    ⟨T, _U, hs1Ty, _ht1TyU⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s1 t1 hFinalBool with
    ⟨hS1T1Same, hS1NN⟩
  have ht1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T := by
    rw [← hS1T1Same, hs1Ty]
  have hs1Ne : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1NN
  have hT1NN :
      __smtx_typeof (__eo_to_smt t1) ≠ SmtType.None := by
    rw [ht1Ty]
    exact seq_ne_none T
  have ht1Ne : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1NN
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = s1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_false] using hHeadS
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = t1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_false] using hHeadT
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hs1Ne
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact ht1Ne
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) s1
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) t1
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s t hPremBool with
    ⟨hSTSameTy, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSTSameTy]
    exact hSNN
  have hIntroSEq : __str_nary_intro s = mkConcat s1 sTail := hIntroS
  have hIntroTEq : __str_nary_intro t = mkConcat t1 tTail := hIntroT
  rcases str_nary_intro_cons_seq_types_of_head_seq s s1 sTail T
      hIntroSEq hs1Ty hSNN with
    ⟨hsTy, hsTailTy⟩
  rcases str_nary_intro_cons_seq_types_of_head_seq t t1 tTail T
      hIntroTEq ht1Ty hTNN with
    ⟨htTy, htTailTy⟩
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroSEq]
    simp [mkConcat]
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck := by
    rw [hIntroTEq]
    simp [mkConcat]
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T := by
    rw [hIntroSEq]
    exact smt_typeof_str_concat_of_seq s1 sTail T hs1Ty hsTailTy
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T := by
    rw [hIntroTEq]
    exact smt_typeof_str_concat_of_seq t1 tTail T ht1Ty htTailTy
  have hIntroBool :
      RuleProofs.eo_has_bool_type
        (mkEq (__str_nary_intro s) (__str_nary_intro t)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroSTy, hIntroTTy]
    · rw [hIntroSTy]
      exact seq_ne_none T
  have hIntroEq :
      eo_interprets M (mkEq (__str_nary_intro s) (__str_nary_intro t)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM s t T hsTy htTy
      hIntroSNe hIntroTNe hST hIntroBool
  have hConcatEq :
      eo_interprets M (mkEq (mkConcat s1 sTail) (mkConcat t1 tTail)) true := by
    simpa [hIntroSEq, hIntroTEq] using hIntroEq
  exact eo_interprets_str_concat_heads_of_len_eq_of_seq M hM
    s1 sTail t1 tTail T hs1Ty hsTailTy ht1Ty htTailTy hLen hConcatEq

private theorem final_eq_bool_of_len_bool_and_eo_typeof_bool
    (s1 t1 : Term)
    (hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen s1) (mkStrLen t1)))
    (hResultTy : __eo_typeof (mkEq s1 t1) = Term.Bool) :
    RuleProofs.eo_has_bool_type (mkEq s1 t1) := by
  rcases len_eq_seq_types_of_bool s1 t1 hLenBool with
    ⟨T, U, hs1Ty, ht1TyU⟩
  rcases eo_typeof_eq_operands_same_of_bool s1 t1 hResultTy with
    ⟨hEoSame, hS1EoNN, hT1EoNN⟩
  have hS1Match :=
    TranslationProofs.eo_to_smt_typeof_matches_translation s1
      (by rw [hs1Ty]; exact seq_ne_none T)
  have hT1Match :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t1
      (by rw [ht1TyU]; exact seq_ne_none U)
  have hSeqSame : SmtType.Seq T = SmtType.Seq U := by
    rw [← hs1Ty, ← ht1TyU]
    rw [hS1Match, hT1Match, hEoSame]
  have hUT : U = T := by
    injection hSeqSame.symm
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hs1Ty, ht1TyU, hUT]
  · rw [hs1Ty]
    exact seq_ne_none T

private theorem eo_prog_concat_unify_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_unify rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ s t s1 t1,
      x1 = mkEq s t ∧ x2 = mkEq (mkStrLen s1) (mkStrLen t1) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 s =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply lhs2 rhs2 =>
                      cases lhs2 with
                      | Apply op2 lhsLen =>
                          cases op2 with
                          | UOp u2 =>
                              cases u2 with
                              | eq =>
                                  cases lhsLen with
                                  | Apply lenOp s1 =>
                                      cases lenOp with
                                      | UOp lenU1 =>
                                          cases lenU1 with
                                          | str_len =>
                                              cases rhs2 with
                                              | Apply lenOp2 t1 =>
                                                  cases lenOp2 with
                                                  | UOp lenU2 =>
                                                      cases lenU2 with
                                                      | str_len =>
                                                          exact
                                                            ⟨s, rhs1, s1, t1,
                                                              rfl, rfl⟩
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_unify]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_unify]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_unify]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_unify]
                                                  at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_unify] at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_unify] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_unify] at hProg
                          | _ =>
                              cases rev <;>
                                simp [__eo_prog_concat_unify] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_unify] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_unify] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_unify] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_unify] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_unify] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_unify] at hProg

private theorem eo_list_nth_arg_ne_stuck_of_ne_stuck
    (f a i : Term)
    (hNth : __eo_list_nth f a i ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a i) ≠ Term.Stuck := by
    simpa [__eo_list_nth] using hNth
  have hIsNe : __eo_is_list f a ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a i) hReq
  intro hA
  subst a
  cases f <;> simp [__eo_is_list] at hIsNe

private theorem concatUnifyNormalize_ne_stuck_of_head_ne_stuck
    (rev x : Term)
    (hHead : concatUnifyHead rev x ≠ Term.Stuck) :
    concatUnifyNormalize rev x ≠ Term.Stuck := by
  exact eo_list_nth_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_concat) (concatUnifyNormalize rev x)
    (Term.Numeral 0) hHead

private theorem concatUnify_rev_cases_of_prog_ne_stuck
    (rev s t s1 t1 : Term)
    (hProg :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck)
    (hs1Ne : s1 ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_unify_eq_of_ne_stuck rev s t s1 t1 hProg with
    ⟨_, hHeadS, _⟩
  have hHeadNe : concatUnifyHead rev s ≠ Term.Stuck := by
    rw [hHeadS]
    exact hs1Ne
  have hNormNe : concatUnifyNormalize rev s ≠ Term.Stuck :=
    concatUnifyNormalize_ne_stuck_of_head_ne_stuck rev s hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (__str_nary_intro s) ≠ Term.Stuck := by
    simpa [concatUnifyNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
    (__str_nary_intro s) hIteNe

private theorem eo_interprets_rev_cons_snoc_of_list_nil_raw
    (M : SmtModel) (hM : model_wf M) (head nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat nil head)) true := by
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hElimCons :
      __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy (eo_is_list_str_concat_nil_true_of_nil_true nil hNil)
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil))
  let rhs := mkConcat nil head
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Seq T := by
    subst lhs
    rw [hRevConsEq]
    exact smt_typeof_str_nary_elim_of_seq_ne_stuck
      (mkConcat head nil) T hConsTy hElimCons
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    subst rhs
    exact smt_typeof_str_concat_of_seq nil head T hNilTy hHeadTy
  have hBool : RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLhsTy, hRhsTy]
    · rw [hLhsTy]
      exact seq_ne_none T
  have hLhsToCons :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    subst lhs
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T
      hConsTy hElimCons
  have hConsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
        (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T hHeadTy
      hNil hNilTy
  have hRhsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) := by
    subst rhs
    exact smt_value_rel_str_concat_list_nil_left_empty M hM nil head T
      hNil hNilTy hHeadTy
  have hLhsToHead :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt head)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lhs))
        (__smtx_model_eval M (__eo_to_smt rhs)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt rhs)) hLhsToHead
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) hRhsToHead)
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool hRel

private theorem eo_interprets_rev_cons_snoc_prefix_of_seq
    (M : SmtModel) (hM : model_wf M) (head tail : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck) :
    ∃ pref,
      __smtx_typeof (__eo_to_smt pref) = SmtType.Seq T ∧
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)))
            (mkConcat pref head)) true := by
  by_cases hTailConcat : ∃ a aTail : Term, tail = mkConcat a aTail
  · rcases hTailConcat with ⟨a, aTail, rfl⟩
    have hRevTail :
        __eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat a aTail) ≠ Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        (mkConcat a aTail) hTailList
    have hElimTail :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat a aTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq a aTail T
        hTailTy hRevTail
    let pref :=
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat a aTail))
    have hPrefixTy :
        __smtx_typeof (__eo_to_smt pref) = SmtType.Seq T := by
      subst pref
      exact smt_typeof_str_nary_elim_list_rev_of_seq (mkConcat a aTail)
        T hTailList hTailTy hRevTail hElimTail
    have hSnoc :
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head (mkConcat a aTail))))
            (mkConcat pref head)) true := by
      subst pref
      exact eo_interprets_rev_cons_snoc_of_seq M hM head (mkConcat a aTail)
        T hHeadTy hTailList hTailTy hRevCons hRevTail hElimCons
        hElimTail
    exact ⟨pref, hPrefixTy, hSnoc⟩
  · have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) tail =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_of_list_true_not_concat tail hTailList
        hTailConcat
    exact ⟨tail, hTailTy,
      eo_interprets_rev_cons_snoc_of_list_nil_raw M hM head tail T
        hHeadTy hNil hTailTy hRevCons⟩

private theorem eo_interprets_concat_unify_true
    (M : SmtModel) (hM : model_wf M)
    (s t s1 t1 : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen s1) (mkStrLen t1)))
    (hFinalBool : RuleProofs.eo_has_bool_type (mkEq s1 t1))
    (hProg :
      __eo_prog_concat_unify (Term.Boolean true) (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck)
    (hST : eo_interprets M (mkEq s t) true)
    (hLen : eo_interprets M (mkEq (mkStrLen s1) (mkStrLen t1)) true) :
    eo_interprets M (mkEq s1 t1) true := by
  rcases eo_prog_concat_unify_eq_of_ne_stuck
      (Term.Boolean true) s t s1 t1 hProg with
    ⟨_, hHeadS, hHeadT⟩
  rcases len_eq_seq_types_of_bool s1 t1 hLenBool with
    ⟨T, _U, hs1Ty, _ht1TyU⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s1 t1 hFinalBool with
    ⟨hS1T1Same, hS1NN⟩
  have ht1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T := by
    rw [← hS1T1Same, hs1Ty]
  have hs1Ne : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1NN
  have hT1NN :
      __smtx_typeof (__eo_to_smt t1) ≠ SmtType.None := by
    rw [ht1Ty]
    exact seq_ne_none T
  have ht1Ne : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1NN
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = s1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_true] using hHeadS
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = t1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_true] using hHeadT
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hs1Ne
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact ht1Ne
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      s1 hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, hSTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      t1 hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, hTTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s t hPremBool with
    ⟨hSTSameTy, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSTSameTy]
    exact hSNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq s s1 sTail T
      hRevIntroS hs1Ty hSNN with
    ⟨hsTy, hsTailTy⟩
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t t1 tTail T
      hRevIntroT ht1Ty hTNN with
    ⟨htTy, htTailTy⟩
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hRevIntroTNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck := by
    rw [hRevIntroT]
    simp
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntroTNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T
      hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf t T htTy hTInh hTWf
      hIntroTNe
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroSNe
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroTNe
  have hDoubleS :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroSNe hRevIntroSNe
  have hDoubleT :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroTNe hRevIntroTNe
  have hDoubleEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))) true :=
    eo_interprets_double_rev_intros_of_elim_intros M hM s t T hsTy htTy
      hIntroSNN hIntroTNN hIntroSNe hIntroTNe hElimIntroS
      hElimIntroT hDoubleS hDoubleT hST
  have hRevConcatEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat s1 sTail)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat t1 tTail)))) true := by
    simpa [hRevIntroS, hRevIntroT] using hDoubleEq
  have hConsSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat s1 sTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      s1 sTail (by decide) hSTailList
  have hConsTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat t1 tTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      t1 tTail (by decide) hTTailList
  have hConsSTy :
      __smtx_typeof (__eo_to_smt (mkConcat s1 sTail)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq s1 sTail T hs1Ty hsTailTy
  have hConsTTy :
      __smtx_typeof (__eo_to_smt (mkConcat t1 tTail)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 tTail T ht1Ty htTailTy
  have hRevConsS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat s1 sTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat s1 sTail) hConsSList
  have hRevConsT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t1 tTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat t1 tTail) hConsTList
  have hElimConsS :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat s1 sTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq s1 sTail T
      hConsSTy hRevConsS
  have hElimConsT :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat t1 tTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq t1 tTail T
      hConsTTy hRevConsT
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM s1 sTail T
      hs1Ty hSTailList hsTailTy hRevConsS hElimConsS with
    ⟨sPrefix, hsPrefixTy, hSnocS⟩
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM t1 tTail T
      ht1Ty hTTailList htTailTy hRevConsT hElimConsT with
    ⟨tPrefix, htPrefixTy, hSnocT⟩
  have hSnocSSymm :
      eo_interprets M
        (mkEq (mkConcat sPrefix s1)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat s1 sTail)))) true :=
    eo_interprets_eq_symm_local M
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat s1 sTail)))
      (mkConcat sPrefix s1) hSnocS
  have hLeftToRight :
      eo_interprets M
        (mkEq (mkConcat sPrefix s1)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat t1 tTail)))) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat sPrefix s1)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat s1 sTail)))
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t1 tTail)))
      hSnocSSymm hRevConcatEq
  have hSnocEq :
      eo_interprets M
        (mkEq (mkConcat sPrefix s1) (mkConcat tPrefix t1)) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat sPrefix s1)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t1 tTail)))
      (mkConcat tPrefix t1) hLeftToRight hSnocT
  exact eo_interprets_str_concat_tails_of_len_eq_of_seq M hM
    sPrefix s1 tPrefix t1 T hsPrefixTy hs1Ty htPrefixTy ht1Ty hLen
    hSnocEq

private theorem step_concat_unify_core
    (M : SmtModel) (hM : model_wf M)
    (rev s t s1 t1 : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen s1) (mkStrLen t1)))
    (hProg :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_unify rev (Proof.pf (mkEq s t))
            (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1)))) =
        Term.Bool) :
    StepRuleProperties M [mkEq s t, mkEq (mkStrLen s1) (mkStrLen t1)]
      (__eo_prog_concat_unify rev (Proof.pf (mkEq s t))
        (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1)))) := by
  rcases eo_prog_concat_unify_eq_of_ne_stuck rev s t s1 t1 hProg with
    ⟨hProgEq, _, _⟩
  have hFinalTy : __eo_typeof (mkEq s1 t1) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hFinalBool : RuleProofs.eo_has_bool_type (mkEq s1 t1) :=
    final_eq_bool_of_len_bool_and_eo_typeof_bool s1 t1 hLenBool hFinalTy
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s1 t1 hFinalBool with
    ⟨_hS1T1, hS1NN⟩
  have hs1Ne : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1NN
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hST : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    have hLen :
        eo_interprets M (mkEq (mkStrLen s1) (mkStrLen t1)) true :=
      hPremisesTrue (mkEq (mkStrLen s1) (mkStrLen t1)) (by simp)
    rcases concatUnify_rev_cases_of_prog_ne_stuck rev s t s1 t1 hProg
        hs1Ne with hRev | hRev
    · subst rev
      rw [hProgEq]
      exact eo_interprets_concat_unify_true M hM s t s1 t1 hPremBool
        hLenBool hFinalBool hProg hST hLen
    · subst rev
      rw [hProgEq]
      exact eo_interprets_concat_unify_false M hM s t s1 t1 hPremBool
        hLenBool hFinalBool hProg hST hLen
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq s1 t1) hFinalBool

public theorem cmd_step_concat_unify_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_unify args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_unify args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_unify args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_unify args premises ≠
      Term.Stuck :=
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        have hArgs : RuleProofs.eo_has_smt_translation a1 ∧
                            True := by
                          simpa [cmdTranslationOk, cArgListTranslationOk]
                            using hCmdTrans
                        exact hArgs.1
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_unify a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_unify a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_unify_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, lhs1, rhs1, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkEq (mkStrLen lhs1) (mkStrLen rhs1) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hLenEqBool :
                          RuleProofs.eo_has_bool_type
                            (mkEq (mkStrLen lhs1) (mkStrLen rhs1)) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_unify a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkEq (mkStrLen lhs1) (mkStrLen rhs1))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_unify a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkEq (mkStrLen lhs1) (mkStrLen rhs1)))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_unify a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_unify a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_unify_core M hM a1 lhs rhs lhs1 rhs1
                        hA1Trans hPremEqBool hLenEqBool hProgRule
                        hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
