module

public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport
public import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
import all Cpc.Proofs.RuleSupport.StrReplaceAllSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem seq_eval_op_shape {t u : Term}
    (h :
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠
        Term.Stuck) :
    __seq_eval t = u ∧
      __eo_prog_seq_eval_op (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u := by
  change __eo_requires (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) ≠ Term.Stuck at h
  exact ⟨eo_requires_eq_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h,
    eo_requires_eq_result_of_ne_stuck (__seq_eval t) u
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) h⟩

private theorem term_ne_stuck_of_eo_is_list_true (f x : Term)
    (h : __eo_is_list f x = Term.Boolean true) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_is_list] at h

private theorem eo_list_concat_str_concat_lists_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hA := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hZ := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  exact ⟨hA, hZ⟩

private theorem eo_list_concat_str_concat_eq_rec_of_ne_stuck (a z : Term)
    (h : __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠
    Term.Stuck at h
  have hOuter := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) h
  have hInner := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hOuter, hInner]

private theorem str_value_len_numeral_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    ∃ n : native_Int, __str_value_len x = Term.Numeral n := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__str_value_len] at h
  by_cases hUnit : ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    exact ⟨1, by simp [__str_value_len]⟩
  have hNotUnit : ∀ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
    intro e he
    exact hUnit ⟨e, he⟩
  have hValue :
      __str_value_len x =
        __eo_ite (__eo_is_str x) (__eo_len x)
          (__eo_requires (__is_seq_const x) (Term.Boolean true)
            (__eo_list_len (Term.UOp UserOp.str_concat) x)) := by
    rw [__str_value_len.eq_3 x hx hNotUnit]
  obtain ⟨isStr, hStr⟩ := RuleProofs.eo_is_str_boolean_of_ne_stuck x hx
  cases isStr
  · have hReqNe :
        __eo_requires (__is_seq_const x) (Term.Boolean true)
          (__eo_list_len (Term.UOp UserOp.str_concat) x) ≠ Term.Stuck := by
      rw [hValue] at h
      simpa [hStr, eo_ite_false] using h
    have hReq :=
      eo_requires_eq_result_of_ne_stuck (__is_seq_const x) (Term.Boolean true)
        (__eo_list_len (Term.UOp UserOp.str_concat) x) hReqNe
    have hListNe :
        __eo_list_len (Term.UOp UserOp.str_concat) x ≠ Term.Stuck :=
      eo_requires_result_ne_stuck_of_ne_stuck (__is_seq_const x)
        (Term.Boolean true) (__eo_list_len (Term.UOp UserOp.str_concat) x)
        hReqNe
    rcases RuleProofs.eo_list_len_stuck_or_numeral
        (Term.UOp UserOp.str_concat) x with hList | ⟨n, hList⟩
    · exact False.elim (hListNe hList)
    · refine ⟨n, ?_⟩
      rw [hValue]
      simpa [hStr, eo_ite_false, hList] using hReq
  · obtain ⟨w, hxString⟩ := RuleProofs.eo_is_str_true_cases x hStr
    subst x
    exact ⟨Int.ofNat w.length, RuleProofs.str_value_len_string w⟩

private theorem str_value_len_numeral_of_is_seq_const_true (x : Term)
    (hSeq : __is_seq_const x = Term.Boolean true) :
    ∃ n : native_Int, __str_value_len x = Term.Numeral n := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__is_seq_const] at hSeq
  by_cases hUnit : ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    exact ⟨1, by simp [__str_value_len]⟩
  have hNotUnit : ∀ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
    intro e he
    exact hUnit ⟨e, he⟩
  have hRec : __is_seq_const_rec x = Term.Boolean true := by
    rw [__is_seq_const.eq_3 x hx hNotUnit] at hSeq
    exact hSeq
  exact RuleProofs.str_value_len_numeral_of_seq_const_rec_true x hRec

private theorem str_value_len_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_value_len] at h

private theorem smt_typeof_str_value_len_of_ne_stuck (x : Term)
    (h : __str_value_len x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_value_len x)) = SmtType.Int := by
  rcases str_value_len_numeral_of_ne_stuck x h with ⟨n, hLen⟩
  rw [hLen]
  change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
  rw [__smtx_typeof.eq_2]

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_wf M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem int_arg_numeral_of_eo_is_neg_bool (n : Term)
    (b : native_Bool)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hNeg : __eo_is_neg n = Term.Boolean b) :
    ∃ i, n = Term.Numeral i ∧ native_zlt i 0 = b := by
  cases n <;> simp [__eo_is_neg] at hNeg
  case Numeral i =>
    exact ⟨i, rfl, by simpa using hNeg⟩
  case Rational r =>
    change __smtx_typeof (SmtTerm.Rational r) = SmtType.Int at hnTy
    rw [__smtx_typeof.eq_3] at hnTy
    cases hnTy

private theorem int_args_numerals_of_eo_gt_bool (n m : Term)
    (b : native_Bool)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int)
    (hGt : __eo_gt n m = Term.Boolean b) :
    ∃ i j, n = Term.Numeral i ∧ m = Term.Numeral j ∧
      native_zlt j i = b := by
  cases n <;> cases m <;> simp [__eo_gt] at hGt
  case Numeral.Numeral i j =>
    exact ⟨i, j, rfl, rfl, by simpa using hGt⟩
  case Rational.Rational r q =>
    change __smtx_typeof (SmtTerm.Rational r) = SmtType.Int at hnTy
    rw [__smtx_typeof.eq_3] at hnTy
    cases hnTy
  case Binary.Binary w1 n1 w2 n2 =>
    change __smtx_typeof (SmtTerm.Binary w1 n1) = SmtType.Int at hnTy
    by_cases hg :
        native_and (native_zleq 0 w1)
            (native_zeq n1 (native_mod_total n1 (native_int_pow2 w1))) =
          true
    · simp [__smtx_typeof, native_ite, hg] at hnTy
    · simp [__smtx_typeof, native_ite, hg] at hnTy

private theorem eo_gt_right_ne_stuck_of_bool (n m : Term)
    (b : native_Bool)
    (hGt : __eo_gt n m = Term.Boolean b) :
    m ≠ Term.Stuck := by
  intro hm
  subst m
  cases n <;> simp [__eo_gt] at hGt

private theorem smt_value_rel_seq_unpack_eq
    {sx sy : SmtSeq}
    (hRel : RuleProofs.smt_value_rel (SmtValue.Seq sx) (SmtValue.Seq sy)) :
    native_unpack_seq sx = native_unpack_seq sy := by
  have hSeq : RuleProofs.smt_seq_rel sx sy := hRel
  exact congrArg native_unpack_seq
    ((RuleProofs.smt_seq_rel_iff_eq sx sy).1 hSeq)

private theorem smt_value_rel_seq_pack_of_unpack_eq
    (s base : SmtSeq) (xs : List SmtValue) (T : SmtType)
    (hsTy : __smtx_typeof_seq_value s = SmtType.Seq T)
    (hbaseTy : __smtx_typeof_seq_value base = SmtType.Seq T)
    (hUnpack : native_unpack_seq s = xs) :
    RuleProofs.smt_value_rel (SmtValue.Seq s)
      (SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value base) xs)) := by
  have hsElem : __smtx_elem_typeof_seq_value s = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsTy
  have hbaseElem : __smtx_elem_typeof_seq_value base = T :=
    elem_typeof_seq_value_of_typeof_seq_value hbaseTy
  change RuleProofs.smt_seq_rel s
    (native_pack_seq (__smtx_elem_typeof_seq_value base) xs)
  apply (RuleProofs.smt_seq_rel_iff_eq _ _).2
  calc
    s = native_pack_seq (__smtx_elem_typeof_seq_value s)
        (native_unpack_seq s) := (native_pack_unpack_seq s).symm
    _ = native_pack_seq (__smtx_elem_typeof_seq_value base) xs := by
      rw [hUnpack, hsElem, hbaseElem]

private theorem str_nary_intro_ne_stuck_of_seq_type
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_nary_intro x ≠ Term.Stuck := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hEq⟩
    subst x
    have hNN :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) ≠ SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    exact RuleProofs.term_ne_stuck_of_has_smt_translation
      (__str_nary_intro (mkConcat head tail))
      (str_nary_intro_concat_has_smt_translation head tail hNN)
  · have hxNe : x ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq x T hxTy
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    have hTypeMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
    have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hTypeMatch, hxTy]
    let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
    have hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true :=
      eo_is_list_str_concat_nil_true_of_nil_true nil
        (by simpa [nil] using strConcat_nil_is_list_nil_of_type hTy)
    have hNilNe : nil ≠ Term.Stuck := by
      have hNilEq : nil = __seq_empty (__eo_typeof x) := by
        simpa [nil] using strConcat_nil_eq_seq_empty_of_type hTy
      simpa [hNilEq] using seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
    rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat) x
        (by decide) hxNe with ⟨isList, hListBool⟩
    cases isList
    · have hIntroEq :
          __str_nary_intro x =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil := by
        simp [__str_nary_intro, __eo_list_singleton_intro, nil, hListBool,
          eo_ite_false, hNilList, __eo_requires, native_teq, native_ite,
          SmtEval.native_ite, SmtEval.native_not]
      have hApplyNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) nil ≠
            Term.Stuck := by
        cases hNilCases : nil <;> simp [__eo_mk_apply, hNilCases] at hNilNe ⊢
      simpa [hIntroEq] using hApplyNe
    · have hIntroEq : __str_nary_intro x = x :=
        str_nary_intro_eq_self_of_is_list x (by simpa using hListBool)
      simpa [hIntroEq] using hxNe

private theorem smt_typeof_seq_value_of_eval_seq
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (T : SmtType) (sx : SmtSeq)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq sx) :
    __smtx_typeof_seq_value sx = SmtType.Seq T := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by
        unfold term_has_non_none_type
        rw [hTy]
        exact seq_ne_none T)
  rw [hEval] at hEvalTy
  simpa [__smtx_typeof_value, hTy] using hEvalTy

private theorem smt_value_rel_model_eval_str_len_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_len a) (__smtx_model_eval_str_len b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_len, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_prefixof_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_prefixof a b)
      (__smtx_model_eval_str_prefixof c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    unfold RuleProofs.smt_value_rel
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
        __smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      unfold RuleProofs.smt_value_rel
      cases a <;>
        simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_substr,
          __smtx_model_eval_eq, native_veq]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_substr_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_substr a b c)
      (__smtx_model_eval_str_substr d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    unfold RuleProofs.smt_value_rel
    cases b <;> cases e <;> cases c <;> cases f <;>
      simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      unfold RuleProofs.smt_value_rel
      cases a <;> cases c <;> cases f <;>
        simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
          native_veq]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        unfold RuleProofs.smt_value_rel
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
            native_veq]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_model_eval_str_at_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_at a b)
      (__smtx_model_eval_str_at c d) := by
  intro hRelA hRelB
  unfold __smtx_model_eval_str_at
  exact smt_value_rel_model_eval_str_substr_of_rel a b
    (SmtValue.Numeral 1) c d (SmtValue.Numeral 1)
    hRelA hRelB (RuleProofs.smt_value_rel_refl _)

private theorem smtx_model_eval_str_substr_term_eq
    (M : SmtModel) (s i n : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) i) n)) =
      __smtx_model_eval_str_substr
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt i))
        (__smtx_model_eval M (__eo_to_smt n)) := by
  change
    __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt i)
          (__eo_to_smt n)) =
      __smtx_model_eval_str_substr
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt i))
        (__smtx_model_eval M (__eo_to_smt n))
  rw [__smtx_model_eval.eq_82]

private theorem smtx_model_eval_str_at_term_eq
    (M : SmtModel) (s i : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) s) i)) =
      __smtx_model_eval_str_at
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt i)) := by
  change
    __smtx_model_eval M
        (SmtTerm.str_at (__eo_to_smt s) (__eo_to_smt i)) =
      __smtx_model_eval_str_at
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt i))
  rw [__smtx_model_eval.eq_def]

private theorem smt_typeof_raw_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (Term.UOp1 UserOp1.seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
    have hGood :=
      smt_term_result_seq_components_wf_of_non_none (__eo_to_smt x) hTrans
    simpa [hxTy, type_result_seq_components_wf] using hGood
  change
    __smtx_typeof
        (__eo_to_smt_seq_empty (__eo_to_smt_type (__eo_typeof x))) =
      SmtType.Seq T
  rw [hA]
  change __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T
  exact TranslationProofs.smtx_typeof_seq_empty_of_non_none T (by
    simp [__smtx_typeof, __smtx_typeof_guard_wf, hSeqWF, native_ite])

private theorem smtx_model_eval_raw_seq_empty_typeof
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (Term.UOp1 UserOp1.seq_empty (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  change
    __smtx_model_eval M
        (__eo_to_smt_seq_empty (__eo_to_smt_type (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T)
  rw [hA]
  change __smtx_model_eval M (SmtTerm.seq_empty T) =
    SmtValue.Seq (SmtSeq.empty T)
  rw [__smtx_model_eval.eq_79]

private theorem smtx_model_eval_seq_empty_term_of_type
    (M : SmtModel) (A : Term) (T : SmtType)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
      SmtValue.Seq (SmtSeq.empty T) := by
  change
    __smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtValue.Seq (SmtSeq.empty T)
  change
    __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtType.Seq T at hTy
  cases hA : __eo_to_smt_type A with
  | Seq U =>
      simp [__eo_to_smt_seq_empty, hA] at hTy ⊢
      rw [smtx_typeof_seq_empty_term_eq] at hTy
      have hGuardNN :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) ≠
            SmtType.None := by
        rw [hTy]
        exact seq_ne_none T
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) =
            SmtType.Seq U :=
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq U) (SmtType.Seq U)
          hGuardNN
      rw [hGuard] at hTy
      injection hTy with hU
      subst U
      rw [smtx_eval_seq_empty_term_eq]
  | _ =>
      simp [__eo_to_smt_seq_empty, hA, TranslationProofs.smtx_typeof_none]
        at hTy

private theorem native_seq_extract_empty_of_end_nonpos
    (xs : List SmtValue) (i n : native_Int)
    (hEnd : i + n <= 0) :
    native_seq_extract xs i n = [] := by
  unfold native_seq_extract
  by_cases hi : i < 0
  · have hGuard :
        (decide (i < 0) || decide (n <= 0) ||
            decide (i >= Int.ofNat xs.length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inl hi)
    rw [if_pos hGuard]
  · have hiNonneg : 0 <= i := Int.le_of_not_gt hi
    have hn : n <= 0 := by
      by_cases hn : n <= 0
      · exact hn
      · have hnPos : 0 < n := Int.lt_of_not_ge hn
        have hSumPos : 0 < i + n :=
          Int.add_pos_of_nonneg_of_pos hiNonneg hnPos
        exact False.elim ((Int.not_le_of_gt hSumPos) hEnd)
    have hGuard :
        (decide (i < 0) || decide (n <= 0) ||
            decide (i >= Int.ofNat xs.length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inr hn)
    rw [if_pos hGuard]

private theorem native_seq_extract_empty_of_end_neg
    (xs : List SmtValue) (i n : native_Int)
    (hEnd : i + n < 0) :
    native_seq_extract xs i n = [] :=
  native_seq_extract_empty_of_end_nonpos xs i n (Int.le_of_lt hEnd)

private theorem native_seq_extract_nil (i n : native_Int) :
    native_seq_extract [] i n = [] := by
  simp [native_seq_extract]

private theorem native_seq_extract_zero_nat_any_local
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n <= xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length <= n := Nat.le_of_lt hLenLt
        have hLenNotLe :
            ¬ ((Int.ofNat xs.length : Int) + 1 <= 0) := by
          have hNonneg : (0 : Int) <= Int.ofNat xs.length :=
            Int.natCast_nonneg xs.length
          omega
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        have hminNat : min n xs.length.succ = xs.length.succ :=
          Nat.min_eq_right hLenLe
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat, List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

private theorem native_seq_extract_cons_zero_pos
    (x : SmtValue) (xs : List SmtValue) (e : native_Int)
    (he : 0 < e) :
    native_seq_extract (x :: xs) 0 e =
      x :: native_seq_extract xs 0 (e - 1) := by
  let k := e.toNat
  have heEq : e = Int.ofNat k :=
    (Int.toNat_of_nonneg (Int.le_of_lt he)).symm
  have hkPos : 0 < k := by
    have hInt : (0 : Int) < Int.ofNat k := by
      rw [← heEq]
      exact he
    exact Int.ofNat_lt.mp hInt
  have hPredK : (Int.ofNat k : Int) - 1 = Int.ofNat (k - 1) := by
    have hOne : 1 <= k := Nat.succ_le_of_lt hkPos
    simpa using (Int.ofNat_sub hOne).symm
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkPos) with ⟨k', hkEq⟩
  rw [heEq, native_seq_extract_zero_nat_any_local (x :: xs) k]
  rw [hPredK, native_seq_extract_zero_nat_any_local xs (k - 1)]
  rw [hkEq]
  simp

private theorem native_seq_extract_cons_pos_nat
    (x : SmtValue) (xs : List SmtValue) (k : Nat) (n : native_Int) :
    native_seq_extract (x :: xs) (Int.ofNat (Nat.succ k)) n =
      native_seq_extract xs (Int.ofNat k) n := by
  unfold native_seq_extract
  by_cases hn : n <= 0
  · have hLeftGuard :
        (decide ((Int.ofNat (Nat.succ k) : Int) < 0) ||
            decide (n <= 0) ||
            decide
              ((Int.ofNat (Nat.succ k) : Int) >=
                Int.ofNat (x :: xs).length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inr hn)
    have hRightGuard :
        (decide ((Int.ofNat k : Int) < 0) ||
            decide (n <= 0) ||
            decide ((Int.ofNat k : Int) >= Int.ofNat xs.length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inr hn)
    rw [if_pos hLeftGuard, if_pos hRightGuard]
  · by_cases hOut :
        (Int.ofNat (Nat.succ k) : Int) >=
          Int.ofNat (x :: xs).length
    · have hRightOut :
          (Int.ofNat k : Int) >= Int.ofNat xs.length := by
        have hOutNat : (x :: xs).length <= Nat.succ k :=
          Int.ofNat_le.mp hOut
        have hRightOutNat : xs.length <= k :=
          Nat.succ_le_succ_iff.mp (by simpa using hOutNat)
        exact Int.ofNat_le.mpr hRightOutNat
      have hLeftGuard :
          (decide ((Int.ofNat (Nat.succ k) : Int) < 0) ||
              decide (n <= 0) ||
              decide
                ((Int.ofNat (Nat.succ k) : Int) >=
                  Int.ofNat (x :: xs).length)) =
            true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hOut
      have hRightGuard :
          (decide ((Int.ofNat k : Int) < 0) ||
              decide (n <= 0) ||
              decide ((Int.ofNat k : Int) >= Int.ofNat xs.length)) =
            true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hRightOut
      rw [if_pos hLeftGuard, if_pos hRightGuard]
    · have hRightIn :
          ¬ ((Int.ofNat k : Int) >= Int.ofNat xs.length) := by
        intro hRightOut
        apply hOut
        have hRightOutNat : xs.length <= k :=
          Int.ofNat_le.mp hRightOut
        have hOutNat : (x :: xs).length <= Nat.succ k := by
          simpa using Nat.succ_le_succ hRightOutNat
        exact Int.ofNat_le.mpr hOutNat
      have hLen :
          (Int.ofNat xs.length + 1) - (Int.ofNat k + 1) =
            Int.ofNat xs.length - Int.ofNat k := by
        omega
      have hRightLtNat : k < xs.length := by
        apply Nat.lt_of_not_ge
        intro hRightOutNat
        exact hRightIn (Int.ofNat_le.mpr hRightOutNat)
      have hNotRightOutNat : ¬ xs.length <= k :=
        Nat.not_le_of_gt hRightLtNat
      have hSuccIdxNonneg :
          ¬ (Int.ofNat k + 1 < 0) := by
        intro h
        have hkNonneg : (0 : Int) <= Int.ofNat k :=
          Int.natCast_nonneg k
        omega
      have hIdxNonneg :
          ¬ ((Int.ofNat k : Int) < 0) := by
        intro h
        have hkNonneg : (0 : Int) <= Int.ofNat k :=
          Int.natCast_nonneg k
        omega
      simp [hn, hNotRightOutNat]
      change
        (if (Int.ofNat k + 1 < 0) then ([] : List SmtValue)
          else
            List.take
              (Int.toNat (min n
                (Int.ofNat xs.length + 1 - (Int.ofNat k + 1))))
              (List.drop k xs)) =
          (if ((Int.ofNat k : Int) < 0) then ([] : List SmtValue)
            else
              List.take
                (Int.toNat (min n (Int.ofNat xs.length - Int.ofNat k)))
                (List.drop k xs))
      rw [if_neg hSuccIdxNonneg, if_neg hIdxNonneg, hLen]

private theorem native_seq_extract_cons_nonzero
    (x : SmtValue) (xs : List SmtValue) (i n : native_Int)
    (hi : i ≠ 0) :
    native_seq_extract (x :: xs) i n =
      native_seq_extract xs (i - 1) n := by
  by_cases hiNeg : i < 0
  · unfold native_seq_extract
    have hLeftGuard :
        (decide (i < 0) || decide (n <= 0) ||
            decide (i >= Int.ofNat (x :: xs).length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inl hiNeg)
    have hPredNeg : i - 1 < 0 := by
      exact (Int.sub_one_lt_iff).2 (Int.le_of_lt hiNeg)
    have hRightGuard :
        (decide (i - 1 < 0) || decide (n <= 0) ||
            decide (i - 1 >= Int.ofNat xs.length)) =
          true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (Or.inl hPredNeg)
    rw [if_pos hLeftGuard, if_pos hRightGuard]
  · have hiNonneg : 0 <= i := Int.le_of_not_gt hiNeg
    have hiPos : 0 < i := by
      apply Int.lt_of_not_ge
      intro hiLe
      exact hi (Int.le_antisymm hiLe hiNonneg)
    let k := i.toNat
    have hiEq : i = Int.ofNat k :=
      (Int.toNat_of_nonneg hiNonneg).symm
    have hkPos : 0 < k := by
      have hInt : (0 : Int) < Int.ofNat k := by
        rw [← hiEq]
        exact hiPos
      exact Int.ofNat_lt.mp hInt
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkPos) with
      ⟨k', hkEq⟩
    have hPredK :
        (Int.ofNat (Nat.succ k') : Int) - 1 = Int.ofNat k' := by
      simp
    rw [hiEq, hkEq, hPredK]
    exact native_seq_extract_cons_pos_nat x xs k' n

private theorem smt_value_rel_raw_empty_str_substr_of_end_neg
    (M : SmtModel) (hM : model_wf M)
    (a : Term) (T : SmtType) (i n : native_Int)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hEnd : i + n < 0) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))))
      (__smtx_model_eval_str_substr
        (__smtx_model_eval M (__eo_to_smt a))
        (SmtValue.Numeral i) (SmtValue.Numeral n)) := by
  rcases seq_eval_of_seq_type M hM a T hATy with ⟨sa, hAEval⟩
  have hSaTy : __smtx_typeof_seq_value sa = SmtType.Seq T :=
    smt_typeof_seq_value_of_eval_seq M hM a T sa hATy hAEval
  have hElem : __smtx_elem_typeof_seq_value sa = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSaTy
  rw [smtx_model_eval_raw_seq_empty_typeof M a T hATy, hAEval]
  unfold RuleProofs.smt_value_rel
  simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
    native_veq, native_pack_seq, hElem, native_seq_extract_empty_of_end_neg
      (native_unpack_seq sa) i n hEnd]

private theorem int_sub_one_sub_sub_one (e i : native_Int) :
    (e - 1) - (i - 1) = e - i := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
  rw [Int.neg_add]
  simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
  rw [Int.sub_eq_add_neg]

private theorem eo_add_int_args_numerals_of_ne_stuck
    (n m : Term)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hmTy : __smtx_typeof (__eo_to_smt m) = SmtType.Int)
    (hAddNe : __eo_add n m ≠ Term.Stuck) :
    ∃ i j : native_Int,
      n = Term.Numeral i ∧
        m = Term.Numeral j ∧
          __eo_add n m = Term.Numeral (native_zplus i j) := by
  cases n <;> cases m <;>
    simp [__eo_add] at hAddNe ⊢
  case Rational.Rational r _ =>
    change __smtx_typeof (SmtTerm.Rational r) = SmtType.Int at hnTy
    rw [__smtx_typeof.eq_3] at hnTy
    cases hnTy
  case Binary.Binary w n _ _ =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Int at hnTy
    rw [__smtx_typeof.eq_5] at hnTy
    cases hValid :
        (native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w)))) <;>
      simp [native_ite, hValid] at hnTy

private theorem seq_find_left_ne_stuck_of_ne_stuck (a b n : Term)
    (h : __seq_find a b n ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  cases b <;> cases n <;> rw [__seq_find.eq_def] at h <;> simp at h

private theorem seq_find_right_ne_stuck_of_ne_stuck (a b n : Term)
    (h : __seq_find a b n ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> cases n <;> rw [__seq_find.eq_def] at h <;> simp at h

private theorem seq_find_index_ne_stuck_of_ne_stuck (a b n : Term)
    (h : __seq_find a b n ≠ Term.Stuck) :
    n ≠ Term.Stuck := by
  intro hn
  subst n
  cases a <;> cases b <;> rw [__seq_find.eq_def] at h <;> simp at h

private theorem l1_seq_find_right_ne_stuck_of_ne_stuck (a b n : Term)
    (h : __eo_l_1___seq_find a b n ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> cases n <;> rw [__eo_l_1___seq_find.eq_def] at h <;> simp at h

private theorem l1_seq_find_index_ne_stuck_of_ne_stuck (a b n : Term)
    (h : __eo_l_1___seq_find a b n ≠ Term.Stuck) :
    n ≠ Term.Stuck := by
  intro hn
  subst n
  cases a <;> cases b <;> rw [__eo_l_1___seq_find.eq_def] at h <;> simp at h

private theorem l1_seq_find_empty_eq_of_args_ne_stuck (s n U : Term)
    (hs : s ≠ Term.Stuck) (hn : n ≠ Term.Stuck) :
    __eo_l_1___seq_find
        (Term.UOp1 UserOp1.seq_empty ((Term.UOp UserOp.Seq).Apply U))
        s n =
      Term.Numeral (-1 : native_Int) := by
  cases s
  case Stuck => exact False.elim (hs rfl)
  all_goals
    cases n
    case Stuck => exact False.elim (hn rfl)
    all_goals
      rw [__eo_l_1___seq_find.eq_def]

private theorem l1_seq_find_concat_eq_of_args_ne_stuck (t ts s n : Term)
    (hs : s ≠ Term.Stuck) (hn : n ≠ Term.Stuck) :
    __eo_l_1___seq_find
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts) s n =
      __eo_ite
        (__seq_is_prefix s
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts))
        n
        (__seq_find ts s (__eo_add n (Term.Numeral 1))) := by
  cases s
  case Stuck => exact False.elim (hs rfl)
  all_goals
    cases n
    case Stuck => exact False.elim (hn rfl)
    all_goals
      rw [__eo_l_1___seq_find.eq_def]

private theorem seq_find_eq_of_args_ne_stuck (a b n : Term)
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) (hn : n ≠ Term.Stuck) :
    __seq_find a b n =
      __eo_ite (__eo_eq a b) n (__eo_l_1___seq_find a b n) := by
  cases a
  case Stuck => exact False.elim (ha rfl)
  all_goals
    cases b
    case Stuck => exact False.elim (hb rfl)
    all_goals
      cases n
      case Stuck => exact False.elim (hn rfl)
      all_goals
        rw [__seq_find.eq_def]

mutual

private theorem smt_typeof_l1_seq_find_of_seq :
    ∀ a b n T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __eo_l_1___seq_find a b n ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_l_1___seq_find a b n)) =
        SmtType.Int
  | _, Term.Stuck, _, T, _ha, _hb, _hn, hNe => by
      exact False.elim
        ((l1_seq_find_right_ne_stuck_of_ne_stuck _ _ _ hNe) rfl)
  | _, _, Term.Stuck, T, _ha, _hb, _hn, hNe => by
      exact False.elim
        ((l1_seq_find_index_ne_stuck_of_ne_stuck _ _ _ hNe) rfl)
  | Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U),
      s, n, T, _ha, _hb, _hn, _hNe => by
      have hRightNe :
          s ≠ Term.Stuck :=
        l1_seq_find_right_ne_stuck_of_ne_stuck
          (Term.UOp1 UserOp1.seq_empty ((Term.UOp UserOp.Seq).Apply U))
          s n _hNe
      have hIndexNe :
          n ≠ Term.Stuck :=
        l1_seq_find_index_ne_stuck_of_ne_stuck
          (Term.UOp1 UserOp1.seq_empty ((Term.UOp UserOp.Seq).Apply U))
          s n _hNe
      rw [l1_seq_find_empty_eq_of_args_ne_stuck s n U hRightNe hIndexNe]
      change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int
      rw [__smtx_typeof.eq_2]
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts,
      s, n', T, ha, hb, hn, hNe => by
    let whole := mkConcat t ts
    let next := __seq_find ts s (__eo_add n' (Term.Numeral 1))
    have hRightNe :
        s ≠ Term.Stuck :=
      l1_seq_find_right_ne_stuck_of_ne_stuck
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)
        s n' hNe
    have hIndexNe :
        n' ≠ Term.Stuck :=
      l1_seq_find_index_ne_stuck_of_ne_stuck
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)
        s n' hNe
    have hL1Eq :
        __eo_l_1___seq_find
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)
            s n' =
          __eo_ite (__seq_is_prefix s whole) n' next := by
      simpa [whole, next] using
        l1_seq_find_concat_eq_of_args_ne_stuck t ts s n'
          hRightNe hIndexNe
    rw [hL1Eq] at hNe ⊢
    change __smtx_typeof (__eo_to_smt
        (__eo_ite (__seq_is_prefix s whole) n' next)) = SmtType.Int
    rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix s whole) n' next
        hNe with hCond | hCond
    · rw [hCond, eo_ite_true]
      exact hn
    · have hNextNe : next ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      have hAddNe : __eo_add n' (Term.Numeral 1) ≠ Term.Stuck :=
        seq_find_index_ne_stuck_of_ne_stuck ts s
          (__eo_add n' (Term.Numeral 1)) hNextNe
      have hOneTy :
          __smtx_typeof (__eo_to_smt (Term.Numeral 1)) = SmtType.Int := by
        change __smtx_typeof (SmtTerm.Numeral (1 : native_Int)) =
          SmtType.Int
        rw [__smtx_typeof.eq_2]
      rcases eo_add_int_args_numerals_of_ne_stuck n' (Term.Numeral 1)
          hn hOneTy hAddNe with ⟨i, j, hnEq, hOneEq, hAddEq⟩
      have hAddTy :
          __smtx_typeof (__eo_to_smt (__eo_add n' (Term.Numeral 1))) =
            SmtType.Int := by
        rw [hAddEq]
        change __smtx_typeof (SmtTerm.Numeral (native_zplus i j)) =
          SmtType.Int
        rw [__smtx_typeof.eq_2]
      obtain ⟨_hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type t ts T (by simpa [whole, mkConcat] using ha)
      rw [hCond, eo_ite_false]
      exact smt_typeof_seq_find_of_seq ts s (__eo_add n' (Term.Numeral 1))
        T hTailTy hb hAddTy (by simpa [next] using hNextNe)
  | a, b, n, T, ha, hb, hn, hNe => by
      rw [__eo_l_1___seq_find.eq_def] at hNe
      split at hNe
      · simp at hNe
      · simp at hNe
      · rename_i _ _ _ U hRightNe hIndexNe
        rw [l1_seq_find_empty_eq_of_args_ne_stuck b n U hRightNe hIndexNe]
        change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) =
          SmtType.Int
        rw [__smtx_typeof.eq_2]
      · rename_i _ _ _ t ts hRightNe hIndexNe
        let whole := mkConcat t ts
        let next := __seq_find ts b (__eo_add n (Term.Numeral 1))
        have hL1Eq :
            __eo_l_1___seq_find
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)
                b n =
              __eo_ite (__seq_is_prefix b whole) n next := by
          simpa [whole, next] using
            l1_seq_find_concat_eq_of_args_ne_stuck t ts b n
              hRightNe hIndexNe
        rw [hL1Eq]
        change __smtx_typeof (__eo_to_smt
            (__eo_ite (__seq_is_prefix b whole) n next)) = SmtType.Int
        rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix b whole) n next
            hNe with hCond | hCond
        · rw [hCond, eo_ite_true]
          exact hn
        · have hNextNe : next ≠ Term.Stuck := by
            simpa [whole, next, hCond, eo_ite_false] using hNe
          have hAddNe : __eo_add n (Term.Numeral 1) ≠ Term.Stuck :=
            seq_find_index_ne_stuck_of_ne_stuck ts b
              (__eo_add n (Term.Numeral 1)) hNextNe
          have hOneTy :
              __smtx_typeof (__eo_to_smt (Term.Numeral 1)) = SmtType.Int := by
            change __smtx_typeof (SmtTerm.Numeral (1 : native_Int)) =
              SmtType.Int
            rw [__smtx_typeof.eq_2]
          rcases eo_add_int_args_numerals_of_ne_stuck n (Term.Numeral 1)
              hn hOneTy hAddNe with ⟨i, j, hnEq, hOneEq, hAddEq⟩
          have hAddTy :
              __smtx_typeof (__eo_to_smt (__eo_add n (Term.Numeral 1))) =
                SmtType.Int := by
            rw [hAddEq]
            change __smtx_typeof (SmtTerm.Numeral (native_zplus i j)) =
              SmtType.Int
            rw [__smtx_typeof.eq_2]
          obtain ⟨_hHeadTy, hTailTy⟩ :=
            strConcat_args_of_seq_type t ts T
              (by simpa [whole, mkConcat] using ha)
          rw [hCond, eo_ite_false]
          exact smt_typeof_seq_find_of_seq ts b (__eo_add n (Term.Numeral 1))
            T hTailTy hb hAddTy (by simpa [next] using hNextNe)
      · simp at hNe

private theorem smt_typeof_seq_find_of_seq :
    ∀ a b n T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __seq_find a b n ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__seq_find a b n)) = SmtType.Int
  | Term.Stuck, _, _, T, _ha, _hb, _hn, hNe => by
      exact False.elim
        ((seq_find_left_ne_stuck_of_ne_stuck _ _ _ hNe) rfl)
  | _, Term.Stuck, _, T, _ha, _hb, _hn, hNe => by
      exact False.elim
        ((seq_find_right_ne_stuck_of_ne_stuck _ _ _ hNe) rfl)
  | _, _, Term.Stuck, T, _ha, _hb, _hn, hNe => by
      exact False.elim
        ((seq_find_index_ne_stuck_of_ne_stuck _ _ _ hNe) rfl)
  | t, s, n', T, ha, hb, hn, hNe => by
    let l1 := __eo_l_1___seq_find t s n'
    have hLeftNe : t ≠ Term.Stuck :=
      seq_find_left_ne_stuck_of_ne_stuck t s n' hNe
    have hRightNe : s ≠ Term.Stuck :=
      seq_find_right_ne_stuck_of_ne_stuck t s n' hNe
    have hIndexNe : n' ≠ Term.Stuck :=
      seq_find_index_ne_stuck_of_ne_stuck t s n' hNe
    have hFindEq :
        __seq_find t s n' = __eo_ite (__eo_eq t s) n' l1 := by
      simpa [l1] using
        seq_find_eq_of_args_ne_stuck t s n' hLeftNe hRightNe hIndexNe
    rw [hFindEq] at hNe ⊢
    change __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq t s) n' l1)) = SmtType.Int
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t s) n' l1 hNe with
      hCond | hCond
    · rw [hCond, eo_ite_true]
      exact hn
    · have hL1Ne : l1 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      rw [hCond, eo_ite_false]
      exact smt_typeof_l1_seq_find_of_seq t s n' T ha hb hn
        (by simpa [l1] using hL1Ne)

end

private theorem smt_typeof_seq_subsequence_rec_of_seq :
    ∀ l u a T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __seq_subsequence_rec l u a ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__seq_subsequence_rec l u a)) =
        SmtType.Seq T := by
  intro l u a
  induction l, u, a using __seq_subsequence_rec.induct with
  | case1 t x =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case2 t x hx =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case3 x y hx hy =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case4 l u U hl hu =>
      intro T hTy _hNe
      simpa [__seq_subsequence_rec] using hTy
  | case5 l t hl ht hNotEmpty =>
      intro T hTy _hNe
      simpa [__seq_subsequence_rec] using
        smt_typeof_raw_seq_empty_typeof t T hTy
  | case6 u e ts hu hUNeZero ih =>
      intro T hTy hNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let subseq :=
        __seq_subsequence_rec (Term.Numeral 0)
          (__eo_add u (Term.Numeral (-1 : native_Int))) ts
      have hFullNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq ≠
            Term.Stuck := by
        simpa [__seq_subsequence_rec, head, subseq] using hNe
      have hRecNe : subseq ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hTy)
      have hRecTy :
          __smtx_typeof (__eo_to_smt subseq) = SmtType.Seq T :=
        ih T hTailTy hRecNe
      have hApplyEq :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq =
            mkConcat head subseq :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      simpa [__seq_subsequence_rec, head, subseq, hApplyEq] using
        smt_typeof_str_concat_of_seq head subseq T hHeadTy hRecTy
  | case7 l u e ts hl hu hUNeZero hLNeZero ih =>
      intro T hTy hNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      obtain ⟨_hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hTy)
      have hRecNe :
          __seq_subsequence_rec
              (__eo_add l (Term.Numeral (-1 : native_Int)))
              (__eo_add u (Term.Numeral (-1 : native_Int))) ts ≠
            Term.Stuck := by
        simpa [__seq_subsequence_rec, head] using hNe
      simpa [__seq_subsequence_rec, head] using
        ih T hTailTy hRecNe
  | case8 t x y hx hy hyZero ht hNotEmpty hNotZeroConcat hNotConcat =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe

private theorem is_seq_const_rec_raw_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __is_seq_const_rec
        (Term.UOp1 UserOp1.seq_empty (__eo_typeof x)) =
      Term.Boolean true := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rcases TranslationProofs.eo_to_smt_type_eq_seq hA with
    ⟨U, hType, _hU⟩
  rw [hType]
  simp [__is_seq_const_rec]

private theorem is_seq_const_rec_seq_subsequence_rec_true_of_seq :
    ∀ l u a T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __seq_subsequence_rec l u a ≠ Term.Stuck ->
      __is_seq_const_rec (__seq_subsequence_rec l u a) =
        Term.Boolean true := by
  intro l u a
  induction l, u, a using __seq_subsequence_rec.induct with
  | case1 t x =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case2 t x hx =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case3 x y hx hy =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe
  | case4 l u U hl hu =>
      intro T _hTy _hNe
      simp [__seq_subsequence_rec, __is_seq_const_rec]
  | case5 l t hl ht hNotEmpty =>
      intro T hTy _hNe
      simpa [__seq_subsequence_rec] using
        is_seq_const_rec_raw_seq_empty_typeof_of_seq t T hTy
  | case6 u e ts hu hUNeZero ih =>
      intro T hTy hNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let subseq :=
        __seq_subsequence_rec (Term.Numeral 0)
          (__eo_add u (Term.Numeral (-1 : native_Int))) ts
      have hFullNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq ≠
            Term.Stuck := by
        simpa [__seq_subsequence_rec, head, subseq] using hNe
      have hRecNe : subseq ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      obtain ⟨_hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hTy)
      have hRecConst :
          __is_seq_const_rec subseq = Term.Boolean true :=
        ih T hTailTy hRecNe
      have hApplyEq :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq =
            mkConcat head subseq :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      simpa [__seq_subsequence_rec, head, subseq, hApplyEq,
        __is_seq_const_rec] using hRecConst
  | case7 l u e ts hl hu hUNeZero hLNeZero ih =>
      intro T hTy hNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      obtain ⟨_hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hTy)
      have hRecNe :
          __seq_subsequence_rec
              (__eo_add l (Term.Numeral (-1 : native_Int)))
              (__eo_add u (Term.Numeral (-1 : native_Int))) ts ≠
            Term.Stuck := by
        simpa [__seq_subsequence_rec, head] using hNe
      simpa [__seq_subsequence_rec, head] using
        ih T hTailTy hRecNe
  | case8 t x y hx hy hyZero ht hNotEmpty hNotZeroConcat hNotConcat =>
      intro T _hTy hNe
      simp [__seq_subsequence_rec] at hNe

private theorem smt_typeof_seq_substr_body_of_seq
    (a n u : Term) (T : SmtType)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hBodyNe :
      __eo_ite (__eo_is_neg u)
          (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
          (__seq_subsequence_rec n u a) ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_ite (__eo_is_neg u)
            (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
            (__seq_subsequence_rec n u a))) =
      SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck (__eo_is_neg u)
      (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
      (__seq_subsequence_rec n u a) hBodyNe with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact smt_typeof_raw_seq_empty_typeof a T hATy
  · have hSubseqNe : __seq_subsequence_rec n u a ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hBodyNe
    rw [hCond, eo_ite_false]
    exact smt_typeof_seq_subsequence_rec_of_seq n u a T hATy hSubseqNe

private theorem smt_typeof_list_concat_str_concat_of_seq
    (a z : Term) (T : SmtType)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hConcatNe :
      __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
      SmtType.Seq T := by
  have hLists := eo_list_concat_str_concat_lists_of_ne_stuck a z hConcatNe
  rw [eo_list_concat_str_concat_eq_rec_of_ne_stuck a z hConcatNe]
  exact smt_typeof_list_concat_rec_str_concat_of_seq a z T hLists.1 haTy hzTy

private theorem eo_list_concat_str_concat_unpack_of_seq_evals
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (T : SmtType) (sa sz sc : SmtSeq)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa)
    (hZEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz)
    (hConcatNe :
      __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck)
    (hConcatEval :
      __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.str_concat) a z)) =
        SmtValue.Seq sc) :
    native_unpack_seq sc = native_unpack_seq sa ++ native_unpack_seq sz := by
  have hLists := eo_list_concat_str_concat_lists_of_ne_stuck a z hConcatNe
  have hEqRec :=
    eo_list_concat_str_concat_eq_rec_of_ne_stuck a z hConcatNe
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) :=
    strConcat_smt_value_rel_list_concat_rec_eval M hM a z T
      hLists.1 haTy hzTy
  have hConcatEvalRec :
      __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
        SmtValue.Seq sc := by
    simpa [hEqRec] using hConcatEval
  have hMkEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat a z)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value sa)
            (native_unpack_seq sa ++ native_unpack_seq sz)) :=
    RuleProofs.strConcat_eval_eq M a z sa sz hAEval hZEval
  have hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq sc)
        (SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value sa)
            (native_unpack_seq sa ++ native_unpack_seq sz))) := by
    -- rewrite with the concat evaluation before `simp` unfolds
    -- `__eo_to_smt (mkConcat ..)` past its left-hand side
    rw [hConcatEvalRec, hMkEval] at hRel
    exact hRel
  have hUnpack := smt_value_rel_seq_unpack_eq hSeqRel
  simpa [Smtm.native_unpack_pack_seq] using hUnpack

private theorem smt_typeof_eo_cons_str_concat_of_seq
    (head tail : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hConsNe :
      __eo_cons (Term.UOp UserOp.str_concat) head tail ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_cons (Term.UOp UserOp.str_concat) head tail)) =
      SmtType.Seq T := by
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) tail)
          (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail))) =
    SmtType.Seq T
  have hEq :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_list (Term.UOp UserOp.str_concat) tail)
      (Term.Boolean true)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail)
      hConsNe
  rw [hEq]
  exact smt_typeof_str_concat_of_seq head tail T hHeadTy hTailTy

private theorem seq_eval_replace_all_rec_skip_ne_stuck_of_ne_stuck
    (a b u skip lent : Term)
    (h : __seq_eval_replace_all_rec a b u skip lent ≠ Term.Stuck) :
    skip ≠ Term.Stuck := by
  revert h
  induction a, b, u, skip, lent using __seq_eval_replace_all_rec.induct with
  | case1 a u skip lent =>
      intro h hskip
      simp [__seq_eval_replace_all_rec] at h
  | case2 a b skip lent hb =>
      intro h hskip
      simp [__seq_eval_replace_all_rec] at h
  | case3 a b u lent hb hu =>
      intro h hskip
      simp [__seq_eval_replace_all_rec] at h
  | case4 a b u skip hb hu hskip =>
      intro h hskip'
      exact hskip hskip'
  | case5 U b u skip lent hb hu hskip hlent =>
      intro h hskip'
      exact hskip hskip'
  | case6 s1 s2 b u lent hb hu hlent ihSkip ihZero =>
      intro h hskip
      cases hskip
  | case7 s1 s2 b u skip lent hb hu hskip hlent hSkipNeZero ih =>
      intro h hskip'
      exact hskip hskip'
  | case8 a b u skip lent hb hu hskip hlent hNotEmpty hNotConcatZero
      hNotConcat =>
      intro h hskip'
      exact hskip hskip'

private theorem seq_eval_replace_all_rec_lent_ne_stuck_of_ne_stuck
    (a b u skip lent : Term)
    (h : __seq_eval_replace_all_rec a b u skip lent ≠ Term.Stuck) :
    lent ≠ Term.Stuck := by
  revert h
  induction a, b, u, skip, lent using __seq_eval_replace_all_rec.induct with
  | case1 a u skip lent =>
      intro h hlent
      simp [__seq_eval_replace_all_rec] at h
  | case2 a b skip lent hb =>
      intro h hlent
      simp [__seq_eval_replace_all_rec] at h
  | case3 a b u lent hb hu =>
      intro h hlent
      simp [__seq_eval_replace_all_rec] at h
  | case4 a b u skip hb hu hskip =>
      intro h hlent
      simp [__seq_eval_replace_all_rec] at h
  | case5 U b u skip lent hb hu hskip hlent =>
      intro h hlent'
      exact hlent hlent'
  | case6 s1 s2 b u lent hb hu hlent ihSkip ihZero =>
      intro h hlent'
      exact hlent hlent'
  | case7 s1 s2 b u skip lent hb hu hskip hlent hSkipNeZero ih =>
      intro h hlent'
      exact hlent hlent'
  | case8 a b u skip lent hb hu hskip hlent hNotEmpty hNotConcatZero
      hNotConcat =>
      intro h hlent'
      exact hlent hlent'

private theorem smt_typeof_seq_eval_replace_all_rec_of_seq :
    ∀ a b u skip lent T,
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt skip) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt lent) = SmtType.Int ->
      __seq_eval_replace_all_rec a b u skip lent ≠ Term.Stuck ->
      __smtx_typeof
          (__eo_to_smt (__seq_eval_replace_all_rec a b u skip lent)) =
        SmtType.Seq T := by
  intro a b u skip lent
  induction a, b, u, skip, lent using __seq_eval_replace_all_rec.induct with
  | case1 a u skip lent =>
      intro T _hATy _hBTy _hUTy _hSkipTy _hLentTy hNe
      simp [__seq_eval_replace_all_rec] at hNe
  | case2 a b skip lent hb =>
      intro T _hATy _hBTy _hUTy _hSkipTy _hLentTy hNe
      simp [__seq_eval_replace_all_rec] at hNe
  | case3 a b u lent hb hu =>
      intro T _hATy _hBTy _hUTy _hSkipTy _hLentTy hNe
      simp [__seq_eval_replace_all_rec] at hNe
  | case4 a b u skip hb hu hskip =>
      intro T _hATy _hBTy _hUTy _hSkipTy _hLentTy hNe
      simp [__seq_eval_replace_all_rec] at hNe
  | case5 U b u skip lent hb hu hskip hlent =>
      intro T hATy _hBTy _hUTy _hSkipTy _hLentTy _hNe
      simpa [__seq_eval_replace_all_rec] using hATy
  | case6 s1 s2 b u lent hb hu hlent ihSkip ihZero =>
      intro T hATy hBTy hUTy _hSkipTy hLentTy hNe
      let whole := mkConcat s1 s2
      let nextMatch :=
        __seq_eval_replace_all_rec s2 b u
          (__eo_add lent (Term.Numeral (-1 : native_Int))) lent
      let nextNo :=
        __seq_eval_replace_all_rec s2 b u (Term.Numeral 0) lent
      have hWholeTy :
          __smtx_typeof (__eo_to_smt (mkConcat s1 s2)) =
            SmtType.Seq T := by
        simpa [whole, mkConcat] using hATy
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type s1 s2 T hWholeTy
      have hIteNe :
          __eo_ite (__seq_is_prefix b whole)
              (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
              (__eo_cons (Term.UOp UserOp.str_concat) s1 nextNo) ≠
            Term.Stuck := by
        simpa [__seq_eval_replace_all_rec, whole, nextMatch, nextNo] using
          hNe
      rw [show
          __seq_eval_replace_all_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
              b u (Term.Numeral 0) lent =
            __eo_ite (__seq_is_prefix b whole)
              (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
              (__eo_cons (Term.UOp UserOp.str_concat) s1 nextNo) by
        simp [__seq_eval_replace_all_rec, whole, nextMatch, nextNo]]
      rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix b whole)
          (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
          (__eo_cons (Term.UOp UserOp.str_concat) s1 nextNo)
          hIteNe with hCond | hCond
      · have hConcatNe :
            __eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch ≠
              Term.Stuck := by
          simpa [hCond, eo_ite_true] using hIteNe
        have hConcatLists :=
          eo_list_concat_str_concat_lists_of_ne_stuck u nextMatch hConcatNe
        have hNextNe : nextMatch ≠ Term.Stuck :=
          term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
            nextMatch hConcatLists.2
        have hMinusTy :
            __smtx_typeof
                (__eo_to_smt (Term.Numeral (-1 : native_Int))) =
              SmtType.Int := by
          change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) =
            SmtType.Int
          rw [__smtx_typeof.eq_2]
        have hAddNe :
            __eo_add lent (Term.Numeral (-1 : native_Int)) ≠
              Term.Stuck :=
          seq_eval_replace_all_rec_skip_ne_stuck_of_ne_stuck s2 b u
            (__eo_add lent (Term.Numeral (-1 : native_Int))) lent
            (by simpa [nextMatch] using hNextNe)
        have hAddTy :
            __smtx_typeof
                (__eo_to_smt
                  (__eo_add lent (Term.Numeral (-1 : native_Int)))) =
              SmtType.Int := by
          rcases eo_add_int_args_numerals_of_ne_stuck lent
              (Term.Numeral (-1 : native_Int)) hLentTy hMinusTy hAddNe with
            ⟨i, j, hLentEq, hMinusEq, hAddEq⟩
          rw [hAddEq]
          change __smtx_typeof (SmtTerm.Numeral (native_zplus i j)) =
            SmtType.Int
          rw [__smtx_typeof.eq_2]
        have hNextTy :
            __smtx_typeof (__eo_to_smt nextMatch) = SmtType.Seq T := by
          simpa [nextMatch] using
            ihSkip T hTailTy hBTy hUTy hAddTy hLentTy
              (by simpa [nextMatch] using hNextNe)
        have hConcatTy :
            __smtx_typeof
                (__eo_to_smt
                  (__eo_list_concat (Term.UOp UserOp.str_concat) u
                    nextMatch)) =
              SmtType.Seq T :=
          smt_typeof_list_concat_str_concat_of_seq u nextMatch T
            hUTy hNextTy hConcatNe
        rw [hCond, eo_ite_true]
        exact hConcatTy
      · have hConsNe :
            __eo_cons (Term.UOp UserOp.str_concat) s1 nextNo ≠
              Term.Stuck := by
          simpa [hCond, eo_ite_false] using hIteNe
        have hNextList :
            __eo_is_list (Term.UOp UserOp.str_concat) nextNo =
              Term.Boolean true := by
          change __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat) nextNo)
              (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                nextNo) ≠
            Term.Stuck at hConsNe
          exact eo_requires_eq_of_ne_stuck
            (__eo_is_list (Term.UOp UserOp.str_concat) nextNo)
            (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              nextNo) hConsNe
        have hNextNe : nextNo ≠ Term.Stuck :=
          term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
            nextNo hNextList
        have hZeroTy :
            __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
          change __smtx_typeof (SmtTerm.Numeral (0 : native_Int)) =
            SmtType.Int
          rw [__smtx_typeof.eq_2]
        have hNextTy :
            __smtx_typeof (__eo_to_smt nextNo) = SmtType.Seq T := by
          simpa [nextNo] using
            ihZero T hTailTy hBTy hUTy hZeroTy hLentTy
              (by simpa [nextNo] using hNextNe)
        have hConsTy :
            __smtx_typeof
                (__eo_to_smt
                  (__eo_cons (Term.UOp UserOp.str_concat) s1 nextNo)) =
              SmtType.Seq T :=
          smt_typeof_eo_cons_str_concat_of_seq s1 nextNo T
            hHeadTy hNextTy (by simpa [nextNo] using hConsNe)
        rw [hCond, eo_ite_false]
        exact hConsTy
  | case7 s1 s2 b u skip lent hb hu hskip hlent hSkipNeZero ih =>
      intro T hATy hBTy hUTy hSkipTy hLentTy hNe
      let next :=
        __seq_eval_replace_all_rec s2 b u
          (__eo_add skip (Term.Numeral (-1 : native_Int))) lent
      have hNextNe : next ≠ Term.Stuck := by
        simpa [__seq_eval_replace_all_rec, next] using hNe
      have hWholeTy :
          __smtx_typeof (__eo_to_smt (mkConcat s1 s2)) =
            SmtType.Seq T := by
        simpa [mkConcat] using hATy
      obtain ⟨_hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type s1 s2 T hWholeTy
      have hMinusTy :
          __smtx_typeof
              (__eo_to_smt (Term.Numeral (-1 : native_Int))) =
            SmtType.Int := by
        change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) =
          SmtType.Int
        rw [__smtx_typeof.eq_2]
      have hAddNe :
          __eo_add skip (Term.Numeral (-1 : native_Int)) ≠ Term.Stuck :=
        seq_eval_replace_all_rec_skip_ne_stuck_of_ne_stuck s2 b u
          (__eo_add skip (Term.Numeral (-1 : native_Int))) lent
          (by simpa [next] using hNextNe)
      have hAddTy :
          __smtx_typeof
              (__eo_to_smt
                (__eo_add skip (Term.Numeral (-1 : native_Int)))) =
            SmtType.Int := by
        rcases eo_add_int_args_numerals_of_ne_stuck skip
            (Term.Numeral (-1 : native_Int)) hSkipTy hMinusTy hAddNe with
          ⟨i, j, hSkipEq, hMinusEq, hAddEq⟩
        rw [hAddEq]
        change __smtx_typeof (SmtTerm.Numeral (native_zplus i j)) =
          SmtType.Int
        rw [__smtx_typeof.eq_2]
      simpa [__seq_eval_replace_all_rec, next] using
        ih T hTailTy hBTy hUTy hAddTy hLentTy
          (by simpa [next] using hNextNe)
  | case8 a b u skip lent hb hu hskip hlent hNotEmpty hNotConcatZero
      hNotConcat =>
      intro T _hATy _hBTy _hUTy _hSkipTy _hLentTy hNe
      simp [__seq_eval_replace_all_rec] at hNe

private theorem smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
    (M : SmtModel) (hM : model_wf M)
    (l u a : Term) (T : SmtType) (i e : native_Int)
    (hL : l = Term.Numeral i)
    (hU : u = Term.Numeral e)
    (hEndNonneg : 0 <= e)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hSubseqNe : __seq_subsequence_rec l u a ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__seq_subsequence_rec l u a)))
      (__smtx_model_eval_str_substr
        (__smtx_model_eval M (__eo_to_smt a))
        (SmtValue.Numeral i) (SmtValue.Numeral (e - i))) := by
  induction l, u, a using __seq_subsequence_rec.induct generalizing T i e with
  | case1 t x =>
      simp [__seq_subsequence_rec] at hSubseqNe
  | case2 t x hx =>
      simp [__seq_subsequence_rec] at hSubseqNe
  | case3 x y hx hy =>
      simp [__seq_subsequence_rec] at hSubseqNe
  | case4 l u U hl hu =>
      have hEmptyEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.UOp1 UserOp1.seq_empty
                  (Term.Apply (Term.UOp UserOp.Seq) U))) =
            SmtValue.Seq (SmtSeq.empty T) :=
        smtx_model_eval_seq_empty_term_of_type M
          (Term.Apply (Term.UOp UserOp.Seq) U) T hATy
      have hSubseqEq :
          __seq_subsequence_rec l u
              (Term.UOp1 UserOp1.seq_empty
                (Term.Apply (Term.UOp UserOp.Seq) U)) =
            Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) U) := by
        simp [__seq_subsequence_rec]
      rw [hSubseqEq, hEmptyEval]
      unfold RuleProofs.smt_value_rel
      simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq, native_unpack_seq, native_pack_seq,
        native_seq_extract_nil, __smtx_elem_typeof_seq_value]
  | case5 l t hl ht hNotEmpty =>
      injection hU with hE
      subst e
      rcases seq_eval_of_seq_type M hM t T hATy with ⟨sa, hAEval⟩
      have hSaTy : __smtx_typeof_seq_value sa = SmtType.Seq T :=
        smt_typeof_seq_value_of_eval_seq M hM t T sa hATy hAEval
      have hElem : __smtx_elem_typeof_seq_value sa = T :=
        elem_typeof_seq_value_of_typeof_seq_value hSaTy
      have hEmptyEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.UOp1 UserOp1.seq_empty (__eo_typeof t))) =
            SmtValue.Seq (SmtSeq.empty T) :=
        smtx_model_eval_raw_seq_empty_typeof M t T hATy
      have hSubseqEq :
          __seq_subsequence_rec l (Term.Numeral 0) t =
            Term.UOp1 UserOp1.seq_empty (__eo_typeof t) := by
        simp [__seq_subsequence_rec]
      rw [hSubseqEq, hEmptyEval, hAEval]
      unfold RuleProofs.smt_value_rel
      have hExtract :
          native_seq_extract (native_unpack_seq sa) i (-i) = [] := by
        apply native_seq_extract_empty_of_end_nonpos
        rw [Int.add_right_neg]
        exact Int.le_refl 0
      simp [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
        native_veq, hElem]
      rw [hExtract]
      rfl
  | case6 u elem ts hu hUNeZero ih =>
      injection hL with hi
      subst i
      subst u
      have hEPos : 0 < e := by
        have hENe : e ≠ 0 := by
          intro hE
          subst e
          exact hUNeZero rfl
        exact Int.lt_of_not_ge (by
          intro hLe
          exact hENe (Int.le_antisymm hLe hEndNonneg))
      have hRecU :
          __eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int)) =
            Term.Numeral (e - 1) := by
        simp [__eo_add, native_zplus, SmtEval.native_zplus]
        rw [Int.sub_eq_add_neg]
      have hRecEnd : 0 <= e - 1 := by
        have hOneLe : (1 : Int) <= e := Int.add_one_le_iff.mpr hEPos
        exact Int.sub_nonneg.mpr hOneLe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) elem
      let subseq :=
        __seq_subsequence_rec (Term.Numeral 0)
          (__eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int))) ts
      have hFullNe :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq ≠
            Term.Stuck := by
        simpa [__seq_subsequence_rec, head, subseq] using hSubseqNe
      have hSubseqNe : subseq ≠ Term.Stuck :=
        eo_mk_apply_arg_ne_stuck_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hATy)
      have hRecRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt subseq))
            (__smtx_model_eval_str_substr
              (__smtx_model_eval M (__eo_to_smt ts))
              (SmtValue.Numeral 0) (SmtValue.Numeral (e - 1))) := by
        simpa [subseq, hRecU] using
          ih T 0 (e - 1) rfl hRecU hRecEnd hTailTy hSubseqNe
      have hRecTy :
          __smtx_typeof (__eo_to_smt subseq) = SmtType.Seq T :=
        smt_typeof_seq_subsequence_rec_of_seq
          (Term.Numeral 0)
          (__eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int))) ts T
          hTailTy hSubseqNe
      rcases seq_eval_of_seq_type M hM subseq T hRecTy with
        ⟨srec, hRecEval⟩
      rcases seq_eval_of_seq_type M hM ts T hTailTy with
        ⟨stail, hTailEval⟩
      obtain ⟨shead, hHeadEvalRaw, hHeadUnpRaw⟩ :=
        RuleProofs.eval_seqUnitAtom M elem
      have hHeadEval :
          __smtx_model_eval M (__eo_to_smt head) = SmtValue.Seq shead := by
        simpa [head] using hHeadEvalRaw
      have hHeadUnp :
          native_unpack_seq shead = [RuleProofs.seqElemVal M head] := by
        simpa [head] using hHeadUnpRaw
      have hApplyEq :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq =
            mkConcat head subseq :=
        eo_mk_apply_eq_apply_of_ne_stuck
          (Term.Apply (Term.UOp UserOp.str_concat) head) subseq hFullNe
      have hHeadValTy :=
        smt_model_eval_preserves_type M hM (__eo_to_smt head)
          (SmtType.Seq T) hHeadTy (seq_ne_none T) (type_inhabited_seq T)
      have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
        simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
      have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
        elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
      have hTailValTy :=
        smt_model_eval_preserves_type M hM (__eo_to_smt ts)
          (SmtType.Seq T) hTailTy (seq_ne_none T) (type_inhabited_seq T)
      have hTailSeqTy : __smtx_typeof_seq_value stail = SmtType.Seq T := by
        simpa [hTailEval, __smtx_typeof_value] using hTailValTy
      have hTailElem : __smtx_elem_typeof_seq_value stail = T :=
        elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
      have hRecEq :
          srec =
            native_pack_seq T
              (native_seq_extract (native_unpack_seq stail) 0 (e - 1)) := by
        unfold RuleProofs.smt_value_rel at hRecRel
        rw [hRecEval, hTailEval] at hRecRel
        simpa [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
          native_veq, hTailElem] using hRecRel
      have hOrigEval :
          __smtx_model_eval M (__eo_to_smt (mkConcat head ts)) =
            SmtValue.Seq
              (native_pack_seq T
                (RuleProofs.seqElemVal M head :: native_unpack_seq stail)) := by
        rw [smtx_model_eval_str_concat_term_eq, hHeadEval, hTailEval]
        simp [__smtx_model_eval_str_concat, native_seq_concat, hHeadElem,
          hHeadUnp]
      have hConcatEval :
          __smtx_model_eval_str_concat (SmtValue.Seq shead)
              (SmtValue.Seq srec) =
            SmtValue.Seq
              (native_pack_seq T
                (RuleProofs.seqElemVal M head ::
                  native_seq_extract (native_unpack_seq stail) 0 (e - 1))) := by
        rw [hRecEq]
        simp [__smtx_model_eval_str_concat, native_seq_concat, hHeadElem,
          hHeadUnp, Smtm.native_unpack_pack_seq]
      have hSubstrEval :
          __smtx_model_eval_str_substr
              (SmtValue.Seq
                (native_pack_seq T
                  (RuleProofs.seqElemVal M head :: native_unpack_seq stail)))
              (SmtValue.Numeral 0) (SmtValue.Numeral (e - 0)) =
            SmtValue.Seq
              (native_pack_seq T
                (RuleProofs.seqElemVal M head ::
                  native_seq_extract (native_unpack_seq stail) 0 (e - 1))) := by
        simp [__smtx_model_eval_str_substr,
          Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
          native_seq_extract_cons_zero_pos _ _ _ hEPos]
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__seq_subsequence_rec (Term.Numeral 0) (Term.Numeral e)
              (mkConcat head ts))))
        (__smtx_model_eval_str_substr
          (__smtx_model_eval M (__eo_to_smt (mkConcat head ts)))
          (SmtValue.Numeral 0) (SmtValue.Numeral (e - 0)))
      rw [show __seq_subsequence_rec (Term.Numeral 0) (Term.Numeral e)
          (mkConcat head ts) =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
              subseq by
        simp [__seq_subsequence_rec, head, subseq]]
      rw [hApplyEq, smtx_model_eval_str_concat_term_eq, hHeadEval, hRecEval,
        hOrigEval, hConcatEval, hSubstrEval]
      exact RuleProofs.smt_value_rel_refl _
  | case7 l u elem ts hl hu hUNeZero hLNeZero ih =>
      subst l
      subst u
      have hINe : i ≠ 0 := by
        intro hI
        subst i
        exact hLNeZero rfl
      have hENe : e ≠ 0 := by
        intro hE
        subst e
        exact hUNeZero rfl
      have hEPos : 0 < e :=
        Int.lt_of_not_ge (by
          intro hLe
          exact hENe (Int.le_antisymm hLe hEndNonneg))
      have hRecL :
          __eo_add (Term.Numeral i) (Term.Numeral (-1 : native_Int)) =
            Term.Numeral (i - 1) := by
        simp [__eo_add, native_zplus, SmtEval.native_zplus]
        rw [Int.sub_eq_add_neg]
      have hRecU :
          __eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int)) =
            Term.Numeral (e - 1) := by
        simp [__eo_add, native_zplus, SmtEval.native_zplus]
        rw [Int.sub_eq_add_neg]
      have hRecEnd : 0 <= e - 1 := by
        have hOneLe : (1 : Int) <= e := Int.add_one_le_iff.mpr hEPos
        exact Int.sub_nonneg.mpr hOneLe
      have hLenEq : (e - 1) - (i - 1) = e - i := by
        exact int_sub_one_sub_sub_one e i
      let head := Term.Apply (Term.UOp UserOp.seq_unit) elem
      let subseq :=
        __seq_subsequence_rec
          (__eo_add (Term.Numeral i) (Term.Numeral (-1 : native_Int)))
          (__eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int))) ts
      have hSubseqTailNe : subseq ≠ Term.Stuck := by
        simpa [__seq_subsequence_rec, head, subseq, hINe, hENe] using
          hSubseqNe
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head ts T
          (by simpa [head, mkConcat] using hATy)
      have hRecRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt subseq))
            (__smtx_model_eval_str_substr
              (__smtx_model_eval M (__eo_to_smt ts))
              (SmtValue.Numeral (i - 1)) (SmtValue.Numeral (e - i))) := by
        simpa [subseq, hRecL, hRecU, hLenEq] using
          ih T (i - 1) (e - 1) hRecL hRecU hRecEnd hTailTy
            hSubseqTailNe
      have hRecTy :
          __smtx_typeof (__eo_to_smt subseq) = SmtType.Seq T :=
        smt_typeof_seq_subsequence_rec_of_seq
          (__eo_add (Term.Numeral i) (Term.Numeral (-1 : native_Int)))
          (__eo_add (Term.Numeral e) (Term.Numeral (-1 : native_Int))) ts T
          hTailTy hSubseqTailNe
      rcases seq_eval_of_seq_type M hM subseq T hRecTy with
        ⟨srec, hRecEval⟩
      rcases seq_eval_of_seq_type M hM ts T hTailTy with
        ⟨stail, hTailEval⟩
      obtain ⟨shead, hHeadEvalRaw, hHeadUnpRaw⟩ :=
        RuleProofs.eval_seqUnitAtom M elem
      have hHeadEval :
          __smtx_model_eval M (__eo_to_smt head) = SmtValue.Seq shead := by
        simpa [head] using hHeadEvalRaw
      have hHeadUnp :
          native_unpack_seq shead = [RuleProofs.seqElemVal M head] := by
        simpa [head] using hHeadUnpRaw
      have hHeadValTy :=
        smt_model_eval_preserves_type M hM (__eo_to_smt head)
          (SmtType.Seq T) hHeadTy (seq_ne_none T) (type_inhabited_seq T)
      have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
        simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
      have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
        elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
      have hTailValTy :=
        smt_model_eval_preserves_type M hM (__eo_to_smt ts)
          (SmtType.Seq T) hTailTy (seq_ne_none T) (type_inhabited_seq T)
      have hTailSeqTy : __smtx_typeof_seq_value stail = SmtType.Seq T := by
        simpa [hTailEval, __smtx_typeof_value] using hTailValTy
      have hTailElem : __smtx_elem_typeof_seq_value stail = T :=
        elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
      have hRecEq :
          srec =
            native_pack_seq T
              (native_seq_extract (native_unpack_seq stail) (i - 1)
                (e - i)) := by
        unfold RuleProofs.smt_value_rel at hRecRel
        rw [hRecEval, hTailEval] at hRecRel
        simpa [__smtx_model_eval_str_substr, __smtx_model_eval_eq,
          native_veq, hTailElem] using hRecRel
      have hOrigEval :
          __smtx_model_eval M (__eo_to_smt (mkConcat head ts)) =
            SmtValue.Seq
              (native_pack_seq T
                (RuleProofs.seqElemVal M head :: native_unpack_seq stail)) := by
        rw [smtx_model_eval_str_concat_term_eq, hHeadEval, hTailEval]
        simp [__smtx_model_eval_str_concat, native_seq_concat, hHeadElem,
          hHeadUnp]
      have hSubstrEval :
          __smtx_model_eval_str_substr
              (SmtValue.Seq
                (native_pack_seq T
                  (RuleProofs.seqElemVal M head :: native_unpack_seq stail)))
              (SmtValue.Numeral i) (SmtValue.Numeral (e - i)) =
            SmtValue.Seq
              (native_pack_seq T
                (native_seq_extract (native_unpack_seq stail) (i - 1)
                  (e - i))) := by
        simp [__smtx_model_eval_str_substr,
          Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
          native_seq_extract_cons_nonzero _ _ _ _ hINe]
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__seq_subsequence_rec (Term.Numeral i) (Term.Numeral e)
              (mkConcat head ts))))
        (__smtx_model_eval_str_substr
          (__smtx_model_eval M (__eo_to_smt (mkConcat head ts)))
          (SmtValue.Numeral i) (SmtValue.Numeral (e - i)))
      rw [show __seq_subsequence_rec (Term.Numeral i) (Term.Numeral e)
          (mkConcat head ts) = subseq by
        simp [__seq_subsequence_rec, head, subseq]]
      rw [hRecEval, hOrigEval, hSubstrEval, hRecEq]
      exact RuleProofs.smt_value_rel_refl _
  | case8 t x y hx hy hyZero ht hNotEmpty hNotZeroConcat hNotConcat =>
      simp [__seq_subsequence_rec] at hSubseqNe

private theorem native_seq_prefix_eq_take_eq_true
    (xs ys : List SmtValue)
    (h : ys.take xs.length = xs) :
    native_seq_prefix_eq xs ys = true := by
  rw [RuleProofs.native_seq_prefix_eq_iff]
  exact ⟨ys.drop xs.length, by
    calc
      ys = ys.take xs.length ++ ys.drop xs.length :=
        (List.take_append_drop xs.length ys).symm
      _ = xs ++ ys.drop xs.length := by rw [h]⟩

private theorem native_seq_prefix_eq_append_left_same
    (pre xs ys : List SmtValue) :
    native_seq_prefix_eq (pre ++ xs) (pre ++ ys) =
      native_seq_prefix_eq xs ys := by
  induction pre with
  | nil => rfl
  | cons p ps ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_prefix_eq_cons_cons_false_of_veq_false
    {x y : SmtValue} {xs ys : List SmtValue}
    (h : native_veq x y = false) :
    native_seq_prefix_eq (x :: xs) (y :: ys) = false := by
  simp [native_seq_prefix_eq, h]

private theorem seq_is_prefix_left_ne_stuck_of_ne_stuck (a b : Term)
    (h : __seq_is_prefix a b ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  simp [__seq_is_prefix] at h

private theorem seq_is_prefix_right_ne_stuck_of_ne_stuck (a b : Term)
    (h : __seq_is_prefix a b ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> simp [__seq_is_prefix] at h

private theorem seq_element_of_unit_eq_of_ne_stuck (x : Term)
    (h : __seq_element_of_unit x ≠ Term.Stuck) :
    ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e ∧
      __seq_element_of_unit x = e := by
  cases x <;> simp [__seq_element_of_unit] at h ⊢
  case Apply f e =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

private theorem eo_list_nth_eq_rec_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_list_nth f a n = __eo_list_nth_rec a n := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_eq_result_of_ne_stuck (__eo_is_list f a)
    (Term.Boolean true) (__eo_list_nth_rec a n) h

private theorem eo_list_nth_is_list_true_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_is_list f a = Term.Boolean true := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_nth_rec a n) h

private theorem eo_list_nth_rec_ne_stuck_of_ne_stuck (f a n : Term)
    (h : __eo_list_nth f a n ≠ Term.Stuck) :
    __eo_list_nth_rec a n ≠ Term.Stuck := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a n) ≠ Term.Stuck at h
  exact eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a)
    (Term.Boolean true) (__eo_list_nth_rec a n) h

private theorem eo_is_list_str_concat_cons_fun_eq (g x y : Term)
    (h :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) =
        Term.Boolean true) :
    g = Term.UOp UserOp.str_concat := by
  cases g <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_requires,
      __eo_is_ok, native_teq, native_ite, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp at h ⊢

private theorem eo_get_nil_rec_stuck_of_is_list_false (f x : Term)
    (h : __eo_is_list f x = Term.Boolean false) :
    __eo_get_nil_rec f x = Term.Stuck := by
  cases f <;> cases x <;>
    simp [__eo_is_list, __eo_is_ok, native_teq, SmtEval.native_not] at h ⊢
  all_goals
    exact h

private theorem eo_is_list_str_concat_cons_false_of_tail_false
    (x y : Term)
    (hTail :
      __eo_is_list (Term.UOp UserOp.str_concat) y =
        Term.Boolean false) :
    __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x y) =
      Term.Boolean false := by
  have hRec :=
    eo_get_nil_rec_stuck_of_is_list_false
      (Term.UOp UserOp.str_concat) y hTail
  simp [__eo_is_list, __eo_get_nil_rec, hRec, __eo_requires,
    __eo_is_ok, native_teq, native_ite, SmtEval.native_ite,
    SmtEval.native_not]

private theorem list_nth_rec_non_cons_stuck (x i : Term)
    (hNonCons :
      ∀ f a b : Term, x = Term.Apply (Term.Apply f a) b -> False) :
    __eo_list_nth_rec x i = Term.Stuck := by
  by_cases hi : i = Term.Stuck
  · subst i
    exact __eo_list_nth_rec.eq_1 x
  · exact __eo_list_nth_rec.eq_4 x i hNonCons hi
      (by
        intro f a b hx _hi0
        exact hNonCons f a b hx)

private theorem list_nth_rec_stuck_left (i : Term) :
    __eo_list_nth_rec Term.Stuck i = Term.Stuck :=
  list_nth_rec_non_cons_stuck Term.Stuck i
    (by
      intro f a b h
      cases h)

private theorem list_nth_rec_eo_nil_str_concat_stuck (A i : Term) :
    __eo_list_nth_rec (__eo_nil (Term.UOp UserOp.str_concat) A) i =
      Term.Stuck := by
  cases A <;> try
    (simpa [__eo_nil, __eo_nil_str_concat] using
      list_nth_rec_stuck_left i)
  case Apply f x =>
    cases f <;> try
      (simpa [__eo_nil, __eo_nil_str_concat] using
        list_nth_rec_stuck_left i)
    case UOp op =>
      cases op <;> try
        (simpa [__eo_nil, __eo_nil_str_concat] using
          list_nth_rec_stuck_left i)
      case Seq =>
        cases x <;>
          simp [__eo_nil, __eo_nil_str_concat, __seq_empty]
        case UOp op =>
          cases op <;>
            simp
          case Char =>
            exact list_nth_rec_non_cons_stuck (Term.String []) i
              (by
                intro f a b h
                cases h)
          all_goals
            exact list_nth_rec_non_cons_stuck
              _ i
              (by
                intro f a b h
                cases h)
        all_goals
          first
          | exact list_nth_rec_non_cons_stuck (Term.String []) i
              (by
                intro f a b h
                cases h)
          | exact list_nth_rec_non_cons_stuck
              _ i
              (by
                intro f a b h
                cases h)

private theorem list_nth_rec_intro_seqUnit_concat_eq_unit_tail_list
    (head tail n e : Term)
    (hTailNe : tail ≠ Term.Stuck)
    (hNth :
      __eo_list_nth_rec
          (__str_nary_intro
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail)) n =
        Term.Apply (Term.UOp UserOp.seq_unit) e) :
    __eo_is_list (Term.UOp UserOp.str_concat) tail =
      Term.Boolean true := by
  rcases eo_is_list_boolean_of_ne_stuck (Term.UOp UserOp.str_concat)
      tail (by decide) hTailNe with
    ⟨tailList, hTailList⟩
  cases tailList
  · have hConcatList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail) =
          Term.Boolean false :=
      eo_is_list_str_concat_cons_false_of_tail_false
        (Term.Apply (Term.UOp UserOp.seq_unit) head) tail
        (by simpa using hTailList)
    let nil :=
      __eo_nil (Term.UOp UserOp.str_concat)
        (__eo_typeof
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail))
    cases hNilList :
        __eo_is_list (Term.UOp UserOp.str_concat) nil with
    | Boolean nilList =>
        cases nilList
        · have hIntro :
              __str_nary_intro
                  (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail) =
                Term.Stuck := by
            simp [__str_nary_intro, __eo_list_singleton_intro, hConcatList,
              eo_ite_false, nil, hNilList, __eo_requires, native_teq,
              native_ite, SmtEval.native_ite]
          rw [hIntro] at hNth
          cases n <;> simp [__eo_list_nth_rec] at hNth
        · have hMk :
              __eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat)
                    (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head)
                      tail))
                  nil =
                mkConcat
                  (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head)
                    tail)
                  nil := by
            have hNilNe : nil ≠ Term.Stuck := by
              intro hNilStuck
              rw [hNilStuck] at hNilList
              simp [__eo_is_list] at hNilList
            have hMkNe :
                __eo_mk_apply
                    (Term.Apply (Term.UOp UserOp.str_concat)
                      (mkConcat
                        (Term.Apply (Term.UOp UserOp.seq_unit) head) tail))
                    nil ≠ Term.Stuck := by
              cases hNilCases : nil <;>
                simp [__eo_mk_apply, hNilCases] at hNilNe ⊢
            exact eo_mk_apply_eq_apply_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat)
                (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head)
                  tail))
              nil hMkNe
          have hIntro :
              __str_nary_intro
                  (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail) =
                mkConcat
                  (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail)
                  nil := by
            simp [__str_nary_intro, __eo_list_singleton_intro, hConcatList,
              eo_ite_false, nil, hNilList, __eo_requires, hMk, native_teq,
              native_ite, SmtEval.native_ite, SmtEval.native_not]
          rw [hIntro] at hNth
          cases n <;> simp [__eo_list_nth_rec, __eo_add, mkConcat] at hNth
          case Numeral i =>
            by_cases hi : i = 0 <;>
              simp [__eo_list_nth_rec, __eo_add, hi] at hNth
            rw [list_nth_rec_eo_nil_str_concat_stuck
              (__eo_typeof
                (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head)
                  tail))
              (Term.Numeral (native_zplus i (-1)))] at hNth
            simp at hNth
    | _ =>
        have hIntro :
            __str_nary_intro
                (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head) tail) =
              Term.Stuck := by
          simp [__str_nary_intro, __eo_list_singleton_intro, hConcatList,
            eo_ite_false, nil, hNilList, __eo_requires, native_teq,
            native_ite, SmtEval.native_ite]
        rw [hIntro] at hNth
        cases n <;> simp [__eo_list_nth_rec] at hNth
  · simpa using hTailList

private theorem smt_typeof_list_nth_rec_str_concat_of_seq :
    ∀ a n T,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __eo_list_nth_rec a n ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_list_nth_rec a n)) =
        SmtType.Seq T := by
  intro a n
  induction a, n using __eo_list_nth_rec.induct with
  | case1 n =>
      intro T _hList _hTy hNe
      simp [__eo_list_nth_rec] at hNe
  | case2 f x y =>
      intro T hList hTy _hNe
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      exact (strConcat_args_of_seq_type x y T
        (by simpa [mkConcat] using hTy)).1
  | case3 f x y n _hnStuck hnZero ih =>
      intro T hList hTy hNe
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          x y (by simpa [mkConcat] using hList)
      have hTailTy :
          __smtx_typeof (__eo_to_smt y) = SmtType.Seq T :=
        (strConcat_args_of_seq_type x y T
          (by simpa [mkConcat] using hTy)).2
      have hTailNe :
          __eo_list_nth_rec y (__eo_add n (Term.Numeral (-1 : native_Int))) ≠
            Term.Stuck := by
        simpa [__eo_list_nth_rec, hnZero] using hNe
      simpa [__eo_list_nth_rec, hnZero] using
        ih T hTailList hTailTy hTailNe
  | case4 t x hxStuck hNotZero hNotCons =>
      intro T hList hTy hNe
      simp [__eo_list_nth_rec] at hNe

private theorem smt_value_rel_seq_nth_left_congr
    (M : SmtModel) (hM : model_wf M)
    (x y n : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))) :
    RuleProofs.smt_value_rel
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt n)))
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt n))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hnValTy := smt_model_eval_preserves_type M hM (__eo_to_smt n)
    SmtType.Int hnTy (by simp) type_inhabited_int
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases int_value_canonical hnValTy with ⟨i, hnEval⟩
  have hSeqEq : sx = sy := by
    unfold RuleProofs.smt_value_rel at hRel
    rw [hxEval, hyEval] at hRel
    simpa [__smtx_model_eval_eq, native_veq] using hRel
  subst sy
  rw [hxEval, hyEval, hnEval]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_seq_nth M (SmtValue.Seq sx) (SmtValue.Numeral i))

private theorem smtx_model_eval_seq_unit_term (M : SmtModel) (e : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
          (SmtSeq.empty
            (__smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt e))))) := by
  change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
    SmtValue.Seq
      (SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
        (SmtSeq.empty
          (__smtx_typeof_value
            (__smtx_model_eval M (__eo_to_smt e)))))
  simp [__smtx_model_eval]

private theorem smtx_model_eval_seq_nth_term
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_nth x y) =
      __smtx_seq_nth M (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem str_value_len_concat_head_seq_unit (x y : Term)
    (h : __str_value_len (mkConcat x y) ≠ Term.Stuck) :
    ∃ e, x = Term.Apply (Term.UOp UserOp.seq_unit) e := by
  rcases str_value_len_numeral_of_ne_stuck (mkConcat x y) h with ⟨n, hn⟩
  rcases RuleProofs.value_len_numeral_cases (mkConcat x y) n hn with
      ⟨w, hw⟩ | ⟨e, ss, hcons⟩ | ⟨U, hU⟩ | ⟨e, hUnit⟩
  · cases hw
  · injection hcons with hx _hy
    injection hx with _ hx'
    exact ⟨e, hx'⟩
  · cases hU
  · cases hUnit

private theorem str_value_len_concat_tail_ne_stuck (e tail : Term)
    (h :
      __str_value_len
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) ≠
        Term.Stuck) :
    __str_value_len tail ≠ Term.Stuck := by
  intro hTail
  rcases str_value_len_numeral_of_ne_stuck
      (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail) h with
    ⟨n, hLen⟩
  rcases RuleProofs.value_len_tail_numeral_of_concat_seqUnit e tail n hLen with
    ⟨m, hTailLen⟩
  rw [hTail] at hTailLen
  cases hTailLen

private theorem smt_value_rel_list_nth_rec_ssm_of_value_len
    (M : SmtModel) (hM : model_wf M) :
    ∀ a n e T sx i d,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __str_value_len a ≠ Term.Stuck ->
      __eo_list_nth_rec a n = Term.Apply (Term.UOp UserOp.seq_unit) e ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral i ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt e))
        (__smtx_seq_value_nth sx i d) := by
  intro a n
  induction a, n using __eo_list_nth_rec.induct with
  | case1 n =>
      intro e T sx i d _hList _hTy _hLen hNth _hEvalA _hEvalN
      simp [__eo_list_nth_rec] at hNth
  | case2 f x y =>
      intro e T sx i d hList hTy _hLen hNth hEvalA hEvalN
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      have hx : x = Term.Apply (Term.UOp UserOp.seq_unit) e := by
        simpa [__eo_list_nth_rec] using hNth
      subst x
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type (Term.Apply (Term.UOp UserOp.seq_unit) e)
          y T (by simpa [mkConcat] using hTy)
      rcases seq_eval_of_seq_type M hM y T hTailTy with ⟨sy, hTailEval⟩
      have hsx :
          sx =
            native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e)))
              (__smtx_model_eval M (__eo_to_smt e) ::
                native_unpack_seq sy) := by
        rw [smtx_model_eval_str_concat_term_eq, hTailEval] at hEvalA
        rw [smtx_model_eval_seq_unit_term] at hEvalA
        simp [__smtx_model_eval_str_concat, native_seq_concat,
          native_unpack_seq, __smtx_elem_typeof_seq_value] at hEvalA
        exact hEvalA.symm
      change __smtx_model_eval M (SmtTerm.Numeral 0) =
        SmtValue.Numeral i at hEvalN
      rw [__smtx_model_eval.eq_2] at hEvalN
      injection hEvalN with hi
      subst i
      rw [hsx]
      simp [__smtx_seq_value_nth, native_pack_seq,
        RuleProofs.smt_value_rel_refl]
  | case3 f x y n _hnStuck hnZero ih =>
      intro e T sx i d hList hTy hLen hNth hEvalA hEvalN
      have hF : f = Term.UOp UserOp.str_concat :=
        eo_is_list_str_concat_cons_fun_eq f x y hList
      subst f
      rcases str_value_len_concat_head_seq_unit x y
          (by simpa [mkConcat] using hLen) with ⟨e0, hx⟩
      subst x
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y
          (by simpa [mkConcat] using hList)
      have hTailTy :
          __smtx_typeof (__eo_to_smt y) = SmtType.Seq T :=
        (strConcat_args_of_seq_type
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y T
          (by simpa [mkConcat] using hTy)).2
      have hTailLen : __str_value_len y ≠ Term.Stuck :=
        str_value_len_concat_tail_ne_stuck e0 y
          (by simpa [mkConcat] using hLen)
      have hTailNth :
          __eo_list_nth_rec y (__eo_add n (Term.Numeral (-1 : native_Int))) =
            Term.Apply (Term.UOp UserOp.seq_unit) e := by
        simpa [__eo_list_nth_rec, hnZero] using hNth
      rcases seq_eval_of_seq_type M hM y T hTailTy with ⟨sy, hTailEval⟩
      have hTailSeqTy :
          __smtx_typeof_seq_value sy = SmtType.Seq T :=
        smt_typeof_seq_value_of_eval_seq M hM y T sy hTailTy hTailEval
      have hTailElem : __smtx_elem_typeof_seq_value sy = T :=
        elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
      have hHeadTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e0)) =
            SmtType.Seq T :=
        (strConcat_args_of_seq_type
          (Term.Apply (Term.UOp UserOp.seq_unit) e0) y T
          (by simpa [mkConcat] using hTy)).1
      have hE0TyInfo :=
        seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e0) (A := T) hHeadTy
      have hE0ValTy :
          __smtx_typeof_value
              (__smtx_model_eval M (__eo_to_smt e0)) = T := by
        have hE0NN : term_has_non_none_type (__eo_to_smt e0) := by
          unfold term_has_non_none_type
          rw [hE0TyInfo.1]
          exact hE0TyInfo.2
        exact (smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt e0) hE0NN).trans hE0TyInfo.1
      have hPackTail :
          native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e0)))
              (native_unpack_seq sy) =
            sy := by
        rw [hE0ValTy]
        simpa [hTailElem] using native_pack_unpack_seq sy
      have hsx :
          sx =
            native_pack_seq
              (__smtx_typeof_value
                (__smtx_model_eval M (__eo_to_smt e0)))
              (__smtx_model_eval M (__eo_to_smt e0) ::
                native_unpack_seq sy) := by
        rw [smtx_model_eval_str_concat_term_eq, hTailEval] at hEvalA
        rw [smtx_model_eval_seq_unit_term] at hEvalA
        simp [__smtx_model_eval_str_concat, native_seq_concat,
          native_unpack_seq, __smtx_elem_typeof_seq_value] at hEvalA
        exact hEvalA.symm
      cases n <;>
        simp [__eo_add, __eo_list_nth_rec] at hTailNth hEvalN
      case Numeral j =>
        change __smtx_model_eval M (SmtTerm.Numeral j) =
          SmtValue.Numeral i at hEvalN
        rw [__smtx_model_eval.eq_2] at hEvalN
        injection hEvalN with hji
        subst i
        have hj0 : j ≠ 0 := by
          intro hj
          apply hnZero
          subst j
          rfl
        have hPredEval :
            __smtx_model_eval M
                (__eo_to_smt (__eo_add (Term.Numeral j)
                  (Term.Numeral (-1 : native_Int)))) =
              SmtValue.Numeral (native_zplus j (native_zneg 1)) := by
          change __smtx_model_eval M
              (SmtTerm.Numeral (native_zplus j (-1 : native_Int))) =
            SmtValue.Numeral (native_zplus j (native_zneg 1))
          rw [__smtx_model_eval.eq_2]
          rfl
        have hTailRel :=
          ih e T sy (native_zplus j (native_zneg 1)) d hTailList hTailTy
            hTailLen hTailNth hTailEval hPredEval
        rw [hsx]
        simpa [__smtx_seq_value_nth, native_pack_seq, hPackTail, hj0] using
          hTailRel
  | case4 t x hxStuck hNotZero hNotCons =>
      intro e T sx i d hList hTy hLen hNth hEvalA hEvalN
      simp [__eo_list_nth_rec] at hNth

private theorem smt_value_rel_seq_nth_list_rec_of_value_len
    (M : SmtModel) (hM : model_wf M)
    (a n e : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hLen : __str_value_len a ≠ Term.Stuck)
    (hNth :
      __eo_list_nth_rec a n = Term.Apply (Term.UOp UserOp.seq_unit) e)
    (hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt e))
      (__smtx_seq_nth M
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt n))) := by
  have haValTy := smt_model_eval_preserves_type M hM (__eo_to_smt a)
    (SmtType.Seq T) hTy (seq_ne_none T) (type_inhabited_seq T)
  have hnValTy := smt_model_eval_preserves_type M hM (__eo_to_smt n)
    SmtType.Int hnTy (by simp) type_inhabited_int
  rcases seq_value_canonical haValTy with ⟨sx, haEval⟩
  rcases int_value_canonical hnValTy with ⟨i, hnEval⟩
  rw [haEval, hnEval]
  simp [__smtx_seq_nth]
  exact smt_value_rel_list_nth_rec_ssm_of_value_len M hM a n e T sx i
    (__smtx_seq_nth_wrong M sx i (__smtx_typeof_seq_value sx))
    hList hTy hLen hNth haEval hnEval

private theorem seq_element_list_nth_seq_empty_stuck
    (U n : Term) :
    __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U)) n) =
      Term.Stuck := by
  cases n <;>
    simp [__eo_list_nth, __eo_list_nth_rec, __eo_requires,
      __eo_is_list, __eo_get_nil_rec, __eo_is_ok, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __seq_element_of_unit, native_teq,
      native_ite, SmtEval.native_not]

private theorem seq_element_list_nth_intro_seq_empty_stuck
    (U n : Term) :
    __seq_element_of_unit
        (__eo_list_nth (Term.UOp UserOp.str_concat)
          (__str_nary_intro
            (Term.UOp1 UserOp1.seq_empty
              (Term.Apply (Term.UOp UserOp.Seq) U))) n) =
      Term.Stuck := by
  simpa [__str_nary_intro, __eo_list_singleton_intro, __eo_is_list,
    __eo_get_nil_rec, __eo_is_ok, __eo_is_list_nil,
    __eo_is_list_nil_str_concat, __eo_requires, native_ite,
    SmtEval.native_ite, native_teq, native_not, SmtEval.native_not]
    using seq_element_list_nth_seq_empty_stuck U n

private theorem str_concat_unpack_of_seq_evals
    (M : SmtModel) (x y : Term) (sxy sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hxy : __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      SmtValue.Seq sxy) :
    native_unpack_seq sxy = native_unpack_seq sx ++ native_unpack_seq sy := by
  obtain ⟨sxy', hEval, hUnp⟩ :=
    RuleProofs.strConcat_unpack_eval M x y sx sy hx hy
  have hSeq : sxy = sxy' := by
    rw [hxy] at hEval
    injection hEval
  rw [hSeq]
  exact hUnp

private theorem seq_empty_uop1_unpack_nil_of_seq
    (M : SmtModel) (A : Term) (T : SmtType) (sx : SmtSeq)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq T)
    (hEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtValue.Seq sx) :
    native_unpack_seq sx = [] := by
  change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtType.Seq T at hTy
  change __smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtValue.Seq sx at hEval
  cases hA : __eo_to_smt_type A with
  | Seq U =>
      simp [__eo_to_smt_seq_empty, hA] at hTy hEval
      rw [smtx_typeof_seq_empty_term_eq] at hTy
      have hGuardNN :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) ≠
            SmtType.None := by
        rw [hTy]
        exact seq_ne_none T
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) =
            SmtType.Seq U :=
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq U) (SmtType.Seq U)
          hGuardNN
      rw [hGuard] at hTy
      injection hTy with hU
      subst U
      rw [smtx_eval_seq_empty_term_eq] at hEval
      injection hEval with hSx
      subst sx
      rfl
  | _ =>
      simp [__eo_to_smt_seq_empty, hA, TranslationProofs.smtx_typeof_none]
        at hTy

private theorem seq_unit_concat_unpack_cons
    (M : SmtModel) (hM : model_wf M)
    (e tail : Term) (T : SmtType) (sx : SmtSeq)
    (hTNN : T ≠ SmtType.None)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtType.Seq T)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)) =
        SmtValue.Seq sx) :
    ∃ rest,
      native_unpack_seq sx =
        __smtx_model_eval M (__eo_to_smt e) :: rest ∧
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) = T := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  obtain ⟨hHeadTy, hTailTy⟩ :=
    strConcat_args_of_seq_type head tail T
      (by simpa [head] using hTy)
  rcases seq_eval_of_seq_type M hM tail T hTailTy with
    ⟨stail, hTailEval⟩
  let shead :=
    SmtSeq.cons (__smtx_model_eval M (__eo_to_smt e))
      (SmtSeq.empty
        (__smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e))))
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt head) = SmtValue.Seq shead := by
    change __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt e)) =
      SmtValue.Seq shead
    simp [__smtx_model_eval, shead]
  have hHeadUnp :
      native_unpack_seq shead =
        [__smtx_model_eval M (__eo_to_smt e)] := by
    simp [shead, native_unpack_seq]
  obtain ⟨sxy, hWholeEval, hWholeUnp⟩ :=
    RuleProofs.strConcat_unpack_eval M head tail shead stail
      hHeadEval hTailEval
  have hSx : sx = sxy := by
    rw [hEval] at hWholeEval
    injection hWholeEval
  have hElemTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt e)) = T := by
    have hArgTy :
        __smtx_typeof (__eo_to_smt e) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e)
        (A := T) (by have hsimpa := hHeadTy; (try simp [head] at hsimpa ⊢); exact hsimpa)).1
    have hPres := Smtm.smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt e)
      (by
        unfold term_has_non_none_type
        rw [hArgTy]
        exact hTNN)
    simpa [hArgTy] using hPres
  refine ⟨native_unpack_seq stail, ?_, hElemTy⟩
  rw [hSx, hWholeUnp, hHeadUnp]
  rfl

private theorem seq_prefix_l2_eq_bool_native
    (M : SmtModel) (hM : model_wf M) :
    ∀ a b T sx sy,
      T ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_2___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_2___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy)) := by
  intro a b T sx sy hTNN hATy hBTy hAEval hBEval hNe
  unfold __eo_l_2___seq_is_prefix at hNe ⊢
  split at hNe <;> simp at hNe ⊢
  case h_2 x1 x2 et ts es ss =>
    let guard :=
      __eo_ite (__eo_eq et es) (Term.Boolean false)
        (__are_distinct_terms_type et es (__eo_typeof et))
    have hOut :
        __eo_requires guard (Term.Boolean true) (Term.Boolean false) =
          Term.Boolean false :=
      eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true)
        (Term.Boolean false) (by simpa [guard] using hNe)
    have hGuard : guard = Term.Boolean true :=
      eo_requires_eq_of_ne_stuck guard (Term.Boolean true)
        (Term.Boolean false) (by simpa [guard] using hNe)
    rcases seq_unit_concat_unpack_cons M hM et ts T sx hTNN
        (by simpa using hATy) (by simpa using hAEval) with
      ⟨restA, hUnpA, _hEtTy⟩
    rcases seq_unit_concat_unpack_cons M hM es ss T sy hTNN
        (by simpa using hBTy) (by simpa using hBEval) with
      ⟨restB, hUnpB, _hEsTy⟩
    have hGuardParts :
        __eo_eq et es = Term.Boolean false ∧
          __are_distinct_terms_type et es (__eo_typeof et) =
            Term.Boolean true :=
      eo_ite_eq_false_guard_true (by simpa [guard] using hGuard)
    have hEqFalse : __eo_eq et es = Term.Boolean false := hGuardParts.1
    have hDistinct :
        __are_distinct_terms_type et es (__eo_typeof et) =
          Term.Boolean true := hGuardParts.2
    have hEtArgTy :
        __smtx_typeof (__eo_to_smt et) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt et)
        (A := T)
        (by
          exact (strConcat_args_of_seq_type
            (Term.Apply (Term.UOp UserOp.seq_unit) et) ts
            T (by simpa using hATy)).1)).1
    have hEsArgTy :
        __smtx_typeof (__eo_to_smt es) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt es)
        (A := T)
        (by
          exact (strConcat_args_of_seq_type
            (Term.Apply (Term.UOp UserOp.seq_unit) es) ss
            T (by simpa using hBTy)).1)).1
    have hEtTrans : RuleProofs.eo_has_smt_translation et := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hEtArgTy]
      exact hTNN
    have hEsTrans : RuleProofs.eo_has_smt_translation es := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hEsArgTy]
      exact hTNN
    have hEvalEqFalse :
        __smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt et))
            (__smtx_model_eval M (__eo_to_smt es)) =
          SmtValue.Boolean false :=
      are_distinct_terms_type_model_eval_eq_false M hM et es
        hEtTrans hEsTrans hEqFalse hDistinct
    have hVeqFalse :
        native_veq (__smtx_model_eval M (__eo_to_smt et))
            (__smtx_model_eval M (__eo_to_smt es)) = false :=
      RuleProofs.native_veq_false_of_model_eval_eq_false hEvalEqFalse
    rw [hOut, hUnpA, hUnpB]
    rw [native_seq_prefix_eq_cons_cons_false_of_veq_false
      (xs := restA) (ys := restB) hVeqFalse]
  case h_3 =>
    have hNil :
        native_unpack_seq sx = [] :=
      seq_empty_uop1_unpack_nil_of_seq M _ T sx hATy hAEval
    rw [hNil]
    rfl
  case h_4 =>
    rcases seq_unit_concat_unpack_cons M hM _ _ T sx hTNN
        (by simpa using hATy) (by simpa using hAEval) with
      ⟨restA, hUnpA, _hEtTy⟩
    have hNil :
        native_unpack_seq sy = [] :=
      seq_empty_uop1_unpack_nil_of_seq M _ T sy hBTy hBEval
    rw [hUnpA, hNil]
    rfl

private theorem seq_prefix_l1_eq_bool_native
    (M : SmtModel) (hM : model_wf M) :
    ∀ a b T sx sy,
      T ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_1___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_1___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy)) := by
  intro a b
  let motive1 : Term -> Term -> Prop := fun a b =>
    ∀ T sx sy,
      T ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __eo_l_1___seq_is_prefix a b ≠ Term.Stuck ->
      __eo_l_1___seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy))
  let motive2 : Term -> Term -> Prop := fun a b =>
    ∀ T sx sy,
      T ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      __seq_is_prefix a b ≠ Term.Stuck ->
      __seq_is_prefix a b =
        Term.Boolean
          (native_seq_prefix_eq (native_unpack_seq sx)
            (native_unpack_seq sy))
  change motive1 a b
  refine __eo_l_1___seq_is_prefix.induct motive1 motive2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
  · intro x
    dsimp [motive1]
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe
  · intro x hx
    dsimp [motive1]
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe
  · intro t t2 u s2 ih
    dsimp [motive1]
    dsimp [motive2] at ih
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    let a := mkConcat t t2
    let b := mkConcat u s2
    let l2 := __eo_l_2___seq_is_prefix a b
    simp [__eo_l_1___seq_is_prefix] at hNe ⊢
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u)
        (__seq_is_prefix t2 s2) l2 hNe with hCond | hCond
    · have hTailNe : __seq_is_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hNe
      obtain ⟨hHeadTyA, hTailTyA⟩ :=
        strConcat_args_of_seq_type t t2 T hATy
      obtain ⟨_hHeadTyB, hTailTyB⟩ :=
        strConcat_args_of_seq_type u s2 T hBTy
      rcases seq_eval_of_seq_type M hM t T hHeadTyA with
        ⟨sHead, hHeadEvalA⟩
      rcases seq_eval_of_seq_type M hM t2 T hTailTyA with
        ⟨sTailA, hTailEvalA⟩
      rcases seq_eval_of_seq_type M hM s2 T hTailTyB with
        ⟨sTailB, hTailEvalB⟩
      have hHeadEq : u = t :=
        eq_of_eo_eq_true_local t u hCond
      have hHeadEvalB :
          __smtx_model_eval M (__eo_to_smt u) = SmtValue.Seq sHead := by
        simpa [hHeadEq] using hHeadEvalA
      have hUnpA :
          native_unpack_seq sx =
            native_unpack_seq sHead ++ native_unpack_seq sTailA :=
        str_concat_unpack_of_seq_evals M t t2 sx sHead sTailA
          hHeadEvalA hTailEvalA hAEval
      have hUnpB :
          native_unpack_seq sy =
            native_unpack_seq sHead ++ native_unpack_seq sTailB :=
        str_concat_unpack_of_seq_evals M u s2 sy sHead sTailB
          hHeadEvalB hTailEvalB hBEval
      have hTailEq :
          __seq_is_prefix t2 s2 =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sTailA)
                (native_unpack_seq sTailB)) :=
        ih T sTailA sTailB hTNN hTailTyA hTailTyB
          hTailEvalA hTailEvalB hTailNe
      rw [hCond, eo_ite_true, hTailEq, hUnpA, hUnpB]
      rw [native_seq_prefix_eq_append_left_same]
    · have hL2Ne : l2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      have hL2Eq :
          l2 =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        seq_prefix_l2_eq_bool_native M hM a b T sx sy hTNN
          hATy hBTy hAEval hBEval hL2Ne
      rw [hCond, eo_ite_false]
      simpa [l2, a, b] using hL2Eq
  · intro x y hx hy hNotBoth
    dsimp [motive1]
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    simp [__eo_l_1___seq_is_prefix] at hNe ⊢
    exact seq_prefix_l2_eq_bool_native M hM x y T sx sy hTNN
      hATy hBTy hAEval hBEval hNe
  · intro x
    dsimp [motive2]
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    simp [__seq_is_prefix] at hNe
  · intro x hx
    dsimp [motive2]
    intro T sx sy hTNN hATy hBTy hAEval hBEVal hNe
    simp [__seq_is_prefix] at hNe
  · intro x y hx hy ih
    dsimp [motive2]
    dsimp [motive1] at ih
    intro T sx sy hTNN hATy hBTy hAEval hBEval hNe
    simp [__seq_is_prefix] at hNe ⊢
    rcases eo_ite_cases_of_ne_stuck (__eo_eq x y) (Term.Boolean true)
        (__eo_l_1___seq_is_prefix x y) hNe with hCond | hCond
    · have hXY : y = x :=
        eq_of_eo_eq_true_local x y hCond
      have hSeq : sx = sy := by
        rw [hXY, hAEval] at hBEval
        injection hBEval
      rw [hCond, eo_ite_true, hSeq]
      simp [native_seq_prefix_eq_self]
    · have hL1Ne : __eo_l_1___seq_is_prefix x y ≠ Term.Stuck := by
        simpa [hCond, eo_ite_false] using hNe
      have hL1Eq :
          __eo_l_1___seq_is_prefix x y =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        ih T sx sy hTNN hATy hBTy hAEval hBEval hL1Ne
      rw [hCond, eo_ite_false, hL1Eq]

private theorem seq_prefix_eq_bool_native
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) (T : SmtType) (sx sy : SmtSeq)
    (hTNN : T ≠ SmtType.None)
    (hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hAEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy)
    (hNe : __seq_is_prefix a b ≠ Term.Stuck) :
    __seq_is_prefix a b =
      Term.Boolean
        (native_seq_prefix_eq (native_unpack_seq sx)
          (native_unpack_seq sy)) := by
  have hA : a ≠ Term.Stuck :=
    seq_is_prefix_left_ne_stuck_of_ne_stuck a b hNe
  have hB : b ≠ Term.Stuck :=
    seq_is_prefix_right_ne_stuck_of_ne_stuck a b hNe
  have hSeqDef :
      __seq_is_prefix a b =
        __eo_ite (__eo_eq a b) (Term.Boolean true)
          (__eo_l_1___seq_is_prefix a b) := by
    cases a <;> cases b <;> simp [__seq_is_prefix] at hA hB ⊢
  have hNeIte :
      __eo_ite (__eo_eq a b) (Term.Boolean true)
          (__eo_l_1___seq_is_prefix a b) ≠ Term.Stuck := by
    simpa [hSeqDef] using hNe
  rcases eo_ite_cases_of_ne_stuck (__eo_eq a b) (Term.Boolean true)
      (__eo_l_1___seq_is_prefix a b) hNeIte with hCond | hCond
  · have hBA : b = a :=
      eq_of_eo_eq_true_local a b hCond
    have hSeq : sx = sy := by
      rw [hBA, hAEval] at hBEval
      injection hBEval
    rw [hSeqDef, hCond, eo_ite_true, hSeq]
    simp [native_seq_prefix_eq_self]
  · have hL1Ne : __eo_l_1___seq_is_prefix a b ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hNeIte
    have hL1Eq :
        __eo_l_1___seq_is_prefix a b =
          Term.Boolean
            (native_seq_prefix_eq (native_unpack_seq sx)
              (native_unpack_seq sy)) :=
      seq_prefix_l1_eq_bool_native M hM a b T sx sy hTNN
        hATy hBTy hAEval hBEval hL1Ne
    rw [hSeqDef, hCond, eo_ite_false, hL1Eq]

private theorem native_seq_extract_zero_nat_any
    (xs : List SmtValue) (n : Nat) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  by_cases hle : n <= xs.length
  · exact native_seq_extract_zero_nat xs n hle
  · cases xs with
    | nil =>
        simp [native_seq_extract]
    | cons x xs =>
        unfold native_seq_extract
        have hn : n ≠ 0 := by
          intro hn
          subst n
          simp at hle
        have hLenLt : (x :: xs).length < n := Nat.lt_of_not_ge hle
        have hLenLe : (x :: xs).length <= n := Nat.le_of_lt hLenLt
        have hLenNotLe :
            ¬ ((Int.ofNat xs.length : Int) + 1 <= 0) := by
          have hNonneg : (0 : Int) <= Int.ofNat xs.length :=
            Int.natCast_nonneg xs.length
          omega
        have hmin :
            min (Int.ofNat n) (Int.ofNat (x :: xs).length) =
              Int.ofNat (x :: xs).length :=
          Int.min_eq_right (Int.ofNat_le.mpr hLenLe)
        have hminToNat :
            (min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat =
              (x :: xs).length := by
          rw [hmin]
          simp
        simp [hn]
        change
          (x :: xs).take
              ((min (Int.ofNat n) (Int.ofNat (x :: xs).length)).toNat) =
            (x :: xs).take n
        rw [hminToNat, List.take_of_length_le (Nat.le_refl (x :: xs).length),
          List.take_of_length_le hLenLe]

private theorem native_seq_prefix_eq_nil_left (xs : List SmtValue) :
    native_seq_prefix_eq [] xs = true := by
  cases xs <;> rfl

private theorem native_seq_indexof_rec_empty_succ
    (xs : List SmtValue) (i fuel : Nat) :
    native_seq_indexof_rec xs [] i (fuel + 1) = Int.ofNat i := by
  unfold native_seq_indexof_rec
  rw [if_pos (native_seq_prefix_eq_nil_left xs)]

private theorem native_seq_indexof_empty_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  exact StrEqReplSupport.native_seq_indexof_nil_zero xs

private theorem native_seq_replace_eq_extracts_of_indexof_nonneg
    (xs pat repl : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    native_seq_replace xs pat repl =
      native_seq_extract xs 0 (native_seq_indexof xs pat 0) ++ repl ++
        native_seq_extract xs
          (native_seq_indexof xs pat 0 + Int.ofNat pat.length)
          (Int.ofNat xs.length -
            (native_seq_indexof xs pat 0 + Int.ofNat pat.length)) := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : (Int.ofNat j : Int) = idx :=
    Int.toNat_of_nonneg hIdxNonneg
  have hIdxEq : native_seq_indexof xs pat 0 = Int.ofNat j := by
    simpa [idx] using hCast.symm
  have hDecomp :
      native_seq_extract xs 0 idx ++ pat ++
          native_seq_extract xs (idx + Int.ofNat pat.length)
            (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
        xs := by
    simpa [idx] using native_seq_indexof_zero_decomp xs pat hIdxNonneg
  have hPreLenInt :
      Int.ofNat (native_seq_extract xs 0 idx).length = idx := by
    simpa [idx] using
      native_seq_extract_prefix_length_of_indexof_nonneg xs pat hIdxNonneg
  have hPreLen :
      (native_seq_extract xs 0 idx).length = j := by
    apply Int.ofNat.inj
    rw [hPreLenInt, ← hCast]
  have hStartLe : j + pat.length ≤ xs.length := by
    have hLen := congrArg List.length hDecomp
    simp [hPreLen] at hLen
    omega
  have hJLe : j ≤ xs.length := by
    omega
  have hPre :
      native_seq_extract xs 0 idx = xs.take j := by
    rw [← hCast]
    exact native_seq_extract_zero_nat xs j hJLe
  have hStart :
      idx + Int.ofNat pat.length = Int.ofNat (j + pat.length) := by
    rw [← hCast]
    simp
  have hRest :
      Int.ofNat xs.length - (idx + Int.ofNat pat.length) =
        Int.ofNat (xs.length - (j + pat.length)) := by
    rw [← hCast]
    simp
    exact (Int.ofNat_sub hStartLe).symm
  have hRest' :
      Int.ofNat xs.length - Int.ofNat (j + pat.length) =
        Int.ofNat (xs.length - (j + pat.length)) :=
    (Int.ofNat_sub hStartLe).symm
  have hSuf :
      native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
        xs.drop (j + pat.length) := by
    rw [hStart]
    rw [hRest']
    exact native_seq_extract_to_end_nat xs (j + pat.length) hStartLe
  cases pat with
  | nil =>
      rw [StrEqReplSupport.native_seq_replace_eq_indexof,
        native_seq_indexof_empty_zero xs]
      have hZero : native_seq_extract xs 0 0 = [] := by
        simp [native_seq_extract]
      have hAll :
          native_seq_extract xs 0 (Int.ofNat xs.length) = xs := by
        simpa using native_seq_extract_to_end_nat xs 0 (Nat.zero_le xs.length)
      simp [hZero]
      exact hAll.symm
  | cons p ps =>
      have hIdxNotNeg : ¬ idx < 0 := Int.not_lt.mpr hIdxNonneg
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      have hNatNotNeg : ¬ (Int.ofNat j : Int) < 0 := by simp
      simp [hIdxEq]
      have hPre' :
          native_seq_extract xs 0 (Int.ofNat j) = xs.take j := by
        rw [hCast]
        exact hPre
      have hSuf' :
          native_seq_extract xs
              (Int.ofNat j + (Int.ofNat ps.length + 1))
              (Int.ofNat xs.length -
                (Int.ofNat j + (Int.ofNat ps.length + 1))) =
            xs.drop (j + (ps.length + 1)) := by
        rw [hCast]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hSuf
      change
        (if (Int.ofNat j : Int) < 0 then xs
          else xs.take j ++ (repl ++ xs.drop (j + (ps.length + 1)))) =
          native_seq_extract xs 0 (Int.ofNat j) ++
            (repl ++
              native_seq_extract xs
                (Int.ofNat j + (Int.ofNat ps.length + 1))
                (Int.ofNat xs.length -
                  (Int.ofNat j + (Int.ofNat ps.length + 1))))
      rw [if_neg hNatNotNeg]
      rw [← hPre']
      rw [← hSuf']

private theorem native_seq_replace_eq_self_of_indexof_neg
    (xs pat repl : List SmtValue)
    (hIdxNeg : native_seq_indexof xs pat 0 < 0) :
    native_seq_replace xs pat repl = xs := by
  cases pat with
  | nil =>
      have hIdx := native_seq_indexof_empty_zero xs
      rw [hIdx] at hIdxNeg
      exact False.elim (Int.lt_irrefl 0 hIdxNeg)
  | cons p ps =>
      simp [native_seq_replace, hIdxNeg]

private theorem smtx_model_eval_str_prefixof_seq_eq
    (sx sy : SmtSeq) (T : SmtType)
    (hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T) :
    __smtx_model_eval_str_prefixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      SmtValue.Boolean
        (native_seq_prefix_eq (native_unpack_seq sx) (native_unpack_seq sy)) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hsxPack :
      native_pack_seq T xs = sx := by
    simpa [xs, hsxElem] using native_pack_unpack_seq sx
  have hExtract :
      native_seq_extract ys 0 (Int.ofNat xs.length) =
        ys.take xs.length := by
    exact native_seq_extract_zero_nat_any ys xs.length
  by_cases hPref :
      native_seq_prefix_eq xs ys = true
  · rcases (RuleProofs.native_seq_prefix_eq_iff xs ys).1 hPref with
      ⟨rest, hYs⟩
    have hTake : ys.take xs.length = xs := by
      rw [hYs]
      simp
    have hSeqEqExtract :
        sx =
          native_pack_seq T
            (native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length)) := by
      have hExtract' :
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
            native_unpack_seq sx := by
        calc
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
              ys.take xs.length := by
                simpa [xs, ys] using hExtract
          _ = xs := hTake
          _ = native_unpack_seq sx := rfl
      rw [hExtract']
      exact hsxPack.symm
    simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq, native_veq,
      native_seq_len, xs, ys, hsyElem, hPref]
    exact hSeqEqExtract
  · have hPrefFalse :
        native_seq_prefix_eq xs ys = false := by
      cases h : native_seq_prefix_eq xs ys
      · rfl
      · exact False.elim (hPref h)
    have hSeqNe :
        sx ≠ native_pack_seq T (ys.take xs.length) := by
      intro hEq
      have hList :
          xs = ys.take xs.length := by
        have hPackEq :
            native_pack_seq T xs =
              native_pack_seq T (ys.take xs.length) := by
          simpa [hsxPack] using hEq
        exact native_pack_seq_inj T hPackEq
      have hPrefTrue : native_seq_prefix_eq xs ys = true :=
        native_seq_prefix_eq_take_eq_true xs ys hList.symm
      rw [hPrefFalse] at hPrefTrue
      cases hPrefTrue
    have hSeqNeExtract :
        sx ≠
          native_pack_seq T
            (native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length)) := by
      have hExtract' :
          native_seq_extract (native_unpack_seq sy) 0
              (Int.ofNat (native_unpack_seq sx).length) =
            List.take (native_unpack_seq sx).length (native_unpack_seq sy) := by
        simpa [xs, ys] using hExtract
      intro hEq
      apply hSeqNe
      rwa [hExtract'] at hEq
    simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq, native_veq,
      native_seq_len, xs, ys, hsyElem, hPrefFalse]
    exact hSeqNeExtract

private theorem native_seq_extract_suffix_nat_suffix_local
    (xs : List SmtValue) (n : Nat) :
    ∃ pre,
      xs =
        pre ++
          native_seq_extract xs
            (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) := by
  by_cases hle : n <= xs.length
  · refine ⟨xs.take (xs.length - n), ?_⟩
    have hStart :
        Int.ofNat xs.length + -Int.ofNat n =
          Int.ofNat (xs.length - n) := by
      rw [← Int.sub_eq_add_neg]
      exact (Int.ofNat_sub hle).symm
    have hRem : xs.length - (xs.length - n) = n := by
      omega
    have hSub :=
      native_seq_extract_to_end_nat xs (xs.length - n)
        (Nat.sub_le xs.length n)
    rw [hRem] at hSub
    rw [hStart, hSub]
    exact (List.take_append_drop (xs.length - n) xs).symm
  · refine ⟨xs, ?_⟩
    have hlt : xs.length < n := Nat.lt_of_not_ge hle
    have hStartNeg :
        Int.ofNat xs.length + -Int.ofNat n < 0 := by
      have hltInt : (Int.ofNat xs.length : Int) < Int.ofNat n :=
        Int.ofNat_lt.mpr hlt
      omega
    have hExtract :
        native_seq_extract xs
          (Int.ofNat xs.length + -Int.ofNat n) (Int.ofNat n) = [] := by
      unfold native_seq_extract
      have hGuard :
          (decide (Int.ofNat xs.length + -Int.ofNat n < 0) ||
                decide (Int.ofNat n <= 0) ||
              decide
                (Int.ofNat xs.length + -Int.ofNat n >=
                  Int.ofNat xs.length)) =
            true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (Or.inl hStartNeg)
      rw [if_pos hGuard]
    rw [hExtract]
    simp

private theorem native_seq_extract_suffix_eq_of_append
    (pre xs : List SmtValue) :
    native_seq_extract (pre ++ xs)
        (Int.ofNat (pre ++ xs).length + -Int.ofNat xs.length)
        (Int.ofNat xs.length) =
      xs := by
  have hStart :
      Int.ofNat (pre ++ xs).length + -Int.ofNat xs.length =
        Int.ofNat pre.length := by
    simp
    omega
  have hSub :=
    native_seq_extract_to_end_nat (pre ++ xs) pre.length
      (by simp)
  have hRem : (pre ++ xs).length - pre.length = xs.length := by
    simp
  rw [hRem] at hSub
  rw [hStart, hSub]
  simp

private theorem native_seq_extract_suffix_eq_of_rev_prefix_true
    (xs ys : List SmtValue)
    (hPref :
      native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true) :
    native_seq_extract ys
        (Int.ofNat ys.length + -Int.ofNat xs.length)
        (Int.ofNat xs.length) =
      xs := by
  rcases (RuleProofs.native_seq_prefix_eq_iff
      (native_seq_rev xs) (native_seq_rev ys)).1 hPref with
    ⟨rest, hRev⟩
  have hRevList : ys.reverse = xs.reverse ++ rest := by
    simpa [native_seq_rev] using hRev
  have hYs : ys = rest.reverse ++ xs := by
    have h := congrArg List.reverse hRevList
    simpa [List.reverse_append] using h
  rw [hYs]
  exact native_seq_extract_suffix_eq_of_append rest.reverse xs

private theorem native_seq_rev_prefix_true_of_suffix_extract_eq
    (xs ys : List SmtValue)
    (hExtract :
      xs =
        native_seq_extract ys
          (Int.ofNat ys.length + -Int.ofNat xs.length)
          (Int.ofNat xs.length)) :
    native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true := by
  rcases native_seq_extract_suffix_nat_suffix_local ys xs.length with
    ⟨pre, hYs⟩
  rw [← hExtract] at hYs
  rw [RuleProofs.native_seq_prefix_eq_iff]
  refine ⟨pre.reverse, ?_⟩
  rw [hYs]
  simp [native_seq_rev, List.reverse_append]

private theorem smtx_model_eval_str_suffixof_seq_eq
    (sx sy : SmtSeq) (T : SmtType)
    (hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T) :
    __smtx_model_eval_str_suffixof (SmtValue.Seq sx) (SmtValue.Seq sy) =
      SmtValue.Boolean
        (native_seq_prefix_eq (native_seq_rev (native_unpack_seq sx))
          (native_seq_rev (native_unpack_seq sy))) := by
  let xs := native_unpack_seq sx
  let ys := native_unpack_seq sy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hsxPack :
      native_pack_seq T xs = sx := by
    simpa [xs, hsxElem] using native_pack_unpack_seq sx
  by_cases hPref :
      native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) = true
  · have hExtract :
        native_seq_extract ys
            (Int.ofNat ys.length + -Int.ofNat xs.length)
            (Int.ofNat xs.length) =
          xs :=
      native_seq_extract_suffix_eq_of_rev_prefix_true xs ys hPref
    have hSeqEq :
        sx =
          native_pack_seq T
            (native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length)) := by
      rw [hExtract]
      exact hsxPack.symm
    simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq,
      __smtx_model_eval__, native_veq, native_seq_len, xs, ys, hsyElem,
      hPref]
    exact hSeqEq
  · have hPrefFalse :
        native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) =
          false := by
      cases h : native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys)
      · rfl
      · exact False.elim (hPref h)
    have hSeqNe :
        sx ≠
          native_pack_seq T
            (native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length)) := by
      intro hEq
      have hList :
          xs =
            native_seq_extract ys
              (Int.ofNat ys.length + -Int.ofNat xs.length)
              (Int.ofNat xs.length) := by
        have hPackEq :
            native_pack_seq T xs =
              native_pack_seq T
                (native_seq_extract ys
                  (Int.ofNat ys.length + -Int.ofNat xs.length)
                  (Int.ofNat xs.length)) := by
          simpa [hsxPack] using hEq
        exact native_pack_seq_inj T hPackEq
      have hPrefTrue :
          native_seq_prefix_eq (native_seq_rev xs) (native_seq_rev ys) =
            true :=
        native_seq_rev_prefix_true_of_suffix_extract_eq xs ys hList
      rw [hPrefFalse] at hPrefTrue
      cases hPrefTrue
    simp [__smtx_model_eval_str_suffixof, __smtx_model_eval_str_len,
      __smtx_model_eval_str_substr, __smtx_model_eval_eq,
      __smtx_model_eval__, native_veq, native_seq_len, xs, ys, hsyElem,
      hPrefFalse]
    exact hSeqNe

private theorem native_seq_indexof_zero_eq_rec
    (xs pat : List SmtValue) :
    native_seq_indexof xs pat 0 =
      if h : pat.length ≤ xs.length then
        native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1)
      else
        -1 := by
  rw [native_seq_indexof_eq_rec]
  simp

private theorem native_seq_indexof_cons_not_prefix
    (x : SmtValue) (xs pat : List SmtValue)
    (hPref : native_seq_prefix_eq pat (x :: xs) = false) :
    native_seq_indexof (x :: xs) pat 0 =
      (let r := native_seq_indexof xs pat 0
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1) := by
  have hPrefNot : ¬ native_seq_prefix_eq pat (x :: xs) = true := by
    intro h
    rw [h] at hPref
    cases hPref
  rw [native_seq_indexof_zero_eq_rec (x :: xs) pat]
  rw [native_seq_indexof_zero_eq_rec xs pat]
  by_cases hTail : pat.length ≤ xs.length
  · have hCons : pat.length ≤ (x :: xs).length := by
      simpa using Nat.le_trans hTail (Nat.le_succ xs.length)
    rw [dif_pos hCons, dif_pos hTail]
    have hStep :
        native_seq_indexof_rec (x :: xs) pat 0
            ((x :: xs).length - pat.length + 1) =
          native_seq_indexof_rec xs pat 1
            (xs.length - pat.length + 1) := by
      have hFuel :
          (x :: xs).length - pat.length + 1 =
            (xs.length - pat.length + 1) + 1 := by
        simp
        omega
      rw [hFuel]
      simp [native_seq_indexof_rec, hPrefNot]
    rw [hStep]
    exact
      RuleProofs.native_seq_indexof_rec_offset xs pat 0 1
        (xs.length - pat.length + 1)
  · rw [dif_neg hTail]
    by_cases hCons : pat.length ≤ (x :: xs).length
    · rw [dif_pos hCons]
      have hPatLen : pat.length = (x :: xs).length := by
        have hGt : xs.length < pat.length := Nat.lt_of_not_ge hTail
        have hLe : pat.length ≤ xs.length + 1 := by
          simpa using hCons
        simp
        omega
      have hFuel : (x :: xs).length - pat.length + 1 = 1 := by
        rw [hPatLen]
        simp
      rw [hFuel]
      simp [native_seq_indexof_rec, hPrefNot]
    · rw [dif_neg hCons]
      simp

private theorem native_seq_indexof_nil_zero (pat : List SmtValue) :
    native_seq_indexof [] pat 0 =
      if pat = [] then 0 else (-1 : native_Int) := by
  cases pat with
  | nil =>
      simp [native_seq_indexof, native_seq_indexof_rec,
        native_seq_prefix_eq]
  | cons p ps =>
      simp [native_seq_indexof]

private theorem native_seq_indexof_eq_neg_one_of_gt_len
    (xs pat : List SmtValue) (i : native_Int)
    (hGt : Int.ofNat xs.length < i) :
    native_seq_indexof xs pat i = (-1 : native_Int) := by
  rw [native_seq_indexof_eq_rec]
  have hLenNonneg : 0 ≤ (Int.ofNat xs.length : Int) :=
    Int.natCast_nonneg xs.length
  have hiPos : 0 < i := Int.lt_of_le_of_lt hLenNonneg hGt
  have hiNonnegLe : 0 ≤ i := Int.le_of_lt hiPos
  have hiNotNeg : ¬ i < 0 := Int.not_lt.mpr hiNonnegLe
  rw [if_neg hiNotNeg]
  have hCast : (Int.toNat i : Int) = i :=
    Int.toNat_of_nonneg hiNonnegLe
  have hStartGt : xs.length < Int.toNat i := by
    exact Int.ofNat_lt.mp (by simpa [hCast] using hGt)
  have hNoFit : ¬ Int.toNat i + pat.length ≤ xs.length := by
    omega
  rw [dif_neg hNoFit]

private theorem native_seq_indexof_zero_of_prefix
    (xs pat : List SmtValue)
    (hPref : native_seq_prefix_eq pat xs = true) :
    native_seq_indexof xs pat 0 = 0 := by
  have hLen : pat.length ≤ xs.length := by
    rcases (RuleProofs.native_seq_prefix_eq_iff pat xs).1 hPref with
      ⟨rest, hxs⟩
    rw [hxs]
    simp
  rw [native_seq_indexof_eq_rec]
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add,
    List.drop_zero]
  rw [dif_pos (by simpa using hLen)]
  have hFuel :
      xs.length - pat.length + 1 = (xs.length - pat.length) + 1 := by
    omega
  rw [hFuel]
  unfold native_seq_indexof_rec
  rw [if_pos hPref]
  simp

private def native_seq_indexof_offset
    (xs pat : List SmtValue) (off : Nat) : native_Int :=
  let r := native_seq_indexof xs pat 0
  if r = (-1 : native_Int) then (-1 : native_Int) else r + Int.ofNat off

private theorem native_seq_indexof_offset_zero
    (xs pat : List SmtValue) :
    native_seq_indexof_offset xs pat 0 =
      native_seq_indexof xs pat 0 := by
  unfold native_seq_indexof_offset
  by_cases h : native_seq_indexof xs pat 0 = (-1 : native_Int)
  · simp [h]
  · simp [h]

private theorem native_seq_indexof_offset_drop_eq
    (xs pat : List SmtValue) (off : Nat) (hOff : off ≤ xs.length) :
    native_seq_indexof_offset (xs.drop off) pat off =
      native_seq_indexof xs pat (Int.ofNat off) := by
  unfold native_seq_indexof_offset
  rw [native_seq_indexof_zero_eq_rec (xs.drop off) pat]
  rw [native_seq_indexof_eq_rec]
  have hOffNotNeg : ¬ (Int.ofNat off : Int) < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg off)
  rw [if_neg hOffNotNeg]
  change
    (let r :=
      if h : pat.length ≤ (xs.drop off).length then
        native_seq_indexof_rec (xs.drop off) pat 0
          ((xs.drop off).length - pat.length + 1)
      else
        (-1 : native_Int)
     if r = (-1 : native_Int) then (-1 : native_Int)
     else r + Int.ofNat off) =
      if h : off + pat.length ≤ xs.length then
        native_seq_indexof_rec (xs.drop off) pat off
          (xs.length - (off + pat.length) + 1)
      else
        (-1 : native_Int)
  by_cases hTailFit : pat.length ≤ (xs.drop off).length
  · have hFullFit : off + pat.length ≤ xs.length := by
      rw [List.length_drop] at hTailFit
      omega
    rw [dif_pos hTailFit, dif_pos hFullFit]
    have hFuel :
        (xs.drop off).length - pat.length + 1 =
          xs.length - (off + pat.length) + 1 := by
      rw [List.length_drop]
      omega
    rw [hFuel]
    rw [← RuleProofs.native_seq_indexof_rec_offset
      (xs.drop off) pat 0 off]
    simp
  · have hFullNot : ¬ off + pat.length ≤ xs.length := by
      intro hFull
      apply hTailFit
      rw [List.length_drop]
      omega
    rw [dif_neg hTailFit, dif_neg hFullNot]
    simp

private theorem native_seq_indexof_offset_of_prefix
    (xs pat : List SmtValue) (off : Nat)
    (hPref : native_seq_prefix_eq pat xs = true) :
    native_seq_indexof_offset xs pat off = Int.ofNat off := by
  unfold native_seq_indexof_offset
  rw [native_seq_indexof_zero_of_prefix xs pat hPref]
  simp

private theorem native_seq_indexof_offset_cons_not_prefix
    (x : SmtValue) (xs pat : List SmtValue) (off : Nat)
    (hPref : native_seq_prefix_eq pat (x :: xs) = false) :
    native_seq_indexof_offset (x :: xs) pat off =
      native_seq_indexof_offset xs pat (off + 1) := by
  unfold native_seq_indexof_offset
  rw [native_seq_indexof_cons_not_prefix x xs pat hPref]
  by_cases hTail : native_seq_indexof xs pat 0 = (-1 : native_Int)
  · simp [hTail]
  · have hTailNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
      rcases native_seq_indexof_eq_neg_one_or_ge xs pat 0 with
        hNeg | hGe
      · exact False.elim (hTail hNeg)
      · simpa using hGe
    have hStepNe :
        native_seq_indexof xs pat 0 + 1 ≠ (-1 : native_Int) := by
      intro hBad
      have hNonneg : 0 ≤ native_seq_indexof xs pat 0 + 1 :=
        Int.add_nonneg hTailNonneg (by decide)
      rw [hBad] at hNonneg
      exact (by decide : ¬ (0 : native_Int) ≤ -1) hNonneg
    have hStepNeLeft :
        1 + native_seq_indexof xs pat 0 ≠ (-1 : native_Int) := by
      simpa [Int.add_comm] using hStepNe
    simp [hTail, hStepNeLeft, Int.add_assoc, Int.add_comm]

private theorem native_seq_indexof_offset_nil_of_ne_empty
    (pat : List SmtValue) (off : Nat)
    (hPat : pat ≠ []) :
    native_seq_indexof_offset [] pat off = (-1 : native_Int) := by
  unfold native_seq_indexof_offset
  rw [native_seq_indexof_nil_zero pat]
  simp [hPat]

private def native_seq_replace_all_chain (pat repl : List SmtValue) :
    Nat -> List SmtValue -> List SmtValue
  | _, [] => []
  | 0, x :: xs =>
      if native_seq_prefix_eq pat (x :: xs) then
        repl ++ native_seq_replace_all_chain pat repl (pat.length - 1) xs
      else
        x :: native_seq_replace_all_chain pat repl 0 xs
  | skip + 1, _ :: xs =>
      native_seq_replace_all_chain pat repl skip xs

private def native_seq_replace_all_aux (fuel : Nat)
    (pat repl : List SmtValue) : List SmtValue -> List SmtValue
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := native_seq_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                xs.take n ++ repl ++
                  native_seq_replace_all_aux fuel pat repl
                    (xs.drop (n + pat.length))

private theorem native_seq_replace_all_chain_skip_eq_drop
    (pat repl : List SmtValue) :
    ∀ (skip : Nat) (xs : List SmtValue),
      native_seq_replace_all_chain pat repl skip xs =
        native_seq_replace_all_chain pat repl 0 (xs.drop skip) := by
  intro skip
  induction skip with
  | zero =>
      intro xs
      simp
  | succ skip ih =>
      intro xs
      cases xs with
      | nil =>
          simp [native_seq_replace_all_chain]
      | cons _ xs =>
          simpa [native_seq_replace_all_chain] using ih xs

private theorem native_seq_replace_all_aux_prefix_cons
    (fuel : Nat) (xs repl : List SmtValue) (p : SmtValue)
    (ps : List SmtValue)
    (hPrefix : native_seq_prefix_eq (p :: ps) xs = true) :
    native_seq_replace_all_aux (fuel + 1) (p :: ps) repl xs =
      repl ++
        native_seq_replace_all_aux fuel (p :: ps) repl
          (xs.drop (ps.length + 1)) := by
  have hIdx : native_seq_indexof xs (p :: ps) 0 = 0 :=
    native_seq_indexof_zero_of_prefix xs (p :: ps) hPrefix
  simp [native_seq_replace_all_aux, hIdx]

private theorem native_seq_replace_all_aux_eq_chain_of_fuel
    (pat repl : List SmtValue) :
    ∀ (fuel : Nat) (xs : List SmtValue),
      xs.length + 1 ≤ fuel ->
      pat ≠ [] ->
      native_seq_replace_all_aux fuel pat repl xs =
        native_seq_replace_all_chain pat repl 0 xs := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro xs hFuel hPat
      cases fuel with
      | zero =>
          omega
      | succ fuel' =>
          cases pat with
          | nil =>
              contradiction
          | cons p ps =>
              cases xs with
              | nil =>
                  have hIdx :
                      native_seq_indexof [] (p :: ps) 0 = -1 := by
                    simp [native_seq_indexof]
                  simp [native_seq_replace_all_aux,
                    native_seq_replace_all_chain, hIdx]
              | cons x xs =>
                  have hXsFuel : xs.length + 1 ≤ fuel' := by
                    simp at hFuel
                    omega
                  by_cases hPref :
                      native_seq_prefix_eq (p :: ps) (x :: xs) = true
                  · rw [native_seq_replace_all_aux_prefix_cons fuel'
                      (x :: xs) repl p ps hPref]
                    have hDropLen :
                        ((x :: xs).drop (ps.length + 1)).length ≤
                          xs.length := by
                      simp [List.length_drop]
                    have hDropFuel :
                        ((x :: xs).drop (ps.length + 1)).length + 1 ≤
                          fuel' := by
                      omega
                    rw [ih fuel' (by omega)
                      ((x :: xs).drop (ps.length + 1)) hDropFuel
                      (by simp)]
                    simp [native_seq_replace_all_chain, hPref,
                      native_seq_replace_all_chain_skip_eq_drop]
                  · have hPrefFalse :
                        native_seq_prefix_eq (p :: ps) (x :: xs) =
                          false := by
                      cases hp :
                          native_seq_prefix_eq (p :: ps) (x :: xs) <;>
                        simp [hp] at hPref ⊢
                    have hConsIdx :=
                      native_seq_indexof_cons_not_prefix x xs (p :: ps)
                        hPrefFalse
                    by_cases hTailNeg :
                        native_seq_indexof xs (p :: ps) 0 < 0
                    · have hTailEq :
                          native_seq_indexof xs (p :: ps) 0 = -1 := by
                        rcases native_seq_indexof_eq_neg_one_or_ge
                            xs (p :: ps) 0 with hEq | hGe
                        · exact hEq
                        · have hNonneg :
                              0 ≤ native_seq_indexof xs (p :: ps) 0 := by
                            simpa using hGe
                          exact False.elim
                            ((Int.not_lt.mpr hNonneg) hTailNeg)
                      have hParentNeg :
                          native_seq_indexof (x :: xs) (p :: ps) 0 < 0 := by
                        rw [hConsIdx, hTailEq]
                        decide
                      have hTailEvalSelf :
                          native_seq_replace_all_aux fuel' (p :: ps)
                              repl xs =
                            xs := by
                        cases fuel' with
                        | zero =>
                            omega
                        | succ _fuel'' =>
                            simp [native_seq_replace_all_aux, hTailNeg]
                      have hTailChain :
                          native_seq_replace_all_chain (p :: ps) repl 0 xs =
                            xs := by
                        rw [← ih fuel' (by omega) xs hXsFuel (by simp)]
                        exact hTailEvalSelf
                      simp [native_seq_replace_all_aux, hParentNeg,
                        native_seq_replace_all_chain, hPrefFalse,
                        hTailChain]
                    · have hTailNonneg :
                          0 ≤ native_seq_indexof xs (p :: ps) 0 :=
                        Int.le_of_not_gt hTailNeg
                      let r := native_seq_indexof xs (p :: ps) 0
                      let n := Int.toNat r
                      have hRcast : Int.ofNat n = r :=
                        Int.toNat_of_nonneg hTailNonneg
                      have hTailFit :
                          n + (p :: ps).length ≤ xs.length := by
                        simpa [r, n] using
                          RuleProofs.native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
                            xs (p :: ps) hTailNonneg
                      have hTailNe : r ≠ -1 := by
                        intro h
                        have hBad : r < 0 := by
                          rw [h]
                          decide
                        exact hTailNeg (by simpa [r] using hBad)
                      have hParentIdx :
                          native_seq_indexof (x :: xs) (p :: ps) 0 =
                            r + 1 := by
                        rw [hConsIdx]
                        simp [r, hTailNe]
                      have hParentNotNeg :
                          ¬ native_seq_indexof (x :: xs) (p :: ps) 0 < 0 := by
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        intro hlt
                        have hR1Nonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        exact (Int.not_lt_of_ge hR1Nonneg)
                          (by simpa [hParentIdx] using hlt)
                      have hParentToNat :
                          Int.toNat
                              (native_seq_indexof (x :: xs) (p :: ps) 0) =
                            n + 1 := by
                        rw [hParentIdx]
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        have hNonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        apply Int.ofNat.inj
                        calc
                          Int.ofNat (Int.toNat (r + 1)) = r + 1 :=
                            Int.toNat_of_nonneg hNonneg
                          _ = Int.ofNat (n + 1) := by
                            rw [← hRcast]
                            simp
                      cases fuel' with
                      | zero =>
                          omega
                      | succ fuel'' =>
                          have hXsFuel' : xs.length ≤ fuel'' := by
                            omega
                          have hDropLenLe :
                              (xs.drop (n + (p :: ps).length)).length ≤
                                xs.length := by
                            rw [List.length_drop]
                            omega
                          have hDropLenLt :
                              (xs.drop (n + (p :: ps).length)).length <
                                xs.length := by
                            have hPatLenPos : 0 < (p :: ps).length := by
                              simp
                            rw [List.length_drop]
                            omega
                          have hSuffixFuelParent :
                              (xs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' + 1 := by
                            omega
                          have hSuffixFuelTail :
                              (xs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' := by
                            omega
                          have hParentSuffix :
                              native_seq_replace_all_aux (fuel'' + 1)
                                  (p :: ps) repl
                                  (xs.drop (n + (p :: ps).length)) =
                                native_seq_replace_all_chain (p :: ps) repl 0
                                  (xs.drop (n + (p :: ps).length)) :=
                            ih (fuel'' + 1) (by omega)
                              (xs.drop (n + (p :: ps).length))
                              hSuffixFuelParent (by simp)
                          have hTailSuffix :
                              native_seq_replace_all_aux fuel''
                                  (p :: ps) repl
                                  (xs.drop (n + (p :: ps).length)) =
                                native_seq_replace_all_chain (p :: ps) repl 0
                                  (xs.drop (n + (p :: ps).length)) :=
                            ih fuel'' (by omega)
                              (xs.drop (n + (p :: ps).length))
                              hSuffixFuelTail (by simp)
                          have hTailChain :
                              native_seq_replace_all_chain (p :: ps) repl 0 xs =
                                xs.take n ++ repl ++
                                  native_seq_replace_all_chain (p :: ps) repl 0
                                    (xs.drop (n + (p :: ps).length)) := by
                            rw [← ih (fuel'' + 1) (by omega) xs hXsFuel
                              (by simp)]
                            simp [native_seq_replace_all_aux, r, n,
                              hTailNeg]
                            simpa [r, n] using hTailSuffix
                          have hR1NotNeg : ¬ r + 1 < 0 := by
                            have hrNonneg : 0 ≤ r := by
                              rw [← hRcast]
                              exact Int.natCast_nonneg n
                            exact Int.not_lt_of_ge
                              (Int.add_nonneg hrNonneg (by decide))
                          have hToNatR1 : Int.toNat (r + 1) = n + 1 := by
                            simpa [hParentIdx] using hParentToNat
                          have hParentDrop :
                              (x :: xs).drop
                                  (n + 1 + (p :: ps).length) =
                                xs.drop (n + (p :: ps).length) := by
                            rw [show n + 1 + (p :: ps).length =
                                (n + (p :: ps).length) + 1 by omega]
                            simp
                          change
                            (let idx :=
                              native_seq_indexof (x :: xs) (p :: ps) 0
                             if idx < 0 then
                               x :: xs
                             else
                               (x :: xs).take (Int.toNat idx) ++ repl ++
                                 native_seq_replace_all_aux
                                   (fuel'' + 1) (p :: ps) repl
                                   ((x :: xs).drop
                                     (Int.toNat idx + (p :: ps).length))) =
                              native_seq_replace_all_chain (p :: ps) repl 0
                                (x :: xs)
                          rw [hParentIdx]
                          rw [if_neg hR1NotNeg]
                          rw [hToNatR1]
                          rw [hParentDrop]
                          rw [hParentSuffix]
                          simp [native_seq_replace_all_chain, hPrefFalse,
                            hTailChain, List.append_assoc]

private theorem native_seq_replace_all_eq_chain_cons
    (xs repl : List SmtValue) (p : SmtValue) (ps : List SmtValue) :
    native_seq_replace_all xs (p :: ps) repl =
      native_seq_replace_all_chain (p :: ps) repl 0 xs := by
  suffices hGen : ∀ (len : Nat) (ys : List SmtValue), ys.length = len ->
      native_seq_replace_all ys (p :: ps) repl =
        native_seq_replace_all_chain (p :: ps) repl 0 ys by
    exact hGen xs.length xs rfl
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
      intro ys hLen
      cases ys with
      | nil =>
          have hIdx : native_seq_indexof [] (p :: ps) 0 < 0 := by
            rw [native_seq_indexof_eq_rec]
            simp
          rw [StrReplaceAllSupport.replace_all_eq_self_of_indexof_neg
            (p :: ps) repl [] hIdx]
          rfl
      | cons y ys =>
          by_cases hPref :
              native_seq_prefix_eq (p :: ps) (y :: ys) = true
          · have hIdx : native_seq_indexof (y :: ys) (p :: ps) 0 = 0 :=
              native_seq_indexof_zero_of_prefix (y :: ys) (p :: ps) hPref
            have hNonneg : 0 ≤ native_seq_indexof (y :: ys) (p :: ps) 0 := by
              simp [hIdx]
            have hDropLt :
                ((y :: ys).drop (p :: ps).length).length < len := by
              rw [List.length_drop, ← hLen]
              simp only [List.length_cons]
              omega
            rw [StrReplaceAllSupport.replace_all_step (p :: ps) repl
              (y :: ys) (by simp) hNonneg, hIdx]
            simp only [Int.toNat_zero, List.take_zero, List.nil_append,
              Nat.zero_add]
            rw [ih _ hDropLt _ rfl]
            simp [native_seq_replace_all_chain, hPref,
              native_seq_replace_all_chain_skip_eq_drop]
          · have hPrefFalse :
                native_seq_prefix_eq (p :: ps) (y :: ys) = false := by
              cases hp : native_seq_prefix_eq (p :: ps) (y :: ys) <;>
                simp_all
            rw [StrReplaceAllSupport.replace_all_cons_of_not_prefix
              (p :: ps) repl y ys (by simp) hPrefFalse,
              ih ys.length (by
                simp only [List.length_cons] at hLen
                omega) ys rfl]
            simp [native_seq_replace_all_chain, hPrefFalse]

private theorem native_seq_replace_all_nil
    (xs repl : List SmtValue) :
    native_seq_replace_all xs [] repl = xs := by
  exact StrReplaceAllSupport.replace_all_nil_pat repl xs

private theorem smtx_eval_str_replace_all_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace_all x y z) =
      __smtx_model_eval_str_replace_all
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem seq_eval_replace_all_rec_unpack_eq_chain
    (M : SmtModel) (hM : model_wf M) :
    ∀ a b u skip lent T sa sb su sout skipNat,
      T ≠ SmtType.None ->
      __is_seq_const_rec a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sb ->
      __smtx_model_eval M (__eo_to_smt u) = SmtValue.Seq su ->
      skip = Term.Numeral (Int.ofNat skipNat) ->
      lent = Term.Numeral (Int.ofNat (native_unpack_seq sb).length) ->
      native_unpack_seq sb ≠ [] ->
      __seq_eval_replace_all_rec a b u skip lent ≠ Term.Stuck ->
      __smtx_model_eval M
          (__eo_to_smt (__seq_eval_replace_all_rec a b u skip lent)) =
        SmtValue.Seq sout ->
      native_unpack_seq sout =
        native_seq_replace_all_chain (native_unpack_seq sb)
          (native_unpack_seq su) skipNat (native_unpack_seq sa) := by
  intro a
  induction a using __is_seq_const_rec.induct with
  | case1 =>
      intro b u skip lent T sa sb su sout skipNat _hTNN hConst _hATy
        _hBTy _hUTy _hAEval _hBEval _hUEval _hSkip _hLent _hPatNe
        _hRecNe _hRecEval
      simp [__is_seq_const_rec] at hConst
  | case2 e tail ih =>
      intro b u skip lent T sa sb su sout skipNat hTNN hConst hATy hBTy
        hUTy hAEval hBEval hUEval hSkip hLent hPatNe hRecNe hRecEval
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let whole := mkConcat head tail
      have hTailConst : __is_seq_const_rec tail = Term.Boolean true := by
        simpa [head, whole, __is_seq_const_rec] using hConst
      have hWholeTy :
          __smtx_typeof (__eo_to_smt whole) = SmtType.Seq T := by
        simpa [head, whole, mkConcat] using hATy
      obtain ⟨hHeadTy, hTailTy⟩ :=
        strConcat_args_of_seq_type head tail T hWholeTy
      rcases seq_eval_of_seq_type M hM tail T hTailTy with
        ⟨stail, hTailEval⟩
      obtain ⟨shead, hHeadEvalRaw, hHeadUnpRaw⟩ :=
        RuleProofs.eval_seqUnitAtom M e
      have hHeadEval :
          __smtx_model_eval M (__eo_to_smt head) = SmtValue.Seq shead := by
        simpa [head] using hHeadEvalRaw
      have hHeadUnp :
          native_unpack_seq shead = [RuleProofs.seqElemVal M head] := by
        simpa [head] using hHeadUnpRaw
      have hBNe : b ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq b T hBTy
      have hUNe : u ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq u T hUTy
      have hLentNe : lent ≠ Term.Stuck := by
        rw [hLent]
        simp
      have hWholeUnp :
          native_unpack_seq sa =
            native_unpack_seq shead ++ native_unpack_seq stail :=
        str_concat_unpack_of_seq_evals M head tail sa shead stail
          hHeadEval hTailEval (by simpa [head, whole] using hAEval)
      have hWholeUnpCons :
          native_unpack_seq sa =
            RuleProofs.seqElemVal M head :: native_unpack_seq stail := by
        rw [hWholeUnp, hHeadUnp]
        rfl
      cases skipNat with
      | zero =>
          have hSkip0 : skip = Term.Numeral (0 : native_Int) := by
            simpa using hSkip
          subst skip
          rw [show Term.Numeral (Int.ofNat 0) =
              Term.Numeral (0 : native_Int) by rfl] at hRecNe hRecEval
          let nextMatch :=
            __seq_eval_replace_all_rec tail b u
              (__eo_add lent (Term.Numeral (-1 : native_Int))) lent
          let nextNo :=
            __seq_eval_replace_all_rec tail b u (Term.Numeral 0) lent
          have hRecDef :
              __seq_eval_replace_all_rec whole b u (Term.Numeral 0) lent =
                __eo_ite (__seq_is_prefix b whole)
                  (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
                  (__eo_cons (Term.UOp UserOp.str_concat) head nextNo) := by
            change __seq_eval_replace_all_rec (mkConcat head tail) b u
                (Term.Numeral 0) lent =
              __eo_ite (__seq_is_prefix b (mkConcat head tail))
                (__eo_list_concat (Term.UOp UserOp.str_concat) u
                  nextMatch)
                (__eo_cons (Term.UOp UserOp.str_concat) head nextNo)
            simp [__seq_eval_replace_all_rec, nextMatch, nextNo, mkConcat]
          have hRecNeWhole :
              __seq_eval_replace_all_rec whole b u (Term.Numeral 0) lent ≠
                Term.Stuck := by
            simpa [head, whole, mkConcat] using hRecNe
          have hRecEvalWhole :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__seq_eval_replace_all_rec whole b u
                      (Term.Numeral 0) lent)) =
                SmtValue.Seq sout := by
            simpa [head, whole, mkConcat] using hRecEval
          have hIteNe :
              __eo_ite (__seq_is_prefix b whole)
                  (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
                  (__eo_cons (Term.UOp UserOp.str_concat) head nextNo) ≠
                Term.Stuck := by
            simpa [hRecDef] using hRecNeWhole
          rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix b whole)
              (__eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch)
              (__eo_cons (Term.UOp UserOp.str_concat) head nextNo)
              hIteNe with hPref | hPref
          · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
              rw [hPref]
              simp
            have hPrefTerm : __seq_is_prefix b whole = Term.Boolean true :=
              hPref
            have hPrefEval :
                __seq_is_prefix b whole =
                  Term.Boolean
                    (native_seq_prefix_eq (native_unpack_seq sb)
                      (native_unpack_seq sa)) :=
              seq_prefix_eq_bool_native M hM b whole T sb sa hTNN hBTy
                hWholeTy hBEval (by simpa [head, whole] using hAEval)
                hPrefNe
            rw [hPrefEval] at hPref
            injection hPref with hNativePref
            have hNativePrefCons :
                native_seq_prefix_eq (native_unpack_seq sb)
                    (RuleProofs.seqElemVal M head ::
                      native_unpack_seq stail) =
                  true := by
              simpa [hWholeUnpCons] using hNativePref
            have hConcatNe :
                __eo_list_concat (Term.UOp UserOp.str_concat) u nextMatch ≠
                  Term.Stuck := by
              simpa [hPrefTerm, eo_ite_true] using hIteNe
            have hConcatLists :=
              eo_list_concat_str_concat_lists_of_ne_stuck u nextMatch
                hConcatNe
            have hNextNe : nextMatch ≠ Term.Stuck :=
              term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
                nextMatch hConcatLists.2
            have hMinusTy :
                __smtx_typeof
                    (__eo_to_smt (Term.Numeral (-1 : native_Int))) =
                  SmtType.Int := by
              change __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            have hAddNe :
                __eo_add lent (Term.Numeral (-1 : native_Int)) ≠
                  Term.Stuck :=
              seq_eval_replace_all_rec_skip_ne_stuck_of_ne_stuck tail b u
                (__eo_add lent (Term.Numeral (-1 : native_Int))) lent
                (by simpa [nextMatch] using hNextNe)
            have hLentTy :
                __smtx_typeof (__eo_to_smt lent) = SmtType.Int := by
              rw [hLent]
              change __smtx_typeof
                  (SmtTerm.Numeral
                    (Int.ofNat (native_unpack_seq sb).length)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            have hAddTy :
                __smtx_typeof
                    (__eo_to_smt
                      (__eo_add lent (Term.Numeral (-1 : native_Int)))) =
                  SmtType.Int := by
              rcases eo_add_int_args_numerals_of_ne_stuck lent
                  (Term.Numeral (-1 : native_Int)) hLentTy hMinusTy
                  hAddNe with
                ⟨i, j, _hLentEq, _hMinusEq, hAddEq⟩
              rw [hAddEq]
              change __smtx_typeof (SmtTerm.Numeral (native_zplus i j)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            have hNextTy :
                __smtx_typeof (__eo_to_smt nextMatch) = SmtType.Seq T := by
              simpa [nextMatch] using
                smt_typeof_seq_eval_replace_all_rec_of_seq tail b u
                  (__eo_add lent (Term.Numeral (-1 : native_Int))) lent T
                  hTailTy hBTy hUTy hAddTy hLentTy
                  (by simpa [nextMatch] using hNextNe)
            rcases seq_eval_of_seq_type M hM nextMatch T hNextTy with
              ⟨sNext, hNextEval⟩
            have hBranchEval :
                __smtx_model_eval M
                    (__eo_to_smt
                      (__eo_list_concat (Term.UOp UserOp.str_concat) u
                        nextMatch)) =
                  SmtValue.Seq sout := by
              have hEval' := hRecEvalWhole
              rw [hRecDef, hPrefTerm, eo_ite_true] at hEval'
              exact hEval'
            have hConcatUnp :
                native_unpack_seq sout =
                  native_unpack_seq su ++ native_unpack_seq sNext := by
              exact eo_list_concat_str_concat_unpack_of_seq_evals M hM u
                nextMatch T su sNext sout hUTy hNextTy hUEval hNextEval
                hConcatNe hBranchEval
            have hLenPos : 0 < (native_unpack_seq sb).length := by
              cases hPat : native_unpack_seq sb with
              | nil =>
                  exact False.elim (hPatNe hPat)
              | cons _ _ =>
                  simp
            have hAddEq :
                __eo_add lent (Term.Numeral (-1 : native_Int)) =
                  Term.Numeral
                    (Int.ofNat ((native_unpack_seq sb).length - 1)) := by
              cases hLen : (native_unpack_seq sb).length with
              | zero =>
                  simp [hLen] at hLenPos
              | succ n =>
                  rw [hLent]
                  simp [hLen, __eo_add, native_zplus]
                  simpa [Int.ofNat_eq_natCast, Int.natCast_succ]
                    using Int.add_neg_cancel_right (Int.ofNat n) 1
            have hNextUnp :
                native_unpack_seq sNext =
                  native_seq_replace_all_chain (native_unpack_seq sb)
                    (native_unpack_seq su)
                    ((native_unpack_seq sb).length - 1)
                    (native_unpack_seq stail) :=
              ih b u (__eo_add lent (Term.Numeral (-1 : native_Int)))
                lent T stail sb su sNext
                ((native_unpack_seq sb).length - 1) hTNN hTailConst hTailTy
                hBTy hUTy hTailEval hBEval hUEval hAddEq hLent hPatNe
                (by simpa [nextMatch] using hNextNe)
                (by simpa [nextMatch] using hNextEval)
            rw [hConcatUnp, hNextUnp, hWholeUnpCons]
            simp [native_seq_replace_all_chain, hNativePrefCons]
          · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
              rw [hPref]
              simp
            have hPrefTerm : __seq_is_prefix b whole = Term.Boolean false :=
              hPref
            have hPrefEval :
                __seq_is_prefix b whole =
                  Term.Boolean
                    (native_seq_prefix_eq (native_unpack_seq sb)
                      (native_unpack_seq sa)) :=
              seq_prefix_eq_bool_native M hM b whole T sb sa hTNN hBTy
                hWholeTy hBEval (by simpa [head, whole] using hAEval)
                hPrefNe
            rw [hPrefEval] at hPref
            injection hPref with hNativePref
            have hNativePrefCons :
                native_seq_prefix_eq (native_unpack_seq sb)
                    (RuleProofs.seqElemVal M head ::
                      native_unpack_seq stail) =
                  false := by
              simpa [hWholeUnpCons] using hNativePref
            have hConsNe :
                __eo_cons (Term.UOp UserOp.str_concat) head nextNo ≠
                  Term.Stuck := by
              simpa [hPrefTerm, eo_ite_false] using hIteNe
            have hNextList :
                __eo_is_list (Term.UOp UserOp.str_concat) nextNo =
                  Term.Boolean true := by
              change __eo_requires
                  (__eo_is_list (Term.UOp UserOp.str_concat) nextNo)
                  (Term.Boolean true)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
                    nextNo) ≠
                Term.Stuck at hConsNe
              exact eo_requires_eq_of_ne_stuck
                (__eo_is_list (Term.UOp UserOp.str_concat) nextNo)
                (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
                  nextNo) hConsNe
            have hNextNe : nextNo ≠ Term.Stuck :=
              term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
                nextNo hNextList
            have hZeroTy :
                __smtx_typeof (__eo_to_smt (Term.Numeral 0)) =
                  SmtType.Int := by
              change __smtx_typeof (SmtTerm.Numeral (0 : native_Int)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            have hLentTy :
                __smtx_typeof (__eo_to_smt lent) = SmtType.Int := by
              rw [hLent]
              change __smtx_typeof
                  (SmtTerm.Numeral
                    (Int.ofNat (native_unpack_seq sb).length)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            have hNextTy :
                __smtx_typeof (__eo_to_smt nextNo) = SmtType.Seq T := by
              simpa [nextNo] using
                smt_typeof_seq_eval_replace_all_rec_of_seq tail b u
                  (Term.Numeral 0) lent T hTailTy hBTy hUTy hZeroTy
                  hLentTy (by simpa [nextNo] using hNextNe)
            rcases seq_eval_of_seq_type M hM nextNo T hNextTy with
              ⟨sNext, hNextEval⟩
            have hBranchEval :
                __smtx_model_eval M
                    (__eo_to_smt
                      (__eo_cons (Term.UOp UserOp.str_concat) head
                        nextNo)) =
                  SmtValue.Seq sout := by
              have hEval' := hRecEvalWhole
              rw [hRecDef, hPrefTerm, eo_ite_false] at hEval'
              exact hEval'
            have hConsEq :
                __eo_cons (Term.UOp UserOp.str_concat) head nextNo =
                  mkConcat head nextNo :=
              eo_requires_eq_result_of_ne_stuck
                (__eo_is_list (Term.UOp UserOp.str_concat) nextNo)
                (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head)
                  nextNo) hConsNe
            have hConsUnp :
                native_unpack_seq sout =
                  native_unpack_seq shead ++ native_unpack_seq sNext :=
              str_concat_unpack_of_seq_evals M head nextNo sout shead sNext
                hHeadEval hNextEval (by simpa [hConsEq] using hBranchEval)
            have hNextUnp :
                native_unpack_seq sNext =
                  native_seq_replace_all_chain (native_unpack_seq sb)
                    (native_unpack_seq su) 0 (native_unpack_seq stail) :=
              ih b u (Term.Numeral 0) lent T stail sb su sNext 0 hTNN
                hTailConst hTailTy hBTy hUTy hTailEval hBEval hUEval rfl
                hLent hPatNe (by simpa [nextNo] using hNextNe)
                (by simpa [nextNo] using hNextEval)
            rw [hConsUnp, hHeadUnp, hNextUnp, hWholeUnpCons]
            simp [native_seq_replace_all_chain, hNativePrefCons]
      | succ skipNat =>
          subst skip
          let next :=
            __seq_eval_replace_all_rec tail b u
              (__eo_add (Term.Numeral (Int.ofNat (skipNat + 1)))
                (Term.Numeral (-1 : native_Int))) lent
          have hSkipNeZero :
              (Int.ofNat (skipNat + 1) : native_Int) ≠ 0 := by
            rw [Int.ofNat_eq_natCast]
            exact Int.natCast_ne_zero.mpr
              (by simp)
          have hSkipTermNe :
              Term.Numeral (Int.ofNat (skipNat + 1)) ≠
                Term.Numeral (0 : native_Int) := by
            intro h
            injection h with hInt
            exact hSkipNeZero hInt
          have hRecSuccDef :
              __seq_eval_replace_all_rec whole b u
                  (Term.Numeral (Int.ofNat (skipNat + 1))) lent =
                next := by
            change __seq_eval_replace_all_rec (mkConcat head tail) b u
                  (Term.Numeral (Int.ofNat (skipNat + 1))) lent =
                next
            rw [Eo.__seq_eval_replace_all_rec.eq_7 b u
              (Term.Numeral (Int.ofNat (skipNat + 1))) lent head tail
              hBNe hUNe (by simp) hSkipTermNe hLentNe]
          have hRecNeWhole :
              __seq_eval_replace_all_rec whole b u
                  (Term.Numeral (Int.ofNat (skipNat + 1))) lent ≠
                Term.Stuck := by
            simpa [head, whole, mkConcat] using hRecNe
          have hRecEvalWhole :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__seq_eval_replace_all_rec whole b u
                      (Term.Numeral (Int.ofNat (skipNat + 1))) lent)) =
                SmtValue.Seq sout := by
            simpa [head, whole, mkConcat] using hRecEval
          have hNextNe : next ≠ Term.Stuck := by
            rw [← hRecSuccDef]
            exact hRecNeWhole
          have hBranchEval :
              __smtx_model_eval M (__eo_to_smt next) = SmtValue.Seq sout := by
            rw [← hRecSuccDef]
            exact hRecEvalWhole
          have hAddEq :
              __eo_add (Term.Numeral (Int.ofNat (skipNat + 1)))
                  (Term.Numeral (-1 : native_Int)) =
                Term.Numeral (Int.ofNat skipNat) := by
            change Term.Numeral
                ((Int.ofNat (skipNat + 1)) + (-1 : Int)) =
              Term.Numeral (Int.ofNat skipNat)
            congr
            simpa [Int.ofNat_eq_natCast, Int.natCast_succ]
              using Int.add_neg_cancel_right (Int.ofNat skipNat) 1
          have hNextUnp :
              native_unpack_seq sout =
                native_seq_replace_all_chain (native_unpack_seq sb)
                  (native_unpack_seq su) skipNat (native_unpack_seq stail) :=
            ih b u
              (__eo_add (Term.Numeral (Int.ofNat (skipNat + 1)))
                (Term.Numeral (-1 : native_Int))) lent T stail sb su sout
              skipNat hTNN hTailConst hTailTy hBTy hUTy hTailEval hBEval
              hUEval hAddEq hLent hPatNe
              (by simpa [next] using hNextNe)
              (by simpa [next] using hBranchEval)
          rw [hNextUnp, hWholeUnpCons]
          simp [native_seq_replace_all_chain]
  | case3 U =>
      intro b u skip lent T sa sb su sout skipNat _hTNN _hConst hATy
        hBTy hUTy hAEval _hBEval _hUEval hSkip hLent _hPatNe
        _hRecNe hRecEval
      let empty :=
        Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
      have hSourceNil : native_unpack_seq sa = [] :=
        seq_empty_uop1_unpack_nil_of_seq M
          (Term.Apply (Term.UOp UserOp.Seq) U) T sa hATy hAEval
      have hBNe : b ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq b T hBTy
      have hUNe : u ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq u T hUTy
      have hRecEmptyDef :
          __seq_eval_replace_all_rec empty b u skip lent = empty := by
        rw [hSkip, hLent]
        simp [empty, __seq_eval_replace_all_rec]
      have hRecEvalEmpty :
          __smtx_model_eval M (__eo_to_smt empty) = SmtValue.Seq sout := by
        simpa [empty, hRecEmptyDef] using hRecEval
      have hOutNil : native_unpack_seq sout = [] :=
        seq_empty_uop1_unpack_nil_of_seq M
          (Term.Apply (Term.UOp UserOp.Seq) U) T sout hATy hRecEvalEmpty
      rw [hOutNil, hSourceNil]
      cases skipNat <;> simp [native_seq_replace_all_chain]
  | case4 ss hStuck hNotConcat hNotEmpty =>
      intro b u skip lent T sa sb su sout skipNat _hTNN hConst _hATy
        _hBTy _hUTy _hAEval _hBEval _hUEval _hSkip _hLent _hPatNe
        _hRecNe _hRecEval
      rw [__is_seq_const_rec.eq_4 ss hStuck hNotConcat hNotEmpty] at hConst
      cases hConst

private theorem seq_eval_replace_all_rec_string_nil_stuck
    (b u skip lent : Term) :
    __seq_eval_replace_all_rec (Term.String []) b u skip lent =
      Term.Stuck := by
  by_cases hB : b = Term.Stuck
  · subst b
    simp [__seq_eval_replace_all_rec]
  by_cases hU : u = Term.Stuck
  · subst u
    simp [__seq_eval_replace_all_rec]
  by_cases hSkip : skip = Term.Stuck
  · subst skip
    simp [__seq_eval_replace_all_rec]
  by_cases hLent : lent = Term.Stuck
  · subst lent
    simp [__seq_eval_replace_all_rec]
  exact Eo.__seq_eval_replace_all_rec.eq_8
    (Term.String []) b u skip lent
    (by
      intro T h
      cases h)
    (by
      intro s1 s2 h
      cases h)
    hB hU hSkip
    (by
      intro s1 s2 h _
      cases h)
    hLent

private theorem eo_ite_stuck_stuck (c : Term) :
    __eo_ite c Term.Stuck Term.Stuck = Term.Stuck := by
  unfold __eo_ite
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · simp [hTrue, SmtEval.native_ite]
  · simp [hTrue, SmtEval.native_ite]

private theorem eo_list_concat_str_concat_stuck_right (u : Term) :
    __eo_list_concat (Term.UOp UserOp.str_concat) u Term.Stuck =
      Term.Stuck := by
  simp [__eo_list_concat, __eo_is_list, __eo_requires,
    SmtEval.native_ite, SmtEval.native_not, native_teq]

private theorem eo_cons_str_concat_stuck_tail (head : Term) :
    __eo_cons (Term.UOp UserOp.str_concat) head Term.Stuck =
      Term.Stuck := by
  simp [__eo_cons, __eo_is_list, __eo_requires,
    SmtEval.native_ite, native_teq]

private theorem str_nary_intro_const_rec_true_of_guard_replace_all_ne
    (t b u lent : Term) (T : SmtType)
    (hTNN : T ≠ SmtType.None)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hGuard : __is_seq_const t = Term.Boolean true)
    (hRecNe :
      __seq_eval_replace_all_rec (__str_nary_intro t) b u
          (Term.Numeral 0) lent ≠
        Term.Stuck) :
    __is_seq_const_rec (__str_nary_intro t) = Term.Boolean true := by
  by_cases htStuck : t = Term.Stuck
  · subst t
    simp [__is_seq_const] at hGuard
  by_cases hUnit : ∃ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    let tail := __seq_empty (__eo_typeof head)
    let whole := mkConcat head tail
    have hHeadTy :
        __smtx_typeof (__eo_to_smt head) = SmtType.Seq T := by
      simpa [head] using htTy
    have heTy :
        __smtx_typeof (__eo_to_smt e) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e) (A := T)
        hHeadTy).1
    have heNN : __smtx_typeof (__eo_to_smt e) ≠ SmtType.None := by
      rw [heTy]
      exact hTNN
    have hTypeMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation e heNN
    have heEoTyNe : __eo_typeof e ≠ Term.Stuck := by
      intro heStuck
      rw [heStuck] at hTypeMatch
      rw [heTy] at hTypeMatch
      simp [__eo_to_smt_type] at hTypeMatch
      exact hTNN hTypeMatch
    have hIntro :
        __str_nary_intro head = whole := by
      simpa [head, tail, whole, mkConcat] using
        RuleProofs.str_nary_intro_seqUnit_eq e heEoTyNe
    rw [hIntro] at hRecNe ⊢
    have hTailEmpty : __str_is_empty tail = Term.Boolean true := by
      simpa [tail] using
        RuleProofs.str_is_empty_seq_empty_typeof_of_seq head T hHeadTy
    rcases RuleProofs.str_is_empty_cases tail hTailEmpty with
      hTailExplicit | hTailString
    · rcases hTailExplicit with ⟨U, hTailShape⟩
      rw [show tail = __seq_empty (__eo_typeof head) by rfl] at hTailShape
      change
        __is_seq_const_rec
            (mkConcat head (__seq_empty (__eo_typeof head))) =
          Term.Boolean true
      rw [hTailShape]
      simp [head, __is_seq_const_rec]
    · have hBad :
          __seq_eval_replace_all_rec whole b u (Term.Numeral 0) lent =
            Term.Stuck := by
        rw [show tail = __seq_empty (__eo_typeof head) by rfl] at hTailString
        change
          __seq_eval_replace_all_rec
              (mkConcat head (__seq_empty (__eo_typeof head))) b u
              (Term.Numeral 0) lent =
            Term.Stuck
        rw [hTailString]
        by_cases hB : b = Term.Stuck
        · subst b
          simp [__seq_eval_replace_all_rec]
        by_cases hU : u = Term.Stuck
        · subst u
          simp [__seq_eval_replace_all_rec]
        by_cases hLent : lent = Term.Stuck
        · subst lent
          simp [__seq_eval_replace_all_rec]
        rw [Eo.__seq_eval_replace_all_rec.eq_6 b u lent head
          (Term.String []) hB hU hLent]
        rw [seq_eval_replace_all_rec_string_nil_stuck]
        rw [seq_eval_replace_all_rec_string_nil_stuck]
        rw [eo_list_concat_str_concat_stuck_right]
        rw [eo_cons_str_concat_stuck_tail]
        exact eo_ite_stuck_stuck
          (__seq_is_prefix b
            (((Term.UOp UserOp.str_concat).Apply head).Apply
              (Term.String [])))
      exact False.elim (hRecNe hBad)
  · have hRec : __is_seq_const_rec t = Term.Boolean true := by
      have hNotUnit :
          ∀ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
        intro e he
        exact hUnit ⟨e, he⟩
      rw [__is_seq_const.eq_3 t htStuck hNotUnit] at hGuard
      exact hGuard
    have hList :=
      RuleProofs.is_seq_const_rec_true_is_str_concat_list t hRec
    have hIntro : __str_nary_intro t = t :=
      str_nary_intro_eq_self_of_is_list t hList
    rw [hIntro]
    exact hRec

private theorem smt_seq_type_wf_of_typeof_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_type_wf (SmtType.Seq T) = true := by
  have hGood :=
    smt_term_result_seq_components_wf_of_non_none
      (__eo_to_smt x)
      (by
        unfold term_has_non_none_type
        rw [hxTy]
        exact seq_ne_none T)
  simpa [hxTy, type_result_seq_components_wf] using hGood

private theorem seq_empty_arg_smt_type_eq_of_type
    (A : Term) (T : SmtType)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq T) :
    __eo_to_smt_type A = SmtType.Seq T := by
  change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
      SmtType.Seq T at hTy
  cases hA : __eo_to_smt_type A with
  | Seq U =>
      simp [__eo_to_smt_seq_empty, hA] at hTy
      rw [smtx_typeof_seq_empty_term_eq] at hTy
      have hGuardNN :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) ≠
            SmtType.None := by
        rw [hTy]
        exact seq_ne_none T
      have hGuard :
          __smtx_typeof_guard_wf (SmtType.Seq U) (SmtType.Seq U) =
            SmtType.Seq U :=
        smtx_typeof_guard_wf_of_non_none (SmtType.Seq U) (SmtType.Seq U)
          hGuardNN
      rw [hGuard] at hTy
      injection hTy with hU
      subst U
      rfl
  | _ =>
      simp [__eo_to_smt_seq_empty, hA, TranslationProofs.smtx_typeof_none]
        at hTy

private theorem explicit_seq_empty_eq_of_same_seq_type
    (A B : Term) (T : SmtType)
    (hATy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq T)
    (hBTy :
      __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty B)) =
        SmtType.Seq T) :
    Term.UOp1 UserOp1.seq_empty A = Term.UOp1 UserOp1.seq_empty B := by
  have hSeqWF :
      __smtx_type_wf (SmtType.Seq T) = true :=
    smt_seq_type_wf_of_typeof_seq
      (Term.UOp1 UserOp1.seq_empty A) T hATy
  have hSeqComp :
      __smtx_type_wf_component (SmtType.Seq T) = true := by
    simpa [__smtx_type_wf] using hSeqWF
  have hSeqRec :
      __smtx_type_wf_rec (SmtType.Seq T) = true :=
    (smtx_type_wf_component_parts hSeqComp).2
  have hFieldWF :
      TranslationProofs.smtx_type_field_wf_rec (SmtType.Seq T)
        native_reflist_nil :=
    TranslationProofs.smtx_type_field_wf_rec_of_type_wf_rec hSeqRec
  have hAArg :
      __eo_to_smt_type A = SmtType.Seq T :=
    seq_empty_arg_smt_type_eq_of_type A T hATy
  have hBArg :
      __eo_to_smt_type B = SmtType.Seq T :=
    seq_empty_arg_smt_type_eq_of_type B T hBTy
  have hAB : A = B :=
    TranslationProofs.eo_to_smt_type_injective_of_field_wf_rec hAArg hBArg
      hFieldWF
  rw [hAB]

private def SeqFindPatternOk (b : Term) (T : SmtType) (sy : SmtSeq) : Prop :=
  ∀ A,
    __smtx_typeof (__eo_to_smt (Term.UOp1 UserOp1.seq_empty A)) =
        SmtType.Seq T ->
      native_unpack_seq sy = [] ->
        b = Term.UOp1 UserOp1.seq_empty A

private theorem seq_find_explicit_empty_eq_native_indexof_offset
    (M : SmtModel) (hM : model_wf M)
    (b n U : Term) (T : SmtType) (sy : SmtSeq) (off : Nat)
    (hEmptyTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.UOp1 UserOp1.seq_empty
              ((Term.UOp UserOp.Seq).Apply U))) =
        SmtType.Seq T)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy)
    (hPattern : SeqFindPatternOk b T sy)
    (hn : n = Term.Numeral (Int.ofNat off))
    (hFindNe :
      __seq_find
          (Term.UOp1 UserOp1.seq_empty
            ((Term.UOp UserOp.Seq).Apply U)) b n ≠ Term.Stuck) :
    __seq_find
        (Term.UOp1 UserOp1.seq_empty
          ((Term.UOp UserOp.Seq).Apply U)) b n =
      Term.Numeral
        (native_seq_indexof_offset [] (native_unpack_seq sy) off) := by
  let a :=
    Term.UOp1 UserOp1.seq_empty ((Term.UOp UserOp.Seq).Apply U)
  have hLeftNe : a ≠ Term.Stuck := by
    simp [a]
  have hRightNe : b ≠ Term.Stuck :=
    seq_find_right_ne_stuck_of_ne_stuck a b n
      (by simpa [a] using hFindNe)
  have hIndexNe : n ≠ Term.Stuck :=
    seq_find_index_ne_stuck_of_ne_stuck a b n
      (by simpa [a] using hFindNe)
  have hFindEq :
      __seq_find a b n =
        __eo_ite (__eo_eq a b) n (__eo_l_1___seq_find a b n) :=
    seq_find_eq_of_args_ne_stuck a b n hLeftNe hRightNe hIndexNe
  rw [hFindEq] at hFindNe ⊢
  rcases eo_ite_cases_of_ne_stuck (__eo_eq a b) n
      (__eo_l_1___seq_find a b n) hFindNe with hEq | hEq
  · have hBA : b = a :=
      eq_of_eo_eq_true_local a b hEq
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Seq (SmtSeq.empty T) := by
      simpa [a] using
        smtx_model_eval_seq_empty_term_of_type M
          ((Term.UOp UserOp.Seq).Apply U) T hEmptyTy
    have hSy : sy = SmtSeq.empty T := by
      rw [hBA, hAEval] at hBEval
      injection hBEval with hSeq
      exact hSeq.symm
    have hPatNil : native_unpack_seq sy = [] := by
      rw [hSy]
      simp [native_unpack_seq]
    rw [hEq, eo_ite_true, hn]
    rw [hPatNil]
    rw [native_seq_indexof_offset_of_prefix]
    simp [native_seq_prefix_eq]
  · have hPatNonempty : native_unpack_seq sy ≠ [] := by
      intro hPatEmpty
      have hb : b = a := by
        simpa [a] using hPattern
          ((Term.UOp UserOp.Seq).Apply U) hEmptyTy hPatEmpty
      rw [hb] at hEq
      have hSelf : native_teq a a = true := by
        simp [a, native_teq]
      simp [a, __eo_eq, hSelf] at hEq
    have hL1 :
        __eo_l_1___seq_find a b n = Term.Numeral (-1 : native_Int) := by
      simpa [a] using
        l1_seq_find_empty_eq_of_args_ne_stuck b n U hRightNe hIndexNe
    rw [hEq, eo_ite_false, hL1, native_seq_indexof_offset_nil_of_ne_empty
      (native_unpack_seq sy) off hPatNonempty]

private theorem guarded_intro_pattern_ok
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (T : SmtType) (sy : SmtSeq)
    (hTNN : T ≠ SmtType.None)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hGuard : __is_seq_const s = Term.Boolean true)
    (hBTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) =
        SmtType.Seq T)
    (hBEval :
      __smtx_model_eval M (__eo_to_smt (__str_nary_intro s)) =
        SmtValue.Seq sy) :
    SeqFindPatternOk (__str_nary_intro s) T sy := by
  intro A hEmptyTy hSyNil
  by_cases hsStuck : s = Term.Stuck
  · subst s
    simp [__is_seq_const] at hGuard
  by_cases hUnit : ∃ e, s = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    have hHeadTy :
        __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
          SmtType.Seq T := by
      simpa using hsTy
    have heTy :
        __smtx_typeof (__eo_to_smt e) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e) (A := T)
        hHeadTy).1
    have heNN : __smtx_typeof (__eo_to_smt e) ≠ SmtType.None := by
      rw [heTy]
      exact hTNN
    have hTypeMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation e heNN
    have heEoTyNe : __eo_typeof e ≠ Term.Stuck := by
      intro heStuck
      rw [heStuck] at hTypeMatch
      rw [heTy] at hTypeMatch
      simp [__eo_to_smt_type] at hTypeMatch
      exact hTNN hTypeMatch
    have hIntro :=
      RuleProofs.str_nary_intro_seqUnit_eq e heEoTyNe
    rw [hIntro] at hBTy hBEval
    have hSeqUnitTy :=
      RuleProofs.seqUnit_typeof_eq_of_arg_ne_stuck e heEoTyNe
    rcases seq_unit_concat_unpack_cons M hM e
        (__seq_empty (__eo_typeof
          (Term.Apply (Term.UOp UserOp.seq_unit) e))) T sy hTNN
        (by simpa using hBTy) (by simpa using hBEval) with
      ⟨rest, hUnp, _hElemTy⟩
    rw [hUnp] at hSyNil
    cases hSyNil
  · have hRec : __is_seq_const_rec s = Term.Boolean true := by
      have hNotUnit :
          ∀ e, s = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
        intro e he
        exact hUnit ⟨e, he⟩
      rw [__is_seq_const.eq_3 s hsStuck hNotUnit] at hGuard
      exact hGuard
    have hList :=
      RuleProofs.is_seq_const_rec_true_is_str_concat_list s hRec
    have hIntro : __str_nary_intro s = s :=
      str_nary_intro_eq_self_of_is_list s hList
    rw [hIntro] at hBTy hBEval ⊢
    rcases RuleProofs.is_seq_const_rec_true_cases s hRec with
      hConcat | hEmpty
    · rcases hConcat with ⟨e, tail, hShape⟩
      subst s
      rcases seq_unit_concat_unpack_cons M hM e tail T sy hTNN
          (by simpa using hBTy) (by simpa using hBEval) with
        ⟨rest, hUnp, _hElemTy⟩
      rw [hUnp] at hSyNil
      cases hSyNil
    · rcases hEmpty with ⟨U, hShape⟩
      subst s
      exact explicit_seq_empty_eq_of_same_seq_type
        ((Term.UOp UserOp.Seq).Apply U) A T hBTy hEmptyTy

private theorem seq_find_const_rec_eq_native_indexof_offset
    (M : SmtModel) (hM : model_wf M) :
    ∀ a b n T sx sy off,
      T ≠ SmtType.None ->
      __is_seq_const_rec a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt b) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sx ->
      __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy ->
      SeqFindPatternOk b T sy ->
      n = Term.Numeral (Int.ofNat off) ->
      __seq_find a b n ≠ Term.Stuck ->
      __seq_find a b n =
        Term.Numeral
          (native_seq_indexof_offset (native_unpack_seq sx)
            (native_unpack_seq sy) off) := by
  intro a
  induction a using __is_seq_const_rec.induct with
  | case1 =>
      intro b n T sx sy off hTNN hConst hATy hBTy hAEval hBEval
        hPattern hn hFindNe
      simp [__is_seq_const_rec] at hConst
  | case2 e ss ih =>
      intro b n T sx sy off hTNN hConst hATy hBTy hAEval hBEval
        hPattern hn hFindNe
      let head := Term.Apply (Term.UOp UserOp.seq_unit) e
      let whole := mkConcat head ss
      let next := __seq_find ss b (__eo_add n (Term.Numeral 1))
      have hTailConst : __is_seq_const_rec ss = Term.Boolean true := by
        simpa [head, whole, __is_seq_const_rec] using hConst
      have hLeftNe : whole ≠ Term.Stuck := by
        simp [whole, head, mkConcat]
      have hRightNe : b ≠ Term.Stuck :=
        seq_find_right_ne_stuck_of_ne_stuck whole b n
          (by simpa [whole, head, mkConcat] using hFindNe)
      have hIndexNe : n ≠ Term.Stuck :=
        seq_find_index_ne_stuck_of_ne_stuck whole b n
          (by simpa [whole, head, mkConcat] using hFindNe)
      have hFindEq :
          __seq_find whole b n =
            __eo_ite (__eo_eq whole b) n
              (__eo_l_1___seq_find whole b n) :=
        seq_find_eq_of_args_ne_stuck whole b n hLeftNe hRightNe hIndexNe
      change __seq_find whole b n =
        Term.Numeral
          (native_seq_indexof_offset (native_unpack_seq sx)
            (native_unpack_seq sy) off)
      rw [hFindEq] at hFindNe ⊢
      rcases eo_ite_cases_of_ne_stuck (__eo_eq whole b) n
          (__eo_l_1___seq_find whole b n) hFindNe with hEq | hEq
      · have hBWhole : b = whole :=
          eq_of_eo_eq_true_local whole b hEq
        have hSy : sy = sx := by
          rw [hBWhole, hAEval] at hBEval
          injection hBEval with hSeq
          exact hSeq.symm
        rw [hEq, eo_ite_true, hn, hSy]
        rw [native_seq_indexof_offset_of_prefix]
        exact native_seq_prefix_eq_self (native_unpack_seq sx)
      · have hL1Ne : __eo_l_1___seq_find whole b n ≠ Term.Stuck := by
          simpa [hEq, eo_ite_false] using hFindNe
        have hL1Eq :
            __eo_l_1___seq_find whole b n =
              __eo_ite (__seq_is_prefix b whole) n next := by
          simpa [whole, head, next, mkConcat] using
            l1_seq_find_concat_eq_of_args_ne_stuck head ss b n
              hRightNe hIndexNe
        rw [hL1Eq] at hL1Ne ⊢
        rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix b whole) n next
            hL1Ne with hPref | hPref
        · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
            rw [hPref]
            simp
          have hPrefTerm : __seq_is_prefix b whole = Term.Boolean true :=
            hPref
          have hPrefEval :=
            seq_prefix_eq_bool_native M hM b whole T sy sx hTNN hBTy
              (by simpa [whole, head, mkConcat] using hATy)
              hBEval (by simpa [whole, head, mkConcat] using hAEval)
              hPrefNe
          rw [hPrefEval] at hPref
          injection hPref with hNativePref
          rw [hEq, eo_ite_false, hPrefTerm, eo_ite_true, hn]
          rw [native_seq_indexof_offset_of_prefix
            (native_unpack_seq sx) (native_unpack_seq sy) off hNativePref]
        · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
            rw [hPref]
            simp
          have hPrefTerm : __seq_is_prefix b whole = Term.Boolean false :=
            hPref
          have hPrefEval :=
            seq_prefix_eq_bool_native M hM b whole T sy sx hTNN hBTy
              (by simpa [whole, head, mkConcat] using hATy)
              hBEval (by simpa [whole, head, mkConcat] using hAEval)
              hPrefNe
          rw [hPrefEval] at hPref
          injection hPref with hNativePref
          have hNextNe : next ≠ Term.Stuck := by
            simpa [hPrefTerm, eo_ite_false] using hL1Ne
          obtain ⟨_hHeadTy, hTailTy⟩ :=
            strConcat_args_of_seq_type head ss T
              (by simpa [whole, head, mkConcat] using hATy)
          rcases seq_eval_of_seq_type M hM ss T hTailTy with
            ⟨stail, hTailEval⟩
          obtain ⟨shead, hHeadEval, hHeadUnp⟩ :=
            RuleProofs.eval_seqUnitAtom M e
          have hUnpWhole :
              native_unpack_seq sx =
                __smtx_model_eval M (__eo_to_smt e) ::
                  native_unpack_seq stail := by
            have hConcat :=
              str_concat_unpack_of_seq_evals M head ss sx shead stail
                (by simpa [head] using hHeadEval) hTailEval
                (by simpa [whole, head, mkConcat] using hAEval)
            rw [hConcat, hHeadUnp]
            rfl
          have hAdd :
              __eo_add n (Term.Numeral 1) =
                Term.Numeral (Int.ofNat (off + 1)) := by
            rw [hn]
            simp [__eo_add, native_zplus]
          have hRec :=
            ih b (__eo_add n (Term.Numeral 1)) T stail sy (off + 1)
              hTNN hTailConst hTailTy hBTy hTailEval hBEval hPattern
              hAdd (by simpa [next] using hNextNe)
          rw [hEq, eo_ite_false, hPrefTerm, eo_ite_false]
          change __seq_find ss b (__eo_add n (Term.Numeral 1)) =
            Term.Numeral
              (native_seq_indexof_offset (native_unpack_seq sx)
                (native_unpack_seq sy) off)
          rw [hRec]
          have hNativePrefCons :
              native_seq_prefix_eq (native_unpack_seq sy)
                  (__smtx_model_eval M (__eo_to_smt e) ::
                    native_unpack_seq stail) =
                false := by
            simpa [hUnpWhole] using hNativePref
          rw [hUnpWhole]
          rw [native_seq_indexof_offset_cons_not_prefix
            (__smtx_model_eval M (__eo_to_smt e))
            (native_unpack_seq stail) (native_unpack_seq sy) off
            hNativePrefCons]
  | case3 U =>
      intro b n T sx sy off hTNN hConst hATy hBTy hAEval hBEval
        hPattern hn hFindNe
      have hUnp :
          native_unpack_seq sx = [] :=
        seq_empty_uop1_unpack_nil_of_seq M
          ((Term.UOp UserOp.Seq).Apply U) T sx hATy hAEval
      rw [hUnp]
      exact seq_find_explicit_empty_eq_native_indexof_offset M hM b n U T
        sy off hATy hBTy hBEval hPattern hn hFindNe
  | case4 ss hStuck hNotConcat hNotEmpty =>
      intro b n T sx sy off hTNN hConst hATy hBTy hAEval hBEval
        hPattern hn hFindNe
      rw [__is_seq_const_rec.eq_4 ss hStuck hNotConcat hNotEmpty] at hConst
      cases hConst

private theorem smt_seq_component_ne_none_of_typeof_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    T ≠ SmtType.None := by
  have hSeqWF :
      __smtx_type_wf (SmtType.Seq T) = true :=
    smt_seq_type_wf_of_typeof_seq x T hxTy
  intro hT
  subst T
  simp [__smtx_type_wf, __smtx_type_wf_component,
    __smtx_type_wf_rec, native_inhabited_type, native_Teq, SmtEval.native_and]
    at hSeqWF

private theorem seq_find_empty_string_tail_contra
    (M : SmtModel) (hM : model_wf M)
    (b n : Term) (T : SmtType) (sy : SmtSeq)
    (hTailTy :
      __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq T)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sy)
    (hPattern : SeqFindPatternOk b T sy)
    (hFindNe : __seq_find (Term.String []) b n ≠ Term.Stuck) :
    False := by
  have hLeftNe : (Term.String []) ≠ Term.Stuck := by simp
  have hRightNe : b ≠ Term.Stuck :=
    seq_find_right_ne_stuck_of_ne_stuck (Term.String []) b n hFindNe
  have hIndexNe : n ≠ Term.Stuck :=
    seq_find_index_ne_stuck_of_ne_stuck (Term.String []) b n hFindNe
  have hFindEq :
      __seq_find (Term.String []) b n =
        __eo_ite (__eo_eq (Term.String []) b) n
          (__eo_l_1___seq_find (Term.String []) b n) :=
    seq_find_eq_of_args_ne_stuck (Term.String []) b n
      hLeftNe hRightNe hIndexNe
  rw [hFindEq] at hFindNe
  rcases eo_ite_cases_of_ne_stuck (__eo_eq (Term.String []) b) n
      (__eo_l_1___seq_find (Term.String []) b n) hFindNe with hEq | hEq
  · have hBString : b = Term.String [] :=
      eq_of_eo_eq_true_local (Term.String []) b hEq
    have hStringTy :
        __smtx_typeof (__eo_to_smt (Term.String [])) =
          SmtType.Seq SmtType.Char := by
      change __smtx_typeof (SmtTerm.String []) =
        SmtType.Seq SmtType.Char
      rw [__smtx_typeof.eq_4]
      simp [native_string_valid, native_ite]
    rw [hStringTy] at hTailTy
    injection hTailTy with hT
    subst T
    have hStringEval :
        __smtx_model_eval M (__eo_to_smt (Term.String [])) =
          SmtValue.Seq (native_pack_string []) := by
      change __smtx_model_eval M (SmtTerm.String []) =
        SmtValue.Seq (native_pack_string [])
      rw [__smtx_model_eval.eq_4]
    have hSyNil : native_unpack_seq sy = [] := by
      rw [hBString, hStringEval] at hBEval
      injection hBEval with hSy
      subst sy
      simp [native_pack_string, Smtm.native_unpack_pack_seq]
    have hEmptyTy :
        __smtx_typeof
            (__eo_to_smt
              (Term.UOp1 UserOp1.seq_empty (__eo_typeof (Term.String [])))) =
          SmtType.Seq SmtType.Char :=
      smt_typeof_raw_seq_empty_typeof (Term.String []) SmtType.Char
        hStringTy
    have hBExplicit :
        b = Term.UOp1 UserOp1.seq_empty (__eo_typeof (Term.String [])) :=
      hPattern (__eo_typeof (Term.String [])) hEmptyTy hSyNil
    rw [hBString] at hBExplicit
    cases hBExplicit
  · have hL1Ne :
        __eo_l_1___seq_find (Term.String []) b n ≠ Term.Stuck := by
      simpa [hEq, eo_ite_false] using hFindNe
    have hL1Stuck :
        __eo_l_1___seq_find (Term.String []) b n = Term.Stuck := by
      cases b
      case Stuck => exact False.elim (hRightNe rfl)
      all_goals
        cases n
        case Stuck => exact False.elim (hIndexNe rfl)
        all_goals
          rw [__eo_l_1___seq_find.eq_def]
    exact hL1Ne hL1Stuck

private theorem seq_find_str_nary_intro_guarded_eq_native_indexof_offset
    (M : SmtModel) (hM : model_wf M)
    (t b n : Term) (T : SmtType) (sa sb : SmtSeq) (off : Nat)
    (hTNN : T ≠ SmtType.None)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hGuardT : __is_seq_const t = Term.Boolean true)
    (hATy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T)
    (hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Seq T)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (__str_nary_intro t)) =
        SmtValue.Seq sa)
    (hBEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sb)
    (hPattern : SeqFindPatternOk b T sb)
    (hn : n = Term.Numeral (Int.ofNat off))
    (hFindNe : __seq_find (__str_nary_intro t) b n ≠ Term.Stuck) :
    __seq_find (__str_nary_intro t) b n =
      Term.Numeral
        (native_seq_indexof_offset (native_unpack_seq sa)
          (native_unpack_seq sb) off) := by
  by_cases htStuck : t = Term.Stuck
  · subst t
    simp [__is_seq_const] at hGuardT
  by_cases hUnit : ∃ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e
  · rcases hUnit with ⟨e, rfl⟩
    let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    let tail := __seq_empty (__eo_typeof head)
    let whole := mkConcat head tail
    have hHeadTy :
        __smtx_typeof (__eo_to_smt head) = SmtType.Seq T := by
      simpa [head] using htTy
    have heTy :
        __smtx_typeof (__eo_to_smt e) = T :=
      (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e) (A := T)
        hHeadTy).1
    have heNN : __smtx_typeof (__eo_to_smt e) ≠ SmtType.None := by
      rw [heTy]
      exact hTNN
    have hTypeMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation e heNN
    have heEoTyNe : __eo_typeof e ≠ Term.Stuck := by
      intro heStuck
      rw [heStuck] at hTypeMatch
      rw [heTy] at hTypeMatch
      simp [__eo_to_smt_type] at hTypeMatch
      exact hTNN hTypeMatch
    have hIntro :=
      RuleProofs.str_nary_intro_seqUnit_eq e heEoTyNe
    rw [hIntro] at hATy hAEval hFindNe ⊢
    change __seq_find whole b n ≠ Term.Stuck at hFindNe
    change __seq_find whole b n =
      Term.Numeral
        (native_seq_indexof_offset (native_unpack_seq sa)
          (native_unpack_seq sb) off)
    have hLeftNe : whole ≠ Term.Stuck := by
      simp [whole, head, tail, mkConcat]
    have hRightNe : b ≠ Term.Stuck :=
      seq_find_right_ne_stuck_of_ne_stuck whole b n hFindNe
    have hIndexNe : n ≠ Term.Stuck :=
      seq_find_index_ne_stuck_of_ne_stuck whole b n hFindNe
    have hFindEq :
        __seq_find whole b n =
          __eo_ite (__eo_eq whole b) n
            (__eo_l_1___seq_find whole b n) :=
      seq_find_eq_of_args_ne_stuck whole b n
        hLeftNe hRightNe hIndexNe
    rw [hFindEq] at hFindNe ⊢
    rcases eo_ite_cases_of_ne_stuck (__eo_eq whole b) n
        (__eo_l_1___seq_find whole b n) hFindNe with hEq | hEq
    · have hBWhole : b = whole :=
        eq_of_eo_eq_true_local whole b hEq
      have hSb : sb = sa := by
        rw [hBWhole, hAEval] at hBEval
        injection hBEval with hSeq
        exact hSeq.symm
      rw [hEq, eo_ite_true, hn, hSb]
      rw [native_seq_indexof_offset_of_prefix]
      exact native_seq_prefix_eq_self (native_unpack_seq sa)
    · have hL1Ne : __eo_l_1___seq_find whole b n ≠ Term.Stuck := by
        simpa [hEq, eo_ite_false] using hFindNe
      let next := __seq_find tail b (__eo_add n (Term.Numeral 1))
      have hL1Eq :
          __eo_l_1___seq_find whole b n =
            __eo_ite (__seq_is_prefix b whole) n next := by
        simpa [whole, head, tail, next, mkConcat] using
          l1_seq_find_concat_eq_of_args_ne_stuck head tail b n
            hRightNe hIndexNe
      rw [hL1Eq] at hL1Ne ⊢
      rcases eo_ite_cases_of_ne_stuck (__seq_is_prefix b whole) n next
          hL1Ne with hPref | hPref
      · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
          rw [hPref]
          simp
        have hPrefTerm : __seq_is_prefix b whole = Term.Boolean true :=
          hPref
        have hPrefEval :=
          seq_prefix_eq_bool_native M hM b whole T sb sa hTNN hBTy
            (by simpa [whole, head, tail, mkConcat] using hATy)
            hBEval (by simpa [whole, head, tail, mkConcat] using hAEval)
            hPrefNe
        rw [hPrefEval] at hPref
        injection hPref with hNativePref
        rw [hEq, eo_ite_false, hPrefTerm, eo_ite_true, hn]
        rw [native_seq_indexof_offset_of_prefix
          (native_unpack_seq sa) (native_unpack_seq sb) off hNativePref]
      · have hPrefNe : __seq_is_prefix b whole ≠ Term.Stuck := by
          rw [hPref]
          simp
        have hPrefTerm : __seq_is_prefix b whole = Term.Boolean false :=
          hPref
        have hPrefEval :=
          seq_prefix_eq_bool_native M hM b whole T sb sa hTNN hBTy
            (by simpa [whole, head, tail, mkConcat] using hATy)
            hBEval (by simpa [whole, head, tail, mkConcat] using hAEval)
            hPrefNe
        rw [hPrefEval] at hPref
        injection hPref with hNativePref
        have hNextNe : next ≠ Term.Stuck := by
          simpa [hPrefTerm, eo_ite_false] using hL1Ne
        obtain ⟨_hHeadTy, hTailTy⟩ :=
          strConcat_args_of_seq_type head tail T
            (by simpa [whole, head, tail, mkConcat] using hATy)
        rcases seq_eval_of_seq_type M hM tail T hTailTy with
          ⟨stail, hTailEval⟩
        obtain ⟨shead, hHeadEval, hHeadUnp⟩ :=
          RuleProofs.eval_seqUnitAtom M e
        have hUnpWhole :
            native_unpack_seq sa =
              __smtx_model_eval M (__eo_to_smt e) ::
                native_unpack_seq stail := by
          have hConcat :=
            str_concat_unpack_of_seq_evals M head tail sa shead stail
              (by simpa [head] using hHeadEval) hTailEval
              (by simpa [whole, head, tail, mkConcat] using hAEval)
          rw [hConcat, hHeadUnp]
          rfl
        have hAdd :
            __eo_add n (Term.Numeral 1) =
              Term.Numeral (Int.ofNat (off + 1)) := by
          rw [hn]
          simp [__eo_add, native_zplus]
        have hTailEmpty :
            __str_is_empty tail = Term.Boolean true := by
          simpa [tail] using
            RuleProofs.str_is_empty_seq_empty_typeof_of_seq head T hHeadTy
        rcases RuleProofs.str_is_empty_cases tail hTailEmpty with
          hTailExplicit | hTailString
        · rcases hTailExplicit with ⟨U, hTailShape⟩
          have hTailNil : native_unpack_seq stail = [] :=
            seq_empty_uop1_unpack_nil_of_seq M
              ((Term.UOp UserOp.Seq).Apply U) T stail
              (by simpa [hTailShape] using hTailTy)
              (by simpa [hTailShape] using hTailEval)
          have hNext :
              __seq_find tail b (__eo_add n (Term.Numeral 1)) =
                Term.Numeral
                  (native_seq_indexof_offset []
                    (native_unpack_seq sb) (off + 1)) := by
            simpa [hTailShape] using
              seq_find_explicit_empty_eq_native_indexof_offset M hM b
                (__eo_add n (Term.Numeral 1)) U T sb (off + 1)
                (by simpa [hTailShape] using hTailTy) hBTy hBEval
                hPattern hAdd (by simpa [next, hTailShape] using hNextNe)
          rw [hEq, eo_ite_false, hPrefTerm, eo_ite_false]
          change __seq_find tail b (__eo_add n (Term.Numeral 1)) =
            Term.Numeral
              (native_seq_indexof_offset (native_unpack_seq sa)
                (native_unpack_seq sb) off)
          rw [hNext]
          have hNativePrefCons :
              native_seq_prefix_eq (native_unpack_seq sb)
                  (__smtx_model_eval M (__eo_to_smt e) ::
                    native_unpack_seq stail) =
                false := by
            simpa [hUnpWhole] using hNativePref
          rw [hUnpWhole]
          rw [native_seq_indexof_offset_cons_not_prefix
            (__smtx_model_eval M (__eo_to_smt e))
            (native_unpack_seq stail) (native_unpack_seq sb) off
            hNativePrefCons]
          rw [hTailNil]
        · have hBad :=
            seq_find_empty_string_tail_contra M hM b
              (__eo_add n (Term.Numeral 1)) T sb
              (by simpa [hTailString] using hTailTy) hBTy hBEval
              hPattern (by simpa [next, hTailString] using hNextNe)
          exact False.elim hBad
  · have hRec : __is_seq_const_rec t = Term.Boolean true := by
      have hNotUnit :
          ∀ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e → False := by
        intro e he
        exact hUnit ⟨e, he⟩
      rw [__is_seq_const.eq_3 t htStuck hNotUnit] at hGuardT
      exact hGuardT
    have hList :=
      RuleProofs.is_seq_const_rec_true_is_str_concat_list t hRec
    have hIntro : __str_nary_intro t = t :=
      str_nary_intro_eq_self_of_is_list t hList
    rw [hIntro] at hATy hAEval hFindNe ⊢
    exact seq_find_const_rec_eq_native_indexof_offset M hM t b n T
      sa sb off hTNN hRec hATy hBTy hAEval hBEval hPattern hn hFindNe

private theorem smtx_model_eval_not_is_neg_indexof_contains
    (M : SmtModel) (xs pat : List SmtValue) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_not
            (__eo_is_neg
              (Term.Numeral (native_seq_indexof xs pat 0))))) =
      SmtValue.Boolean (native_seq_contains xs pat) := by
  let idx := native_seq_indexof xs pat 0
  by_cases hNeg : idx < 0
  · have hNotLe : ¬ 0 ≤ idx := by
      intro hLe
      exact (Int.not_lt.mpr hLe) hNeg
    simp [idx, __eo_is_neg, __eo_not, native_seq_contains, native_zlt,
      SmtEval.native_zlt, SmtEval.native_not, __smtx_model_eval, hNeg,
      hNotLe]
  · have hLe : 0 ≤ idx := Int.not_lt.mp hNeg
    simp [idx, __eo_is_neg, __eo_not, native_seq_contains, native_zlt,
      SmtEval.native_zlt, SmtEval.native_not, __smtx_model_eval, hNeg,
      hLe]

private theorem seq_find_str_nary_intro_guarded_eq_native_indexof
    (M : SmtModel) (hM : model_wf M)
    (t s : Term) (T : SmtType) (sa sb : SmtSeq)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hGuardT : __is_seq_const t = Term.Boolean true)
    (hGuardS : __is_seq_const s = Term.Boolean true)
    (hATy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T)
    (hBTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (__str_nary_intro t)) =
        SmtValue.Seq sa)
    (hBEval :
      __smtx_model_eval M (__eo_to_smt (__str_nary_intro s)) =
        SmtValue.Seq sb)
    (hFindNe :
      __seq_find (__str_nary_intro t) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck) :
    __seq_find (__str_nary_intro t) (__str_nary_intro s)
        (Term.Numeral 0) =
      Term.Numeral
        (native_seq_indexof (native_unpack_seq sa)
          (native_unpack_seq sb) 0) := by
  have hTNN : T ≠ SmtType.None :=
    smt_seq_component_ne_none_of_typeof_seq t T htTy
  have hPattern :
      SeqFindPatternOk (__str_nary_intro s) T sb :=
    guarded_intro_pattern_ok M hM s T sb hTNN hsTy hGuardS
      hBTy hBEval
  have hOffset :=
    seq_find_str_nary_intro_guarded_eq_native_indexof_offset M hM
      t (__str_nary_intro s) (Term.Numeral 0) T sa sb 0 hTNN
      htTy hGuardT hATy hBTy hAEval hBEval hPattern rfl hFindNe
  simpa [native_seq_indexof_offset_zero] using hOffset

private theorem str_value_len_eval_seq_length
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hLenNe : __str_value_len x ≠ Term.Stuck) :
    ∃ sx n,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
        __str_value_len x = Term.Numeral n ∧
        n = Int.ofNat (native_unpack_seq sx).length := by
  rcases str_value_len_numeral_of_ne_stuck x hLenNe with ⟨nLen, hLen⟩
  rcases RuleProofs.value_len_numeral_cases x nLen hLen with
      ⟨w, hxString⟩ | ⟨e, ss, hxCons⟩ | ⟨U, hxEmpty⟩ | ⟨e, hxUnit⟩
  · subst x
    refine ⟨native_pack_string w, Int.ofNat w.length, ?_, ?_, ?_⟩
    · change __smtx_model_eval M (SmtTerm.String w) =
        SmtValue.Seq (native_pack_string w)
      rw [__smtx_model_eval.eq_4]
    · exact RuleProofs.str_value_len_string w
    · rw [RuleProofs.unpack_pack_string_map]
      simp
  · subst x
    let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    have hTailNe : __str_value_len ss ≠ Term.Stuck := by
      exact str_value_len_concat_tail_ne_stuck e ss (by simpa [head] using hLenNe)
    obtain ⟨hHeadTy, hTailTy⟩ :=
      strConcat_args_of_seq_type head ss T (by simpa [head] using hxTy)
    obtain ⟨stail, ntail, hTailEval, hTailLen, hNtail⟩ :=
      str_value_len_eval_seq_length M hM ss T hTailTy hTailNe
    obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
    obtain ⟨sxy, hWholeEval, hWholeUnp⟩ :=
      RuleProofs.concat_unpack M head ss shead stail hHeadEval hTailEval
    refine ⟨sxy, native_zplus (1 : native_Int) ntail,
      by simpa [head] using hWholeEval, ?_, ?_⟩
    · have hTailSeq :=
        RuleProofs.seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral
          e ss nLen (by simpa [head] using hLen)
      exact RuleProofs.str_value_len_concat_seqUnit_eq_add_tail e ss ntail
        hTailSeq hTailLen
    · rw [hWholeUnp, hHeadUnp, hNtail]
      simp [native_zplus]
      exact Int.add_comm 1 (Int.ofNat (native_unpack_seq stail).length)
  · subst x
    change __smtx_typeof
        (__eo_to_smt_seq_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
      SmtType.Seq T at hxTy
    have hEvalEmpty :
        __smtx_model_eval M
          (__eo_to_smt_seq_empty
            (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtValue.Seq (SmtSeq.empty T) := by
      change __smtx_model_eval M
        (__eo_to_smt_seq_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))) =
        SmtValue.Seq (SmtSeq.empty T)
      cases hTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) with
      | Seq A =>
          simp [__eo_to_smt_seq_empty, hTy] at hxTy ⊢
          rw [smtx_typeof_seq_empty_term_eq] at hxTy
          have hGuardNN :
              __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
                SmtType.None := by
            rw [hxTy]
            exact seq_ne_none T
          have hGuard :
              __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) =
                SmtType.Seq A :=
            smtx_typeof_guard_wf_of_non_none (SmtType.Seq A)
              (SmtType.Seq A) hGuardNN
          rw [hGuard] at hxTy
          injection hxTy with hA
          subst A
          rw [smtx_eval_seq_empty_term_eq]
      | _ =>
          simp [__eo_to_smt_seq_empty, hTy,
            TranslationProofs.smtx_typeof_none] at hxTy
    have hn0 : 0 = nLen := by
      simpa [__str_value_len, __is_seq_const, __is_seq_const_rec,
        __eo_is_str, __eo_is_str_internal, __eo_ite, native_teq,
        native_ite, SmtEval.native_ite, SmtEval.native_and,
        SmtEval.native_not, __eo_requires, __eo_list_len,
        RuleProofs.strConcat_is_list_explicit_seq_empty_seq,
        __eo_list_len_rec] using hLen
    refine ⟨SmtSeq.empty T, nLen, hEvalEmpty, hLen, ?_⟩
    rw [← hn0]
    simp [native_unpack_seq]
  · subst x
    obtain ⟨sa, hEval, hUnp⟩ := RuleProofs.eval_seqUnitAtom M e
    refine ⟨sa, 1, hEval, by simp [__str_value_len], ?_⟩
    rw [hUnp]
    simp
termination_by x

private theorem smt_typeof_str_rev_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)) =
      SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) = SmtType.Seq T
  rw [typeof_str_rev_eq, hxTy]
  simp [__smtx_typeof_seq_op_1]

private theorem str_nary_elim_list_rev_str_nary_intro_ne_stuck_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x)) ≠
      Term.Stuck := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRev
  have hRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro x) T
      hIntroList hIntroTy hRev
  have hRevList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x)) =
        Term.Boolean true :=
    eo_list_rev_result_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRev
  exact str_nary_elim_ne_stuck_of_list_seq
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x)) T
    hRevTy hRevList

private theorem smt_value_rel_str_rev_seq_unit_snoc
    (M : SmtModel) (hM : model_wf M)
    (e tail : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail)
          (Term.Apply (Term.UOp UserOp.seq_unit) e))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) tail)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hTailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tail)
    (SmtType.Seq T) hTailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hTailValTy with ⟨stail, hTailEval⟩
  obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
  have hTailSeqTy : __smtx_typeof_seq_value stail = SmtType.Seq T := by
    simpa [hTailEval, __smtx_typeof_value] using hTailValTy
  have hTailElem : __smtx_elem_typeof_seq_value stail = T :=
    elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
  have hHeadValTy := smt_model_eval_preserves_type M hM (__eo_to_smt head)
    (SmtType.Seq T) (by simpa [head] using hHeadTy) (seq_ne_none T)
    (type_inhabited_seq T)
  have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
    simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
  have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
    elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq]
  change __smtx_model_eval_eq
    (__smtx_model_eval_str_concat
      (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt tail)))
      (__smtx_model_eval M (__eo_to_smt head)))
    (__smtx_model_eval M
      (SmtTerm.str_rev (__eo_to_smt (mkConcat head tail)))) =
      SmtValue.Boolean true
  rw [__smtx_model_eval.eq_89, __smtx_model_eval.eq_89]
  rw [smtx_model_eval_str_concat_term_eq, hTailEval, hHeadEval]
  simp [__smtx_model_eval_str_rev, __smtx_model_eval_str_concat,
    native_seq_rev, native_seq_concat, hTailElem, hHeadElem, hHeadUnp,
    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, List.reverse_cons,
    __smtx_model_eval_eq, native_veq]

private theorem smt_value_rel_str_rev_list_nil_empty
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev (__smtx_model_eval M (__eo_to_smt nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  cases hEval : __smtx_model_eval M (__eo_to_smt nil) with
  | Seq s =>
      rw [hEval] at hNilRel
      cases s with
      | empty U =>
          simp [__smtx_model_eval_str_rev, __smtx_model_eval_eq,
            native_veq] at hNilRel ⊢
          subst T
          rfl
      | cons v vs =>
          simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | _ =>
      rw [hEval] at hNilRel
      simp [__smtx_model_eval_eq, native_veq] at hNilRel

private theorem smt_value_rel_str_rev_list_nil_empty_term
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt nil)))
    (SmtValue.Seq (SmtSeq.empty T))
  rw [__smtx_model_eval.eq_89]
  exact smt_value_rel_str_rev_list_nil_empty M nil T hNil hNilTy

private theorem smt_value_rel_seq_nil_to_str_rev
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt nil))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil))) := by
  have hNilEmpty := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  have hRevEmpty :=
    smt_value_rel_str_rev_list_nil_empty_term M nil T hNil hNilTy
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt nil))
    (SmtValue.Seq (SmtSeq.empty T))
    (__smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
    hNilEmpty
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
      (SmtValue.Seq (SmtSeq.empty T)) hRevEmpty)

private theorem smt_value_rel_seq_unit_to_str_rev
    (M : SmtModel) (hM : model_wf M) (e : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (Term.Apply (Term.UOp UserOp.seq_unit) e)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  obtain ⟨shead, hHeadEval, hHeadUnp⟩ := RuleProofs.eval_seqUnitAtom M e
  have hHeadValTy := smt_model_eval_preserves_type M hM (__eo_to_smt head)
    (SmtType.Seq T) (by simpa [head] using hHeadTy) (seq_ne_none T)
    (type_inhabited_seq T)
  have hHeadSeqTy : __smtx_typeof_seq_value shead = SmtType.Seq T := by
    simpa [head, hHeadEval, __smtx_typeof_value] using hHeadValTy
  have hHeadElem : __smtx_elem_typeof_seq_value shead = T :=
    elem_typeof_seq_value_of_typeof_seq_value hHeadSeqTy
  unfold RuleProofs.smt_value_rel
  change __smtx_model_eval_eq
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt head))) =
      SmtValue.Boolean true
  rw [__smtx_model_eval.eq_89, hHeadEval]
  simp only [__smtx_model_eval_str_rev, native_seq_rev, hHeadElem]
  rw [hHeadUnp]
  simp [List.reverse_cons, List.reverse_nil]
  rw [← hHeadUnp]
  change RuleProofs.smt_seq_rel shead
    (native_pack_seq T (native_unpack_seq shead))
  exact smt_seq_rel_pack_unpack T shead hHeadElem

private theorem smt_value_rel_elim_rev_seq_unit_cons_nil
    (M : SmtModel) (hM : model_wf M)
    (e nil : Term) (T : SmtType)
    (hHeadTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil) ≠
          Term.Stuck)
    (hElimCons :
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)) ≠
            Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) nil)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T (by simpa [head] using hHeadTy)
      hNilTy
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil
      (by simpa [head] using hRevCons)
  have hElimCons' : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevConsEq, head] using hElimCons
  have hLhsToCons : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T hConsTy
      hElimCons'
  have hConsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T
      (by simpa [head] using hHeadTy) hNil hNilTy
  have hRevNilTy :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev) nil)) = SmtType.Seq T :=
    smt_typeof_str_rev_of_seq nil T hNilTy
  have hRevNilEmpty :=
    smt_value_rel_str_rev_list_nil_empty_term M nil T hNil hNilTy
  have hConcatRevNilHeadToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_left_of_rel_empty M hM
      (Term.Apply (Term.UOp UserOp.str_rev) nil) head T
      hRevNilTy (by simpa [head] using hHeadTy) hRevNilEmpty
  have hSnoc :=
    smt_value_rel_str_rev_seq_unit_snoc M hM e nil T
      (by simpa [head] using hHeadTy) hNilTy
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_model_eval M (__eo_to_smt
      (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head nil))))
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead)
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head nil))))
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) nil) head)))
        (__smtx_model_eval M (__eo_to_smt head)) hConcatRevNilHeadToHead)
      (by simpa [head] using hSnoc))

private theorem smt_value_rel_elim_rev_seq_unit_list
    (M : SmtModel) (hM : model_wf M)
    (ss e : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat)
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss) =
          Term.Boolean true)
    (hConsTy :
      __smtx_typeof (__eo_to_smt
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)) =
          SmtType.Seq T)
    (hLenEx :
      ∃ n, __str_value_len
        (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss) =
          Term.Numeral n) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)) ≠
        Term.Stuck ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)))))
        (__smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_rev)
            (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e) ss)))) := by
  let head := Term.Apply (Term.UOp UserOp.seq_unit) e
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) ss = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
      head ss (by simpa [head] using hList)
  obtain ⟨hHeadTy, hTailTy⟩ :=
    strConcat_args_of_seq_type head ss T (by simpa [head] using hConsTy)
  rcases hLenEx with ⟨n, hLen⟩
  have hTailLenEx : ∃ m, __str_value_len ss = Term.Numeral m := by
    simpa [head] using
      RuleProofs.value_len_tail_numeral_of_concat_seqUnit e ss n
        (by simpa [head] using hLen)
  rcases hTailLenEx with ⟨m, hTailLen⟩
  rcases RuleProofs.value_len_numeral_cases ss m hTailLen with
      ⟨w, hs⟩ | ⟨e2, ss2, hs⟩ | ⟨U, hs⟩ | ⟨e2, hs⟩
  · subst ss
    cases w with
    | nil =>
        let nil := Term.String []
        have hNil :
            __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
              Term.Boolean true := by
          simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat,
            __eo_eq, native_teq]
        have hRevCons :
            __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
              Term.Stuck :=
          eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
            (mkConcat head nil) (by simpa [head, nil] using hList)
        have hElimCons :
            __str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (mkConcat head nil)) ≠ Term.Stuck :=
          str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head nil T
            (by simpa [head, nil] using hConsTy) hRevCons
        exact ⟨by simpa [head, nil] using hElimCons,
          by simpa [head, nil] using
            smt_value_rel_elim_rev_seq_unit_cons_nil M hM e nil T
              hHeadTy hNil (by simpa [nil] using hTailTy)
              hRevCons hElimCons⟩
    | cons ch rest =>
        simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
          __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
          native_teq, native_ite, SmtEval.native_ite, native_not,
          SmtEval.native_not] at hTailList
  · subst ss
    let tailHead := Term.Apply (Term.UOp UserOp.seq_unit) e2
    let tail := mkConcat tailHead ss2
    have hRevCons :
        __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
          Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        (mkConcat head tail) (by simpa [head, tail, tailHead] using hList)
    have hElimCons :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat head tail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head tail T
        (by simpa [head, tail, tailHead] using hConsTy) hRevCons
    refine ⟨by simpa [head, tail, tailHead] using hElimCons, ?_⟩
    have hTailLenEx' : ∃ m, __str_value_len tail = Term.Numeral m :=
      ⟨m, by simpa [tail, tailHead] using hTailLen⟩
    obtain ⟨hElimTail, hTailRel⟩ :=
      smt_value_rel_elim_rev_seq_unit_list M hM ss2 e2 T
        (by simpa [tail, tailHead] using hTailList)
        (by simpa [tail, tailHead] using hTailTy)
        hTailLenEx'
    have hRevTail :
        __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        tail (by simpa [tail, tailHead] using hTailList)
    have hConsToSnoc : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat head tail)))))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
            head))) := by
      have hInterp :=
        eo_interprets_rev_cons_snoc_of_seq M hM head tail T hHeadTy
          (by simpa [tail, tailHead] using hTailList)
          (by simpa [tail, tailHead] using hTailTy)
          hRevCons hRevTail hElimCons hElimTail
      exact RuleProofs.eo_interprets_eq_rel M
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head) hInterp
    have hElimTailTy :
        __smtx_typeof (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) tail))) =
          SmtType.Seq T :=
      smt_typeof_str_nary_elim_list_rev_of_seq tail T
        (by simpa [tail, tailHead] using hTailList)
        (by simpa [tail, tailHead] using hTailTy)
        hRevTail hElimTail
    have hRevTailTy :
        __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) tail)) =
          SmtType.Seq T :=
      smt_typeof_str_rev_of_seq tail T
        (by simpa [tail, tailHead] using hTailTy)
    have hSnocCong : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
            head)))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail) head))) :=
      strConcat_smt_value_rel_left_congr M hM
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
        (Term.Apply (Term.UOp UserOp.str_rev) tail) head T
        hElimTailTy hRevTailTy hHeadTy hTailRel
    have hSnoc :=
      smt_value_rel_str_rev_seq_unit_snoc M hM e tail T hHeadTy
        (by simpa [tail, tailHead] using hTailTy)
    exact RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))))
      (__smtx_model_eval M (__eo_to_smt
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head tail))))
      hConsToSnoc
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
            head)))
        (__smtx_model_eval M (__eo_to_smt
          (mkConcat (Term.Apply (Term.UOp UserOp.str_rev) tail) head)))
        (__smtx_model_eval M (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_rev) (mkConcat head tail))))
        hSnocCong hSnoc)
  · subst ss
    let nil := Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true := by
      simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat]
    have hRevCons :
        __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
          Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        (mkConcat head nil) (by simpa [head, nil] using hList)
    have hElimCons :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat head nil)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq head nil T
        (by simpa [head, nil] using hConsTy) hRevCons
    exact ⟨by simpa [head, nil] using hElimCons,
      by simpa [head, nil] using
        smt_value_rel_elim_rev_seq_unit_cons_nil M hM e nil T
          hHeadTy hNil (by simpa [nil] using hTailTy)
          hRevCons hElimCons⟩
  · subst ss
    simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_ok,
      __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq,
      native_ite, SmtEval.native_ite, native_not, SmtEval.native_not]
      at hTailList
termination_by ss

private theorem smt_value_rel_elim_rev_str_nary_intro_to_str_rev
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (T : SmtType)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hGuard : __is_seq_const t = Term.Boolean true)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hIntroNe : __str_nary_intro t ≠ Term.Stuck)
    (hRevNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck)
    (hOutNe :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t))) := by
  let a := __str_nary_intro t
  let r := __eo_list_rev (Term.UOp UserOp.str_concat) a
  let out := __str_nary_elim r
  have hIntroTy :
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
    simpa [a] using
      smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
        (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
  rcases str_value_len_numeral_of_is_seq_const_true t hGuard with
    ⟨n, hLen⟩
  rcases RuleProofs.value_len_numeral_cases t n hLen with
    ⟨w, ht⟩ | ⟨e, ss, ht⟩ | ⟨U, ht⟩ | ⟨e, ht⟩
  · subst t
    simp [__is_seq_const, __is_seq_const_rec] at hGuard
  · subst t
    let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    have hTailSeq :=
      RuleProofs.seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral
        e ss n (by simpa [head] using hLen)
    have hRawSeq :
        __is_seq_const_rec (mkConcat head ss) = Term.Boolean true := by
      simp [head, __is_seq_const_rec, hTailSeq]
    have hRawList :
        __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head ss) =
          Term.Boolean true :=
      RuleProofs.is_seq_const_rec_true_is_str_concat_list
        (mkConcat head ss) hRawSeq
    have hIntroEq : a = mkConcat head ss := by
      simp [a, head, __eo_list_singleton_intro, hRawList, eo_ite_true]
    simpa [out, r, a, head, hIntroEq, mkConcat] using
      (smt_value_rel_elim_rev_seq_unit_list M hM ss e T hRawList
        (by simpa [head] using htTy)
        ⟨n, by simpa [head] using hLen⟩).2
  · subst t
    let nil :=
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
          Term.Boolean true := by
      simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat]
    have hNotConcat : ¬ ∃ head tail : Term, nil = mkConcat head tail := by
      intro hConcat
      rcases hConcat with ⟨head, tail, hEq⟩
      change
        Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail
        at hEq
      cases hEq
    have hRevEq :
        __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_nary_intro nil) =
          __str_nary_intro nil :=
      eo_list_rev_str_nary_intro_eq_of_not_str_concat nil hNotConcat
        (by simpa [nil, a] using hIntroNe)
        (by simpa [nil, a, r] using hRevNe)
    have hElimIntroNe :
        __str_nary_elim (__str_nary_intro nil) ≠ Term.Stuck := by
      simpa [nil, a, r, out, hRevEq] using hOutNe
    have hInterp :=
      eo_interprets_str_nary_elim_intro_eq_of_seq M hM nil T
        (by simpa [nil] using htTy)
        (by simpa [nil, a] using hIntroNN)
        (by simpa [nil, a] using hIntroNe)
        hElimIntroNe
    have hOutToNil : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt out))
        (__smtx_model_eval M (__eo_to_smt nil)) := by
      have hRel :=
        RuleProofs.eo_interprets_eq_rel M
          (__str_nary_elim (__str_nary_intro nil)) nil hInterp
      simpa [nil, a, r, out, hRevEq] using hRel
    have hNilToRev :=
      smt_value_rel_seq_nil_to_str_rev M nil T hNil
        (by simpa [nil] using htTy)
    exact RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt out))
      (__smtx_model_eval M (__eo_to_smt nil))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
      hOutToNil hNilToRev
  · subst t
    let head := Term.Apply (Term.UOp UserOp.seq_unit) e
    have hNotConcat : ¬ ∃ x y : Term, head = mkConcat x y := by
      intro hConcat
      rcases hConcat with ⟨x, y, hEq⟩
      change Term.Apply (Term.UOp UserOp.seq_unit) e =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y at hEq
      injection hEq with hFun _hArg
      cases hFun
    have hRevEq :
        __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_nary_intro head) =
          __str_nary_intro head :=
      eo_list_rev_str_nary_intro_eq_of_not_str_concat head hNotConcat
        (by simpa [head, a] using hIntroNe)
        (by simpa [head, a, r] using hRevNe)
    have hElimIntroNe :
        __str_nary_elim (__str_nary_intro head) ≠ Term.Stuck := by
      simpa [head, a, r, out, hRevEq] using hOutNe
    have hInterp :=
      eo_interprets_str_nary_elim_intro_eq_of_seq M hM head T
        (by simpa [head] using htTy)
        (by simpa [head, a] using hIntroNN)
        (by simpa [head, a] using hIntroNe)
        hElimIntroNe
    have hOutToHead : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt out))
        (__smtx_model_eval M (__eo_to_smt head)) := by
      have hRel :=
        RuleProofs.eo_interprets_eq_rel M
          (__str_nary_elim (__str_nary_intro head)) head hInterp
      simpa [head, a, r, out, hRevEq] using hRel
    have hHeadToRev :=
      smt_value_rel_seq_unit_to_str_rev M hM e T
        (by simpa [head] using htTy)
    exact RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt out))
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) head)))
      hOutToHead hHeadToRev

set_option linter.unusedSimpArgs false in
private theorem seq_eval_smt_type_and_value_rel
    (M : SmtModel) (hM : model_wf M) :
    ∀ t,
      __seq_eval t ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (__seq_eval t)) =
          __smtx_typeof (__eo_to_smt t) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
          (__smtx_model_eval M (__eo_to_smt t)) := by
  intro t hEvalNe hNN
  induction t using __seq_eval.induct with
  | case1 =>
      simp [__seq_eval] at hEvalNe
  | case2 t n =>
      let a := __str_nary_intro t
      let nth := __eo_list_nth (Term.UOp UserOp.str_concat) a n
      let guard := __is_seq_const t
      have hReqNe :
          __eo_requires guard (Term.Boolean true)
              (__seq_element_of_unit nth) ≠ Term.Stuck := by
        simpa [__seq_eval, a, nth, guard] using hEvalNe
      have hGuardTerm : guard = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guard (Term.Boolean true)
          (__seq_element_of_unit nth) hReqNe
      have hSeqEvalResult :
          __seq_eval (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) t) n) =
            __seq_element_of_unit nth := by
        simpa [__seq_eval, a, nth, guard] using
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true)
            (__seq_element_of_unit nth) hReqNe
      have hElemNe : __seq_element_of_unit nth ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          (__seq_element_of_unit nth) hReqNe
      rcases seq_element_of_unit_eq_of_ne_stuck nth hElemNe with
        ⟨e, hNthUnit, hElemEq⟩
      have hNthNe : nth ≠ Term.Stuck := by
        intro hStuck
        rw [hStuck] at hElemNe
        simp [__seq_element_of_unit] at hElemNe
      have hSeqNthNN :
          term_has_non_none_type
            (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_nth_args_of_non_none hSeqNthNN with
        ⟨T, htTy, hnTy⟩
      have hList :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true :=
        eo_list_nth_is_list_true_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hIntroNe : a ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) a hList
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
      have hNthRecEq :
          nth = __eo_list_nth_rec a n :=
        eo_list_nth_eq_rec_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hNthRecNe :
          __eo_list_nth_rec a n ≠ Term.Stuck :=
        eo_list_nth_rec_ne_stuck_of_ne_stuck
          (Term.UOp UserOp.str_concat) a n hNthNe
      have hNthRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_nth_rec a n)) =
            SmtType.Seq T :=
        smt_typeof_list_nth_rec_str_concat_of_seq a n T hList hATy
          hNthRecNe
      have hSeqUnitTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
            SmtType.Seq T := by
        rw [← hNthUnit, hNthRecEq]
        exact hNthRecTy
      have hETy : __smtx_typeof (__eo_to_smt e) = T :=
        (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt e)
          (A := T) hSeqUnitTy).1
      have hGuardNN :
          __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        have hSeqNthTy :
            __smtx_typeof
                (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)) =
              __smtx_typeof_guard_wf T T := by
          rw [typeof_seq_nth_eq, htTy, hnTy]
          rfl
        unfold term_has_non_none_type at hSeqNthNN
        rw [hSeqNthTy] at hSeqNthNN
        exact hSeqNthNN
      have hGuard :
          __smtx_typeof_guard_wf T T = T :=
        smtx_typeof_guard_wf_of_non_none T T hGuardNN
      have hEvalEq :
          __seq_eval (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) t) n) =
            e := by
        rw [hSeqEvalResult]
        exact hElemEq
      constructor
      · rw [hEvalEq]
        change __smtx_typeof (__eo_to_smt e) =
          __smtx_typeof (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n))
        rw [hETy, typeof_seq_nth_eq, htTy, hnTy]
        change T = __smtx_typeof_guard_wf T T
        rw [hGuard]
      · rw [hEvalEq]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt e))
          (__smtx_model_eval M
            (SmtTerm.seq_nth (__eo_to_smt t) (__eo_to_smt n)))
        rw [smtx_model_eval_seq_nth_term]
        have hNthRecUnit :
            __eo_list_nth_rec a n =
              Term.Apply (Term.UOp UserOp.seq_unit) e := by
          rw [← hNthRecEq]
          exact hNthUnit
        have hFinish :
            __str_value_len a ≠ Term.Stuck ->
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt e))
                (__smtx_seq_nth M
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt n))) := by
          intro hLenA
          have hRelA :=
            smt_value_rel_seq_nth_list_rec_of_value_len M hM a n e T
              hList hATy hLenA hNthRecUnit hnTy
          have hIntroRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt t)) :=
            smt_value_rel_str_nary_intro M hM t T htTy
              (by simpa [a] using hIntroNe)
          have hCong :=
            smt_value_rel_seq_nth_left_congr M hM a t n T hATy htTy
              hnTy hIntroRel
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt e))
            (__smtx_seq_nth M
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt n)))
            (__smtx_seq_nth M
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval M (__eo_to_smt n))) hRelA hCong
        rcases str_value_len_numeral_of_is_seq_const_true t
            (by simpa [guard] using hGuardTerm) with
          ⟨len, hLenT⟩
        have hLenTNe : __str_value_len t ≠ Term.Stuck := by
          rw [hLenT]
          simp
        rcases RuleProofs.value_len_numeral_cases t len hLenT with
            ⟨w, htString⟩ | ⟨head, tail, htCons⟩ |
            ⟨U, htEmpty⟩ | ⟨head, htUnit⟩
        · subst t
          simp [guard, __is_seq_const, __is_seq_const_rec] at hGuardTerm
        · subst t
          have hTailTy :
              __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T :=
            (strConcat_args_of_seq_type
              (Term.Apply (Term.UOp UserOp.seq_unit) head) tail T
              (by simpa using htTy)).2
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) tail =
                Term.Boolean true :=
            list_nth_rec_intro_seqUnit_concat_eq_unit_tail_list head tail n e
              (term_ne_stuck_of_smt_type_seq tail T hTailTy)
              (by simpa [a] using hNthRecUnit)
          exact hFinish
            (by
              simpa [a, str_nary_intro_concat_eq
                (Term.Apply (Term.UOp UserOp.seq_unit) head) tail hTailList]
                using hLenTNe)
        · subst t
          have hStuck : __seq_element_of_unit nth = Term.Stuck := by
            simpa [a, nth] using
              seq_element_list_nth_intro_seq_empty_stuck U n
          exact False.elim (hElemNe hStuck)
        · subst t
          have hHeadTy :
              __smtx_typeof
                  (__eo_to_smt
                    (Term.Apply (Term.UOp UserOp.seq_unit) head)) =
                SmtType.Seq T := by
            simpa using htTy
          have hHeadArgTy :=
            (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt head)
              (A := T) hHeadTy).1
          have hHeadEoTyNe : __eo_typeof head ≠ Term.Stuck := by
            intro hHeadStuck
            have hHeadNN : __smtx_typeof (__eo_to_smt head) ≠ SmtType.None := by
              rw [hHeadArgTy]
              exact (seq_unit_type_eq_arg_of_eq (t := __eo_to_smt head)
                (A := T) hHeadTy).2
            have hTypeMatch :=
              TranslationProofs.eo_to_smt_typeof_matches_translation head hHeadNN
            rw [hHeadStuck] at hTypeMatch
            have hNone :
                __smtx_typeof (__eo_to_smt head) = SmtType.None := by
              simpa [__eo_to_smt_type, TranslationProofs.smtx_typeof_none]
                using hTypeMatch
            exact hHeadNN hNone
          have hIntroEq :=
            RuleProofs.str_nary_intro_seqUnit_eq head hHeadEoTyNe
          have hNthSingleton :
              __eo_list_nth_rec
                  (mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) head)
                    (__seq_empty
                      (__eo_typeof
                        (Term.Apply (Term.UOp UserOp.seq_unit) head)))) n =
                Term.Apply (Term.UOp UserOp.seq_unit) e := by
            simpa [a, hIntroEq, mkConcat] using hNthRecUnit
          have hTy :=
            RuleProofs.seqUnit_typeof_eq_of_arg_ne_stuck head hHeadEoTyNe
          rw [hTy] at hNthSingleton
          cases n
          case Numeral i =>
            by_cases hi : i = 0
            · have hUnitEq :
                  Term.Apply (Term.UOp UserOp.seq_unit) head =
                    Term.Apply (Term.UOp UserOp.seq_unit) e := by
                simpa only [hi, mkConcat, __eo_list_nth_rec] using
                  hNthSingleton
              have hHeadEq : head = e := by
                injection hUnitEq
              have hIndexEval :
                  __smtx_model_eval M (__eo_to_smt (Term.Numeral i)) =
                    SmtValue.Numeral 0 := by
                calc
                  __smtx_model_eval M (__eo_to_smt (Term.Numeral i))
                      = SmtValue.Numeral i := by
                    rw [show __eo_to_smt (Term.Numeral i) =
                      SmtTerm.Numeral i by rfl]
                    exact __smtx_model_eval.eq_2 M i
                  _ = SmtValue.Numeral 0 := congrArg SmtValue.Numeral hi
              rw [← hHeadEq]
              rw [smtx_model_eval_seq_unit_term]
              rw [hIndexEval]
              exact RuleProofs.smt_value_rel_refl _
            · exfalso
              cases hHeadTyCase : __eo_typeof head <;>
                simp [mkConcat, __seq_empty, __eo_list_nth_rec, __eo_add,
                  hHeadTyCase, hi] at hNthSingleton
              all_goals
                try
                  rename_i op
                  cases op <;>
                    simp [mkConcat, __seq_empty, __eo_list_nth_rec, __eo_add,
                      hHeadTyCase, hi] at hNthSingleton
          all_goals
            exfalso
            cases hHeadTyCase : __eo_typeof head <;>
              simp [mkConcat, __seq_empty, __eo_list_nth_rec, __eo_add,
                hHeadTyCase] at hNthSingleton
            all_goals
              try
                rename_i op
                cases op <;>
                  simp [mkConcat, __seq_empty, __eo_list_nth_rec, __eo_add,
                    hHeadTyCase] at hNthSingleton
  | case3 t =>
      have hLenNe : __str_value_len (__str_nary_intro t) ≠ Term.Stuck := by
        simpa [__seq_eval] using hEvalNe
      rcases str_value_len_numeral_of_ne_stuck (__str_nary_intro t) hLenNe with
        ⟨n, hLen⟩
      have hLenTermNN :
          term_has_non_none_type (SmtTerm.str_len (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
          (typeof_str_len_eq (__eo_to_smt t)) hLenTermNN with
        ⟨T, htTy⟩
      constructor
      · change
          __smtx_typeof (__eo_to_smt (__str_value_len (__str_nary_intro t))) =
            __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        rw [hLen]
        change __smtx_typeof (SmtTerm.Numeral n) =
          __smtx_typeof (SmtTerm.str_len (__eo_to_smt t))
        have hNumTy : __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int := by
          rw [__smtx_typeof.eq_2]
        rw [hNumTy]
        rw [typeof_str_len_eq]
        simp [__smtx_typeof_seq_op_1_ret, htTy]
      · have hIntroNe : __str_nary_intro t ≠ Term.Stuck :=
          str_value_len_arg_ne_stuck_of_ne_stuck (__str_nary_intro t) hLenNe
        have hTComponents :
            type_inhabited T ∧ __smtx_type_wf T = true := by
          have hSeqWF :
              __smtx_type_wf (SmtType.Seq T) = true := by
            have hGood :=
              smt_term_result_seq_components_wf_of_non_none
                (__eo_to_smt t)
                (by
                  unfold term_has_non_none_type
                  rw [htTy]
                  exact seq_ne_none T)
            simpa [htTy, type_result_seq_components_wf] using hGood
          exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
        have hIntroNN :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
              SmtType.None :=
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 hIntroNe
        have hIntroTy :
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) =
              SmtType.Seq T :=
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            hIntroNN hIntroNe
        obtain ⟨sIntro, nIntro, hIntroEval, hIntroLen, hNIntro⟩ :=
          str_value_len_eval_seq_length M hM (__str_nary_intro t) T
            hIntroTy hLenNe
        have hLenIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt (__str_value_len (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t)))) := by
          rw [hIntroLen]
          have hNumEval :
              __smtx_model_eval M (__eo_to_smt (Term.Numeral nIntro)) =
                SmtValue.Numeral nIntro := by
            change __smtx_model_eval M (SmtTerm.Numeral nIntro) =
              SmtValue.Numeral nIntro
            rw [__smtx_model_eval.eq_2]
          rw [hNumEval]
          change RuleProofs.smt_value_rel
            (SmtValue.Numeral nIntro)
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
          rw [smtx_eval_str_len_term_eq, hIntroEval]
          rw [hNIntro]
          simp [__smtx_model_eval_str_len, native_seq_len,
            RuleProofs.smt_value_rel_refl]
        have hIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy hIntroNe
        have hLenCongRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_len)
                    (__str_nary_intro t))))
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t))) := by
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (SmtTerm.str_len (__eo_to_smt (__str_nary_intro t))))
            (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)))
          rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq]
          exact smt_value_rel_model_eval_str_len_of_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_intro t)))
            (__smtx_model_eval M (__eo_to_smt t)) hIntroRel
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M
            (__eo_to_smt (__str_value_len (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp.str_len) (__str_nary_intro t))))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) t)))
          hLenIntroRel hLenCongRel
  | case4 t ts ih =>
      have hConcatNN :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) ts)) ≠
            SmtType.None := hNN
      rcases str_concat_args_of_non_none t ts hConcatNN with
        ⟨T, htTy, htsTy⟩
      let a := __str_nary_intro t
      let z := __str_nary_intro (__seq_eval ts)
      let c := __eo_list_concat (Term.UOp UserOp.str_concat) a z
      have hCNe : c ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck c
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hLists :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true :=
        eo_list_concat_str_concat_lists_of_ne_stuck a z hCNe
      have hIntroTNe : a ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) a hLists.1
      have hIntroEvalTsNe : z ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat) z hLists.2
      have hSeqEvalTsNe : __seq_eval ts ≠ Term.Stuck := by
        exact str_nary_intro_arg_ne_stuck_of_ne_stuck (__seq_eval ts)
          (by simpa [z] using hIntroEvalTsNe)
      have htsNN : __smtx_typeof (__eo_to_smt ts) ≠ SmtType.None := by
        rw [htsTy]
        exact seq_ne_none T
      rcases ih hSeqEvalTsNe htsNN with
        ⟨hSeqEvalTsTySame, hSeqEvalTsRel⟩
      have hSeqEvalTsTy :
          __smtx_typeof (__eo_to_smt (__seq_eval ts)) = SmtType.Seq T := by
        rw [hSeqEvalTsTySame, htsTy]
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
          (by
            simpa [a] using
              str_nary_intro_has_smt_translation_of_seq_wf t T htTy
                hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe))
          (by simpa [a] using hIntroTNe)
      have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T :=
        smt_typeof_str_nary_intro_of_seq_ne_stuck (__seq_eval ts) T
          hSeqEvalTsTy
          (by
            simpa [z] using
              str_nary_intro_has_smt_translation_of_seq_wf (__seq_eval ts) T
                hSeqEvalTsTy hTComponents.1 hTComponents.2
                (by simpa [z] using hIntroEvalTsNe))
          (by simpa [z] using hIntroEvalTsNe)
      have hCEqRec :
          c = __eo_list_concat_rec a z :=
        eo_list_concat_str_concat_eq_rec_of_ne_stuck a z hCNe
      have hRecTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
            SmtType.Seq T :=
        smt_typeof_list_concat_rec_str_concat_of_seq a z T hLists.1 hATy hZTy
      have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.Seq T := by
        rw [hCEqRec]
        exact hRecTy
      have hElimRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
            (__smtx_model_eval M (__eo_to_smt c)) :=
        smt_value_rel_str_nary_elim M hM c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)
      have hListRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z))) := by
        rw [hCEqRec]
        exact strConcat_smt_value_rel_list_concat_rec_eval M hM a z T
          hLists.1 hATy hZTy
      have hIntroTRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt t)) :=
        smt_value_rel_str_nary_intro M hM t T htTy
          (by simpa [a] using hIntroTNe)
      have hIntroEvalTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt (__seq_eval ts))) :=
        smt_value_rel_str_nary_intro M hM (__seq_eval ts) T
          hSeqEvalTsTy (by simpa [z] using hIntroEvalTsNe)
      have hZTsRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt z))
            (__smtx_model_eval M (__eo_to_smt ts)) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt z))
          (__smtx_model_eval M (__eo_to_smt (__seq_eval ts)))
          (__smtx_model_eval M (__eo_to_smt ts))
          hIntroEvalTsRel hSeqEvalTsRel
      have hConcatLeftRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z))) :=
        strConcat_smt_value_rel_left_congr M hM a t z T
          hATy htTy hZTy hIntroTRel
      have hConcatRightRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        strConcat_smt_value_rel_right_congr M hM t z ts T
          htTy hZTy htsTy hZTsRel
      have hConcatRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt c))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts))) :=
        RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hListRel
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t z)))
            (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
            hConcatLeftRel hConcatRightRel)
      constructor
      · change __smtx_typeof (__eo_to_smt (__str_nary_elim c)) =
          __smtx_typeof (__eo_to_smt (mkConcat t ts))
        rw [smt_typeof_str_nary_elim_of_seq_ne_stuck c T hCTy
          (by simpa [__seq_eval, a, z, c] using hEvalNe)]
        exact (smt_typeof_str_concat_of_seq t ts T htTy htsTy).symm
      · change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim c)))
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval M (__eo_to_smt (mkConcat t ts)))
          hElimRel hConcatRel
    | case5 t n m =>
        let a := __str_nary_intro t
        let u := __eo_add n m
        let body :=
          __eo_ite (__eo_is_neg u)
            (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
            (__seq_subsequence_rec n u a)
        let out := __str_nary_elim body
        have hOutNe : out ≠ Term.Stuck := by
          simpa [__seq_eval, a, u, body, out] using hEvalNe
        have hBodyNe : body ≠ Term.Stuck :=
          str_nary_elim_arg_ne_stuck_of_ne_stuck body hOutNe
        have hSubstrNN :
            term_has_non_none_type
              (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
                (__eo_to_smt m)) := by
          unfold term_has_non_none_type
          have hsimpa := hNN
          try simp at hsimpa ⊢
          exact hsimpa
        rcases str_substr_args_of_non_none hSubstrNN with
          ⟨T, htTy, hnTy, hmTy⟩
        have hIntroNe : a ≠ Term.Stuck := by
          simpa [a] using str_nary_intro_ne_stuck_of_seq_type t T htTy
        have hTComponents :
            type_inhabited T ∧ __smtx_type_wf T = true := by
          have hSeqWF :
              __smtx_type_wf (SmtType.Seq T) = true := by
            have hGood :=
              smt_term_result_seq_components_wf_of_non_none
                (__eo_to_smt t)
                (by
                  unfold term_has_non_none_type
                  rw [htTy]
                  exact seq_ne_none T)
            simpa [htTy, type_result_seq_components_wf] using hGood
          exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
        have hIntroNN :
            __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
          simpa [a] using
            str_nary_intro_has_smt_translation_of_seq_wf t T htTy
              hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
        have hATy :
            __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
          simpa [a] using
            smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
              (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
        have hBodyTy :
            __smtx_typeof (__eo_to_smt body) = SmtType.Seq T := by
          simpa [body] using
            smt_typeof_seq_substr_body_of_seq a n u T hATy
              (by simpa [body] using hBodyNe)
        have hOutTy :
            __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
          simpa [out] using
            smt_typeof_str_nary_elim_of_seq_ne_stuck body T hBodyTy
              (by simpa [out] using hOutNe)
        constructor
        · change __smtx_typeof (__eo_to_smt out) =
            __smtx_typeof
              (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
                (__eo_to_smt m))
          rw [hOutTy, typeof_str_substr_eq, htTy, hnTy, hmTy]
          simp [__smtx_typeof_str_substr]
        · have hOutRelBody :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt out))
                (__smtx_model_eval M (__eo_to_smt body)) := by
            simpa [out] using
              smt_value_rel_str_nary_elim M hM body T hBodyTy
                (by simpa [out] using hOutNe)
          have hIntroRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt t)) :=
            smt_value_rel_str_nary_intro M hM t T htTy
              (by simpa [a] using hIntroNe)
          have hSubstrCong :
              RuleProofs.smt_value_rel
                (__smtx_model_eval_str_substr
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt n))
                  (__smtx_model_eval M (__eo_to_smt m)))
                (__smtx_model_eval_str_substr
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt n))
                  (__smtx_model_eval M (__eo_to_smt m))) :=
            smt_value_rel_model_eval_str_substr_of_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt n))
              (__smtx_model_eval M (__eo_to_smt m))
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval M (__eo_to_smt n))
              (__smtx_model_eval M (__eo_to_smt m))
              hIntroRel (RuleProofs.smt_value_rel_refl _)
              (RuleProofs.smt_value_rel_refl _)
          have hBodyRelSubstrA :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt body))
                (__smtx_model_eval_str_substr
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt n))
                  (__smtx_model_eval M (__eo_to_smt m))) := by
            rcases eo_ite_cases_of_ne_stuck (__eo_is_neg u)
                (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
                (__seq_subsequence_rec n u a)
                (by simpa [body] using hBodyNe) with hCond | hCond
            · have hAddNe : u ≠ Term.Stuck := by
                intro hu
                rw [hu] at hCond
                simp [__eo_is_neg] at hCond
              rcases eo_add_int_args_numerals_of_ne_stuck n m hnTy hmTy
                  (by simpa [u] using hAddNe) with
                ⟨i, j, rfl, rfl, hUEq⟩
              have hNegBool :
                  native_zlt (native_zplus i j) 0 = true := by
                simpa [u, hUEq, __eo_is_neg] using hCond
              have hEnd : i + j < 0 := by
                have hsimpa :=
                  hNegBool
                try simp [native_zlt, SmtEval.native_zlt, native_zplus] at hsimpa ⊢
                exact of_decide_eq_true hsimpa
              have hBodyEq :
                  body = Term.UOp1 UserOp1.seq_empty (__eo_typeof a) := by
                simp [body, u, hUEq, __eo_is_neg, hNegBool, eo_ite_true]
              rw [hBodyEq]
              change RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))))
                (__smtx_model_eval_str_substr
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (SmtTerm.Numeral i))
                  (__smtx_model_eval M (SmtTerm.Numeral j)))
              rw [__smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
              exact
                smt_value_rel_raw_empty_str_substr_of_end_neg
                  M hM a T i j hATy hEnd
            · have hAddNe : u ≠ Term.Stuck := by
                intro hu
                rw [hu] at hCond
                simp [__eo_is_neg] at hCond
              rcases eo_add_int_args_numerals_of_ne_stuck n m hnTy hmTy
                  (by simpa [u] using hAddNe) with
                ⟨i, j, rfl, rfl, hUEq⟩
              have hNegFalse :
                  native_zlt (native_zplus i j) 0 = false := by
                simpa [u, hUEq, __eo_is_neg] using hCond
              have hEndNonneg : 0 <= native_zplus i j := by
                have hNotLt : ¬ native_zplus i j < 0 := by
                  simpa [native_zlt, SmtEval.native_zlt] using hNegFalse
                exact Int.le_of_not_gt hNotLt
              have hBodyEq :
                  body =
                    __seq_subsequence_rec (Term.Numeral i)
                      (Term.Numeral (native_zplus i j)) a := by
                simp [body, u, hUEq, __eo_is_neg, hNegFalse, eo_ite_false]
              have hSubseqNe :
                  __seq_subsequence_rec (Term.Numeral i)
                      (Term.Numeral (native_zplus i j)) a ≠
                    Term.Stuck := by
                simpa [hBodyEq] using hBodyNe
              rw [hBodyEq]
              have hLenEq : native_zplus i j - i = j := by
                calc
                  native_zplus i j - i = (i + j) - i := by
                    simp [native_zplus, SmtEval.native_zplus]
                  _ = (j + i) - i := by rw [Int.add_comm i j]
                  _ = j := by simp
              change RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (__seq_subsequence_rec (Term.Numeral i)
                      (Term.Numeral (native_zplus i j)) a)))
                (__smtx_model_eval_str_substr
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (SmtTerm.Numeral i))
                  (__smtx_model_eval M (SmtTerm.Numeral j))
                )
              rw [__smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
              simpa [hLenEq] using
                smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
                  M hM (Term.Numeral i) (Term.Numeral (native_zplus i j))
                  a T i (native_zplus i j) rfl rfl hEndNonneg hATy
                  hSubseqNe
          rw [smtx_model_eval_str_substr_term_eq M t n m]
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt out))
            (__smtx_model_eval M (__eo_to_smt body))
            (__smtx_model_eval_str_substr
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval M (__eo_to_smt n))
              (__smtx_model_eval M (__eo_to_smt m)))
            hOutRelBody
            (RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt body))
              (__smtx_model_eval_str_substr
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt n))
                (__smtx_model_eval M (__eo_to_smt m)))
              (__smtx_model_eval_str_substr
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt n))
                (__smtx_model_eval M (__eo_to_smt m)))
              hBodyRelSubstrA hSubstrCong)
  | case6 t s =>
      let a := __str_nary_intro t
      let b := __str_nary_intro s
      let find := __seq_find a b (Term.Numeral 0)
      let out := __eo_not (__eo_is_neg find)
      let guardT := __is_seq_const t
      let guardS := __is_seq_const s
      have hReqNe :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true) out) ≠
            Term.Stuck := by
        simpa [__seq_eval, a, b, find, out, guardT, guardS] using hEvalNe
      have hInnerReqNe :
          __eo_requires guardS (Term.Boolean true) out ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) out) hReqNe
      have hOutNe : out ≠ Term.Stuck := by
        exact eo_requires_result_ne_stuck_of_ne_stuck guardS
          (Term.Boolean true) out hInnerReqNe
      have hGuardT : guardT = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) out) hReqNe
      have hGuardS : guardS = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardS (Term.Boolean true) out
          hInnerReqNe
      have hReqEq :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true) out) =
            out := by
        have hOuter :=
          eo_requires_eq_result_of_ne_stuck guardT (Term.Boolean true)
            (__eo_requires guardS (Term.Boolean true) out) hReqNe
        have hInner :=
          eo_requires_eq_result_of_ne_stuck guardS (Term.Boolean true) out
            hInnerReqNe
        rw [hOuter, hInner]
      have hFindNe : find ≠ Term.Stuck := by
        intro hStuck
        apply hOutNe
        simp [out, hStuck, __eo_is_neg, __eo_not]
      have hContainsNN :
          term_has_non_none_type
            (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
          (typeof_str_contains_eq (__eo_to_smt t) (__eo_to_smt s))
          hContainsNN with
        ⟨T, htTy, hsTy⟩
      have hIntroTNe : a ≠ Term.Stuck := by
        intro hStuck
        apply hFindNe
        simp [find, __seq_find, hStuck]
      have hIntroSNe : b ≠ Term.Stuck := by
        intro hStuck
        apply hFindNe
        cases a <;> simp [find, __seq_find, hStuck]
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq T := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      rcases seq_eval_of_seq_type M hM a T hATy with
        ⟨sa, hAEval⟩
      rcases seq_eval_of_seq_type M hM b T hBTy with
        ⟨sb, hBEval⟩
      rcases seq_eval_of_seq_type M hM t T htTy with
        ⟨st, hTEval⟩
      rcases seq_eval_of_seq_type M hM s T hsTy with
        ⟨ss, hSEval⟩
      have hIntroTRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt t)) :=
        smt_value_rel_str_nary_intro M hM t T htTy
          (by simpa [a] using hIntroTNe)
      have hIntroSRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt s)) :=
        smt_value_rel_str_nary_intro M hM s T hsTy
          (by simpa [b] using hIntroSNe)
      have hAUnpack :
          native_unpack_seq sa = native_unpack_seq st := by
        exact smt_value_rel_seq_unpack_eq
          (by simpa [hAEval, hTEval] using hIntroTRel)
      have hBUnpack :
          native_unpack_seq sb = native_unpack_seq ss := by
        exact smt_value_rel_seq_unpack_eq
          (by simpa [hBEval, hSEval] using hIntroSRel)
      have hOutBool : ∃ q, out = Term.Boolean q := by
        cases hFind : find with
        | Numeral n =>
            exact ⟨native_not (native_zlt n 0), by
              simp [out, hFind, __eo_is_neg, __eo_not]⟩
        | Rational r =>
            exact ⟨native_not (native_qlt r (native_mk_rational 0 1)), by
              simp [out, hFind, __eo_is_neg, __eo_not]⟩
        | _ =>
            exfalso
            apply hOutNe
            simp [out, hFind, __eo_is_neg, __eo_not]
      have hEvalEq :
          __seq_eval
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) t) s) =
            out := by
        simpa [__seq_eval, a, b, find, out, guardT, guardS] using hReqEq
      constructor
      · rcases hOutBool with ⟨q, hOutEq⟩
        rw [hEvalEq, hOutEq]
        change __smtx_typeof (SmtTerm.Boolean q) =
          __smtx_typeof
            (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s))
        rw [__smtx_typeof.eq_1, typeof_str_contains_eq]
        simp [__smtx_typeof_seq_op_2_ret, htTy, hsTy, native_Teq,
          native_ite]
      · have hContainsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) t) s)) =
              SmtValue.Boolean
                (native_seq_contains (native_unpack_seq st)
                  (native_unpack_seq ss)) :=
          RuleProofs.strContains_eval_eq M t s st ss hTEval hSEval
        rw [hEvalEq, hContainsEval]
        have hOutContains :
            __smtx_model_eval M (__eo_to_smt out) =
              SmtValue.Boolean
                (native_seq_contains (native_unpack_seq st)
                  (native_unpack_seq ss)) := by
          have hFindNative :
              find =
                Term.Numeral
                  (native_seq_indexof (native_unpack_seq st)
                    (native_unpack_seq ss) 0) := by
            have hFindNativeIntro :
                find =
                  Term.Numeral
                    (native_seq_indexof (native_unpack_seq sa)
                      (native_unpack_seq sb) 0) := by
              simpa [find, a, b] using
                seq_find_str_nary_intro_guarded_eq_native_indexof M hM t s T
                  sa sb htTy hsTy
                  (by simpa [guardT] using hGuardT)
                  (by simpa [guardS] using hGuardS)
                  (by simpa [a] using hATy)
                  (by simpa [b] using hBTy)
                  (by simpa [a] using hAEval)
                  (by simpa [b] using hBEval)
                  (by simpa [find, a, b] using hFindNe)
            simpa [hAUnpack, hBUnpack] using hFindNativeIntro
          simpa [out, hFindNative] using
            smtx_model_eval_not_is_neg_indexof_contains M
              (native_unpack_seq st) (native_unpack_seq ss)
        rw [hOutContains]
        exact RuleProofs.smt_value_rel_refl _
  | case7 t s r =>
      let a := __str_nary_intro t
      let len := __str_value_len t
      let b := __str_nary_intro s
      let find := __seq_find a b (Term.Numeral 0)
      let empty := Term.UOp1 UserOp1.seq_empty (__eo_typeof a)
      let isneg := __eo_is_neg find
      let left :=
        __eo_ite isneg empty
          (__seq_subsequence_rec (Term.Numeral 0) find a)
      let right :=
        __eo_ite (__eo_is_neg len) empty
          (__seq_subsequence_rec
            (__eo_add find (__str_value_len s)) len a)
      let repl := __str_nary_intro r
      let tail := __eo_list_concat (Term.UOp UserOp.str_concat) repl right
      let merged := __eo_list_concat (Term.UOp UserOp.str_concat) left tail
      let out := __eo_ite isneg t (__str_nary_elim merged)
      let guardT := __is_seq_const t
      let guardS := __is_seq_const s
      have hReqNe :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true) out) ≠
            Term.Stuck := by
        simpa [__seq_eval, a, len, b, find, empty, isneg, left, right,
          repl, tail, merged, out, guardT, guardS] using hEvalNe
      have hInnerReqNe :
          __eo_requires guardS (Term.Boolean true) out ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) out) hReqNe
      have hOutNe : out ≠ Term.Stuck := by
        exact eo_requires_result_ne_stuck_of_ne_stuck guardS
          (Term.Boolean true) out hInnerReqNe
      have hGuardT : guardT = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) out) hReqNe
      have hGuardS : guardS = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardS (Term.Boolean true) out
          hInnerReqNe
      have hReqEq :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true) out) =
            out := by
        have hOuter :=
          eo_requires_eq_result_of_ne_stuck guardT (Term.Boolean true)
            (__eo_requires guardS (Term.Boolean true) out) hReqNe
        have hInner :=
          eo_requires_eq_result_of_ne_stuck guardS (Term.Boolean true) out
            hInnerReqNe
        rw [hOuter, hInner]
      have hEvalEq :
          __seq_eval
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_replace) t) s) r) =
            out := by
        simpa [__seq_eval, a, len, b, find, empty, isneg, left, right,
          repl, tail, merged, out, guardT, guardS] using hReqEq
      have hReplaceNN :
          term_has_non_none_type
            (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
          (typeof_str_replace_eq (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt r))
          hReplaceNN with
        ⟨T, htTy, hsTy, hrTy⟩
      have hIntroTNe : a ≠ Term.Stuck := by
        simpa [a] using str_nary_intro_ne_stuck_of_seq_type t T htTy
      have hIntroSNe : b ≠ Term.Stuck := by
        simpa [b] using str_nary_intro_ne_stuck_of_seq_type s T hsTy
      have hIntroRNe : repl ≠ Term.Stuck := by
        simpa [repl] using str_nary_intro_ne_stuck_of_seq_type r T hrTy
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hIntroRNN :
          __smtx_typeof (__eo_to_smt repl) ≠ SmtType.None := by
        simpa [repl] using
          str_nary_intro_has_smt_translation_of_seq_wf r T hrTy
            hTComponents.1 hTComponents.2 (by simpa [repl] using hIntroRNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq T := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      have hReplTy :
          __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T := by
        simpa [repl] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck r T hrTy
            (by simpa [repl] using hIntroRNN)
            (by simpa [repl] using hIntroRNe)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
        rcases eo_ite_cases_of_ne_stuck isneg t (__str_nary_elim merged)
            hOutNe with hCond | hCond
        · simpa [out, hCond, eo_ite_true] using htTy
        · have hElimNe : __str_nary_elim merged ≠ Term.Stuck := by
            simpa [out, hCond, eo_ite_false] using hOutNe
          have hMergedNe : merged ≠ Term.Stuck :=
            str_nary_elim_arg_ne_stuck_of_ne_stuck merged hElimNe
          have hMergedLists :=
            eo_list_concat_str_concat_lists_of_ne_stuck left tail hMergedNe
          have hLeftNe : left ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              left hMergedLists.1
          have hTailNe : tail ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              tail hMergedLists.2
          have hTailLists :=
            eo_list_concat_str_concat_lists_of_ne_stuck repl right hTailNe
          have hRightNe : right ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              right hTailLists.2
          have hLeftTy :
              __smtx_typeof (__eo_to_smt left) = SmtType.Seq T := by
            simpa [left, empty] using
              smt_typeof_seq_substr_body_of_seq a (Term.Numeral 0) find T
                hATy (by simpa [left, empty] using hLeftNe)
          have hRightTy :
              __smtx_typeof (__eo_to_smt right) = SmtType.Seq T := by
            simpa [right, empty] using
              smt_typeof_seq_substr_body_of_seq a
                (__eo_add find (__str_value_len s)) len T hATy
                (by simpa [right, empty] using hRightNe)
          have hTailTy :
              __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
            simpa [tail] using
              smt_typeof_list_concat_str_concat_of_seq repl right T
                hReplTy hRightTy (by simpa [tail] using hTailNe)
          have hMergedTy :
              __smtx_typeof (__eo_to_smt merged) = SmtType.Seq T := by
            simpa [merged] using
              smt_typeof_list_concat_str_concat_of_seq left tail T
                hLeftTy hTailTy (by simpa [merged] using hMergedNe)
          simpa [out, hCond, eo_ite_false] using
            smt_typeof_str_nary_elim_of_seq_ne_stuck merged T hMergedTy
              hElimNe
      constructor
      · rw [hEvalEq]
        change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r))
        rw [hOutTy, typeof_str_replace_eq, htTy, hsTy, hrTy]
        simp [__smtx_typeof_seq_op_3, native_Teq, native_ite]
      · rw [hEvalEq]
        rcases seq_eval_of_seq_type M hM t T htTy with
          ⟨st, hTEval⟩
        rcases seq_eval_of_seq_type M hM s T hsTy with
          ⟨ss, hSEval⟩
        rcases seq_eval_of_seq_type M hM r T hrTy with
          ⟨sr, hREval⟩
        rcases seq_eval_of_seq_type M hM a T hATy with
          ⟨sa, hAEval⟩
        rcases seq_eval_of_seq_type M hM b T hBTy with
          ⟨sb, hBEval⟩
        rcases seq_eval_of_seq_type M hM repl T hReplTy with
          ⟨srepl, hReplEval⟩
        have hIntroTRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy
            (by simpa [a] using hIntroTNe)
        have hIntroSRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt s)) :=
          smt_value_rel_str_nary_intro M hM s T hsTy
            (by simpa [b] using hIntroSNe)
        have hIntroRRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt repl))
              (__smtx_model_eval M (__eo_to_smt r)) :=
          smt_value_rel_str_nary_intro M hM r T hrTy
            (by simpa [repl] using hIntroRNe)
        have hAUnpack :
            native_unpack_seq sa = native_unpack_seq st :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hAEval, hTEval] using hIntroTRel)
        have hBUnpack :
            native_unpack_seq sb = native_unpack_seq ss :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hBEval, hSEval] using hIntroSRel)
        have hReplUnpack :
            native_unpack_seq srepl = native_unpack_seq sr :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hReplEval, hREval] using hIntroRRel)
        have hOrigEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_replace) t) s) r)) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_replace (native_unpack_seq st)
                    (native_unpack_seq ss) (native_unpack_seq sr))) :=
          RuleProofs.strReplace_eval_eq M t s r st ss sr
            hTEval hSEval hREval
        have hStTyVal :
            __smtx_typeof_seq_value st = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM t T st htTy hTEval
        have hSaTyVal :
            __smtx_typeof_seq_value sa = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM a T sa hATy hAEval
        have hSaElem : __smtx_elem_typeof_seq_value sa = T :=
          elem_typeof_seq_value_of_typeof_seq_value hSaTyVal
        rcases eo_ite_cases_of_ne_stuck isneg t (__str_nary_elim merged)
            hOutNe with hCond | hCond
        · have hFindNe : find ≠ Term.Stuck := by
            intro hStuck
            have hBad : isneg = Term.Stuck := by
              simp [isneg, hStuck, __eo_is_neg]
            rw [hBad] at hCond
            cases hCond
          let idx :=
            native_seq_indexof (native_unpack_seq sa)
              (native_unpack_seq sb) 0
          have hFindNative : find = Term.Numeral idx := by
            simpa [idx, find, a, b] using
              seq_find_str_nary_intro_guarded_eq_native_indexof M hM t s T
                sa sb htTy hsTy
                (by simpa [guardT] using hGuardT)
                (by simpa [guardS] using hGuardS)
                (by simpa [a] using hATy)
                (by simpa [b] using hBTy)
                (by simpa [a] using hAEval)
                (by simpa [b] using hBEval)
                (by simpa [find, a, b] using hFindNe)
          have hIdxNeg : idx < 0 := by
            have hNegBool : native_zlt idx 0 = true := by
              simpa [isneg, hFindNative, __eo_is_neg] using hCond
            exact of_decide_eq_true
              (by simpa [native_zlt] using hNegBool)
          have hReplaceSelf :
              native_seq_replace (native_unpack_seq st)
                  (native_unpack_seq ss) (native_unpack_seq sr) =
                native_unpack_seq st := by
            rw [← hAUnpack, ← hBUnpack, ← hReplUnpack]
            exact native_seq_replace_eq_self_of_indexof_neg
              (native_unpack_seq sa) (native_unpack_seq sb)
              (native_unpack_seq srepl) hIdxNeg
          have hOutEqT : out = t := by
            simp [out, hCond, eo_ite_true]
          rw [hOutEqT, hTEval, hOrigEval, hReplaceSelf]
          exact smt_value_rel_seq_pack_of_unpack_eq st st
            (native_unpack_seq st) T hStTyVal hStTyVal rfl
        · have hElimNe : __str_nary_elim merged ≠ Term.Stuck := by
            simpa [out, hCond, eo_ite_false] using hOutNe
          have hMergedNe : merged ≠ Term.Stuck :=
            str_nary_elim_arg_ne_stuck_of_ne_stuck merged hElimNe
          have hMergedLists :=
            eo_list_concat_str_concat_lists_of_ne_stuck left tail hMergedNe
          have hLeftNe : left ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              left hMergedLists.1
          have hTailNe : tail ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              tail hMergedLists.2
          have hTailLists :=
            eo_list_concat_str_concat_lists_of_ne_stuck repl right hTailNe
          have hRightNe : right ≠ Term.Stuck :=
            term_ne_stuck_of_eo_is_list_true (Term.UOp UserOp.str_concat)
              right hTailLists.2
          have hFindNe : find ≠ Term.Stuck := by
            intro hStuck
            have hBad : isneg = Term.Stuck := by
              simp [isneg, hStuck, __eo_is_neg]
            rw [hBad] at hCond
            cases hCond
          let idx :=
            native_seq_indexof (native_unpack_seq sa)
              (native_unpack_seq sb) 0
          have hFindNative : find = Term.Numeral idx := by
            simpa [idx, find, a, b] using
              seq_find_str_nary_intro_guarded_eq_native_indexof M hM t s T
                sa sb htTy hsTy
                (by simpa [guardT] using hGuardT)
                (by simpa [guardS] using hGuardS)
                (by simpa [a] using hATy)
                (by simpa [b] using hBTy)
                (by simpa [a] using hAEval)
                (by simpa [b] using hBEval)
                (by simpa [find, a, b] using hFindNe)
          have hIdxNonneg : 0 ≤ idx := by
            have hNegFalse : native_zlt idx 0 = false := by
              simpa [isneg, hFindNative, __eo_is_neg] using hCond
            have hNotLt : ¬ idx < 0 := by
              intro hLt
              have hTrue : native_zlt idx 0 = true := by
                unfold native_zlt
                exact decide_eq_true hLt
              rw [hTrue] at hNegFalse
              cases hNegFalse
            exact Int.not_lt.mp hNotLt
          have hLeftEq :
              left = __seq_subsequence_rec (Term.Numeral 0) find a := by
            simp [left, hCond, eo_ite_false]
          have hLeftSubNe :
              __seq_subsequence_rec (Term.Numeral 0) find a ≠
                Term.Stuck := by
            simpa [hLeftEq] using hLeftNe
          have hLeftTy :
              __smtx_typeof (__eo_to_smt left) = SmtType.Seq T := by
            simpa [left, empty] using
              smt_typeof_seq_substr_body_of_seq a (Term.Numeral 0) find T
                hATy (by simpa [left, empty] using hLeftNe)
          rcases seq_eval_of_seq_type M hM left T hLeftTy with
            ⟨sLeft, hLeftEval⟩
          have hLeftSubEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__seq_subsequence_rec (Term.Numeral 0) find a)) =
                SmtValue.Seq sLeft := by
            rw [← hLeftEq]
            exact hLeftEval
          have hLeftRel :=
            smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
              M hM (Term.Numeral 0) find a T 0 idx rfl hFindNative
              hIdxNonneg hATy hLeftSubNe
          have hLeftPackRel :
              RuleProofs.smt_value_rel (SmtValue.Seq sLeft)
                (SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value sa)
                    (native_seq_extract (native_unpack_seq sa) 0 idx))) := by
            simpa [hLeftSubEval, hAEval, __smtx_model_eval_str_substr,
              hSaElem] using hLeftRel
          have hLeftUnpack :
              native_unpack_seq sLeft =
                native_seq_extract (native_unpack_seq sa) 0 idx :=
            by
              have hUnpack := smt_value_rel_seq_unpack_eq hLeftPackRel
              simpa [Smtm.native_unpack_pack_seq] using hUnpack
          have hLenNe : len ≠ Term.Stuck := by
            intro hStuck
            have hRightIteNe :
                __eo_ite (__eo_is_neg len) empty
                    (__seq_subsequence_rec
                      (__eo_add find (__str_value_len s)) len a) ≠
                  Term.Stuck := by
              simpa [right] using hRightNe
            rcases eo_ite_cases_of_ne_stuck (__eo_is_neg len) empty
                (__seq_subsequence_rec
                  (__eo_add find (__str_value_len s)) len a)
                hRightIteNe with hGuard | hGuard
            · rw [hStuck] at hGuard
              simp [__eo_is_neg] at hGuard
            · rw [hStuck] at hGuard
              simp [__eo_is_neg] at hGuard
          rcases str_value_len_eval_seq_length M hM t T htTy
              (by simpa [len] using hLenNe) with
            ⟨stLen, nLen, hTEvalLen, hLenEq, hNLenEq⟩
          have hStLen : stLen = st := by
            rw [hTEval] at hTEvalLen
            injection hTEvalLen with hSeq
            exact hSeq.symm
          have hNLenEqSt :
              nLen = Int.ofNat (native_unpack_seq st).length := by
            simpa [hStLen] using hNLenEq
          have hLenTermSt :
              len =
                Term.Numeral
                  (Int.ofNat (native_unpack_seq st).length) := by
            have hLenTerm : len = Term.Numeral nLen := by
              simpa [len] using hLenEq
            rw [hLenTerm, hNLenEqSt]
          have hLenTermA :
              len =
                Term.Numeral
                  (Int.ofNat (native_unpack_seq sa).length) := by
            rw [hLenTermSt, hAUnpack]
          have hLenNegFalse :
              __eo_is_neg len = Term.Boolean false := by
            rw [hLenTermSt]
            simp [__eo_is_neg, native_zlt]
          have hRightEq :
              right =
                __seq_subsequence_rec
                  (__eo_add find (__str_value_len s)) len a := by
            simp [right, hLenNegFalse, eo_ite_false]
          have hRightSubNe :
              __seq_subsequence_rec
                  (__eo_add find (__str_value_len s)) len a ≠
                Term.Stuck := by
            simpa [hRightEq] using hRightNe
          rcases str_value_len_eval_seq_length M hM s T hsTy
              (by
                rcases str_value_len_numeral_of_is_seq_const_true s
                    (by simpa [guardS] using hGuardS) with ⟨nS, hLenS⟩
                rw [hLenS]
                simp) with
            ⟨ssLen, nSLen, hSEvalLen, hLenSEq, hNSLenEq⟩
          have hSsLen : ssLen = ss := by
            rw [hSEval] at hSEvalLen
            injection hSEvalLen with hSeq
            exact hSeq.symm
          have hNSLenEqSs :
              nSLen = Int.ofNat (native_unpack_seq ss).length := by
            simpa [hSsLen] using hNSLenEq
          have hLenSTermSb :
              __str_value_len s =
                Term.Numeral
                  (Int.ofNat (native_unpack_seq sb).length) := by
            have hLenSTerm :
                __str_value_len s =
                  Term.Numeral
                    (Int.ofNat (native_unpack_seq ss).length) := by
              rw [hLenSEq, hNSLenEqSs]
            rw [hLenSTerm, hBUnpack]
          have hAddEq :
              __eo_add find (__str_value_len s) =
                Term.Numeral
                  (idx + Int.ofNat (native_unpack_seq sb).length) := by
            simp [hFindNative, hLenSTermSb, __eo_add, native_zplus]
          have hRightTy :
              __smtx_typeof (__eo_to_smt right) = SmtType.Seq T := by
            simpa [right, empty] using
              smt_typeof_seq_substr_body_of_seq a
                (__eo_add find (__str_value_len s)) len T hATy
                (by simpa [right, empty] using hRightNe)
          rcases seq_eval_of_seq_type M hM right T hRightTy with
            ⟨sRight, hRightEval⟩
          have hRightSubEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__seq_subsequence_rec
                      (__eo_add find (__str_value_len s)) len a)) =
                SmtValue.Seq sRight := by
            rw [← hRightEq]
            exact hRightEval
          have hEndNonneg :
              0 ≤ (Int.ofNat (native_unpack_seq sa).length : Int) :=
            Int.natCast_nonneg (native_unpack_seq sa).length
          have hRightRel :=
            smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
              M hM (__eo_add find (__str_value_len s)) len a T
              (idx + Int.ofNat (native_unpack_seq sb).length)
              (Int.ofNat (native_unpack_seq sa).length) hAddEq
              hLenTermA hEndNonneg hATy hRightSubNe
          have hRightPackRel :
              RuleProofs.smt_value_rel (SmtValue.Seq sRight)
                (SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value sa)
                    (native_seq_extract (native_unpack_seq sa)
                      (idx + Int.ofNat (native_unpack_seq sb).length)
                      (Int.ofNat (native_unpack_seq sa).length -
                        (idx + Int.ofNat (native_unpack_seq sb).length))))) := by
            simpa [hRightSubEval, hAEval, __smtx_model_eval_str_substr,
              hSaElem] using hRightRel
          have hRightUnpack :
              native_unpack_seq sRight =
                native_seq_extract (native_unpack_seq sa)
                  (idx + Int.ofNat (native_unpack_seq sb).length)
                  (Int.ofNat (native_unpack_seq sa).length -
                    (idx + Int.ofNat (native_unpack_seq sb).length)) := by
            have hUnpack := smt_value_rel_seq_unpack_eq hRightPackRel
            simpa [Smtm.native_unpack_pack_seq] using hUnpack
          have hTailTy :
              __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
            simpa [tail] using
              smt_typeof_list_concat_str_concat_of_seq repl right T
                hReplTy hRightTy (by simpa [tail] using hTailNe)
          rcases seq_eval_of_seq_type M hM tail T hTailTy with
            ⟨sTail, hTailEval⟩
          have hTailUnpack :
              native_unpack_seq sTail =
                native_unpack_seq srepl ++ native_unpack_seq sRight :=
            by
              simpa [tail] using
                eo_list_concat_str_concat_unpack_of_seq_evals M hM
                  repl right T srepl sRight sTail hReplTy hRightTy
                  hReplEval hRightEval (by simpa [tail] using hTailNe)
                  (by simpa [tail] using hTailEval)
          have hMergedTy :
              __smtx_typeof (__eo_to_smt merged) = SmtType.Seq T := by
            simpa [merged] using
              smt_typeof_list_concat_str_concat_of_seq left tail T
                hLeftTy hTailTy (by simpa [merged] using hMergedNe)
          rcases seq_eval_of_seq_type M hM merged T hMergedTy with
            ⟨sMerged, hMergedEval⟩
          have hMergedUnpack :
              native_unpack_seq sMerged =
                native_unpack_seq sLeft ++ native_unpack_seq sTail :=
            by
              simpa [merged] using
                eo_list_concat_str_concat_unpack_of_seq_evals M hM
                  left tail T sLeft sTail sMerged hLeftTy hTailTy
                  hLeftEval hTailEval (by simpa [merged] using hMergedNe)
                  (by simpa [merged] using hMergedEval)
          have hOutBranch : out = __str_nary_elim merged := by
            simp [out, hCond, eo_ite_false]
          rcases seq_eval_of_seq_type M hM out T hOutTy with
            ⟨sOut, hOutEval⟩
          have hElimEval :
              __smtx_model_eval M
                  (__eo_to_smt (__str_nary_elim merged)) =
                SmtValue.Seq sOut := by
            rw [← hOutBranch]
            exact hOutEval
          have hElimRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (__str_nary_elim merged)))
                (__smtx_model_eval M (__eo_to_smt merged)) :=
            smt_value_rel_str_nary_elim M hM merged T hMergedTy hElimNe
          have hOutMergedUnpack :
              native_unpack_seq sOut = native_unpack_seq sMerged := by
            exact smt_value_rel_seq_unpack_eq
              (by simpa [hElimEval, hMergedEval] using hElimRel)
          have hSOutUnpack :
              native_unpack_seq sOut =
                native_seq_replace (native_unpack_seq sa)
                  (native_unpack_seq sb) (native_unpack_seq srepl) := by
            calc
              native_unpack_seq sOut = native_unpack_seq sMerged :=
                hOutMergedUnpack
              _ = native_unpack_seq sLeft ++ native_unpack_seq sTail :=
                hMergedUnpack
              _ =
                  native_seq_extract (native_unpack_seq sa) 0 idx ++
                    (native_unpack_seq srepl ++
                      native_seq_extract (native_unpack_seq sa)
                        (idx + Int.ofNat (native_unpack_seq sb).length)
                        (Int.ofNat (native_unpack_seq sa).length -
                          (idx + Int.ofNat (native_unpack_seq sb).length))) := by
                rw [hLeftUnpack, hTailUnpack, hRightUnpack]
              _ =
                  native_seq_extract (native_unpack_seq sa) 0 idx ++
                    native_unpack_seq srepl ++
                      native_seq_extract (native_unpack_seq sa)
                        (idx + Int.ofNat (native_unpack_seq sb).length)
                        (Int.ofNat (native_unpack_seq sa).length -
                          (idx + Int.ofNat (native_unpack_seq sb).length)) := by
                simp [List.append_assoc]
              _ =
                  native_seq_replace (native_unpack_seq sa)
                    (native_unpack_seq sb) (native_unpack_seq srepl) := by
                exact (native_seq_replace_eq_extracts_of_indexof_nonneg
                  (native_unpack_seq sa) (native_unpack_seq sb)
                  (native_unpack_seq srepl) hIdxNonneg).symm
          have hSOutUnpackOrig :
              native_unpack_seq sOut =
                native_seq_replace (native_unpack_seq st)
                  (native_unpack_seq ss) (native_unpack_seq sr) := by
            rw [← hAUnpack, ← hBUnpack, ← hReplUnpack]
            exact hSOutUnpack
          have hSOutTy :
              __smtx_typeof_seq_value sOut = SmtType.Seq T :=
            smt_typeof_seq_value_of_eval_seq M hM out T sOut hOutTy
              hOutEval
          rw [hOutEval, hOrigEval]
          exact smt_value_rel_seq_pack_of_unpack_eq sOut st
            (native_seq_replace (native_unpack_seq st)
              (native_unpack_seq ss) (native_unpack_seq sr)) T
            hSOutTy hStTyVal hSOutUnpackOrig
  | case8 t s r =>
      let b := __str_nary_intro s
      let a := __str_nary_intro t
      let repl := __str_nary_intro r
      let lent := __str_value_len s
      let replaced :=
        __seq_eval_replace_all_rec a b repl (Term.Numeral 0) lent
      let emptyPat := __eo_eq lent (Term.Numeral 0)
      let body := __eo_ite emptyPat t (__str_nary_elim replaced)
      let guard := __is_seq_const t
      let out := __eo_requires guard (Term.Boolean true) body
      have hOutNe : out ≠ Term.Stuck := by
        have hsimpa := hEvalNe
        try simp [__seq_eval, b, a, repl, lent, replaced, emptyPat, body, guard, out] at hsimpa ⊢
        exact hsimpa
      have hBodyNe : body ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          body (by simpa [out] using hOutNe)
      have hOutEq : out = body := by
        simpa [out] using
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) body
            (by simpa [out] using hOutNe)
      have hReplaceAllNN :
          term_has_non_none_type
            (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
          (typeof_str_replace_all_eq (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt r))
          hReplaceAllNN with
        ⟨T, htTy, hsTy, hrTy⟩
      have hIntroTNe : a ≠ Term.Stuck := by
        simpa [a] using str_nary_intro_ne_stuck_of_seq_type t T htTy
      have hIntroSNe : b ≠ Term.Stuck := by
        simpa [b] using str_nary_intro_ne_stuck_of_seq_type s T hsTy
      have hIntroRNe : repl ≠ Term.Stuck := by
        simpa [repl] using str_nary_intro_ne_stuck_of_seq_type r T hrTy
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hIntroRNN :
          __smtx_typeof (__eo_to_smt repl) ≠ SmtType.None := by
        simpa [repl] using
          str_nary_intro_has_smt_translation_of_seq_wf r T hrTy
            hTComponents.1 hTComponents.2 (by simpa [repl] using hIntroRNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq T := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      have hReplTy :
          __smtx_typeof (__eo_to_smt repl) = SmtType.Seq T := by
        simpa [repl] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck r T hrTy
            (by simpa [repl] using hIntroRNN)
            (by simpa [repl] using hIntroRNe)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
        rw [hOutEq]
        rcases eo_ite_cases_of_ne_stuck emptyPat t (__str_nary_elim replaced)
            hBodyNe with hCond | hCond
        · simpa [body, hCond, eo_ite_true] using htTy
        · have hElimNe : __str_nary_elim replaced ≠ Term.Stuck := by
            simpa [body, hCond, eo_ite_false] using hBodyNe
          have hRecNe : replaced ≠ Term.Stuck :=
            str_nary_elim_arg_ne_stuck_of_ne_stuck replaced hElimNe
          have hZeroTy :
              __smtx_typeof (__eo_to_smt (Term.Numeral 0)) =
                SmtType.Int := by
            change __smtx_typeof (SmtTerm.Numeral (0 : native_Int)) =
              SmtType.Int
            rw [__smtx_typeof.eq_2]
          have hLentNe : lent ≠ Term.Stuck :=
            seq_eval_replace_all_rec_lent_ne_stuck_of_ne_stuck a b repl
              (Term.Numeral 0) lent (by simpa [replaced] using hRecNe)
          have hLentTy :
              __smtx_typeof (__eo_to_smt lent) = SmtType.Int := by
            simpa [lent] using
              smt_typeof_str_value_len_of_ne_stuck s
                (by simpa [lent] using hLentNe)
          have hRecTy :
              __smtx_typeof (__eo_to_smt replaced) = SmtType.Seq T := by
            simpa [replaced] using
              smt_typeof_seq_eval_replace_all_rec_of_seq a b repl
                (Term.Numeral 0) lent T hATy hBTy hReplTy hZeroTy
                hLentTy (by simpa [replaced] using hRecNe)
          simpa [body, hCond, eo_ite_false] using
            smt_typeof_str_nary_elim_of_seq_ne_stuck replaced T hRecTy
              hElimNe
      constructor
      · change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r))
        rw [hOutTy, typeof_str_replace_all_eq, htTy, hsTy, hrTy]
        simp [__smtx_typeof_seq_op_3, native_Teq, native_ite]
      · change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt out))
          (__smtx_model_eval M
            (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt r)))
        rcases seq_eval_of_seq_type M hM t T htTy with ⟨st, hTEval⟩
        rcases seq_eval_of_seq_type M hM s T hsTy with ⟨ss, hSEval⟩
        rcases seq_eval_of_seq_type M hM r T hrTy with ⟨sr, hREval⟩
        rcases seq_eval_of_seq_type M hM a T hATy with ⟨sa, hAEval⟩
        rcases seq_eval_of_seq_type M hM b T hBTy with ⟨sb, hBEval⟩
        rcases seq_eval_of_seq_type M hM repl T hReplTy with
          ⟨srepl, hReplEval⟩
        have hIntroTRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy
            (by simpa [a] using hIntroTNe)
        have hIntroSRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt s)) :=
          smt_value_rel_str_nary_intro M hM s T hsTy
            (by simpa [b] using hIntroSNe)
        have hIntroRRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt repl))
              (__smtx_model_eval M (__eo_to_smt r)) :=
          smt_value_rel_str_nary_intro M hM r T hrTy
            (by simpa [repl] using hIntroRNe)
        have hAUnpack :
            native_unpack_seq sa = native_unpack_seq st :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hAEval, hTEval] using hIntroTRel)
        have hBUnpack :
            native_unpack_seq sb = native_unpack_seq ss :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hBEval, hSEval] using hIntroSRel)
        have hReplUnpack :
            native_unpack_seq srepl = native_unpack_seq sr :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hReplEval, hREval] using hIntroRRel)
        have hOrigEval :
            __smtx_model_eval M
                (SmtTerm.str_replace_all (__eo_to_smt t) (__eo_to_smt s)
                  (__eo_to_smt r)) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_replace_all (native_unpack_seq st)
                    (native_unpack_seq ss) (native_unpack_seq sr))) := by
          rw [smtx_eval_str_replace_all_term_eq, hTEval, hSEval, hREval]
          rfl
        have hStTyVal :
            __smtx_typeof_seq_value st = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM t T st htTy hTEval
        have hTNN : T ≠ SmtType.None :=
          smt_seq_component_ne_none_of_typeof_seq t T htTy
        have hGuardTrue : guard = Term.Boolean true :=
          eo_requires_eq_of_ne_stuck guard (Term.Boolean true) body
            (by simpa [out] using hOutNe)
        rcases eo_ite_cases_of_ne_stuck emptyPat t
            (__str_nary_elim replaced) hBodyNe with hCond | hCond
        · have hLentEq0 :
              lent = Term.Numeral (0 : native_Int) :=
            (eq_of_eo_eq_true_local lent (Term.Numeral 0) hCond).symm
          have hLenNe : __str_value_len s ≠ Term.Stuck := by
            simp [lent, hLentEq0]
          rcases str_value_len_eval_seq_length M hM s T hsTy hLenNe with
            ⟨ssLen, nSLen, hSEvalLen, hLenSEq, hNSLenEq⟩
          have hSsLen : ssLen = ss := by
            rw [hSEval] at hSEvalLen
            injection hSEvalLen with hSeq
            exact hSeq.symm
          have hNZero : nSLen = 0 := by
            have hTerm :
                Term.Numeral nSLen =
                  Term.Numeral (0 : native_Int) := by
              rw [← hLenSEq]
              simpa [lent] using hLentEq0
            injection hTerm
          have hPatNil : native_unpack_seq ss = [] := by
            have hLenZero :
                Int.ofNat (native_unpack_seq ss).length = 0 := by
              simpa [hSsLen, hNZero] using hNSLenEq.symm
            have hNatZero : (native_unpack_seq ss).length = 0 := by
              exact Int.ofNat.inj (by simpa using hLenZero)
            exact List.eq_nil_of_length_eq_zero hNatZero
          have hReplaceSelf :
              native_seq_replace_all (native_unpack_seq st)
                  (native_unpack_seq ss) (native_unpack_seq sr) =
                native_unpack_seq st := by
            rw [hPatNil, native_seq_replace_all_nil]
          have hOutEqT : out = t := by
            rw [hOutEq]
            simp [body, hCond, eo_ite_true]
          rw [hOutEqT, hTEval, hOrigEval, hReplaceSelf]
          exact smt_value_rel_seq_pack_of_unpack_eq st st
            (native_unpack_seq st) T hStTyVal hStTyVal rfl
        · have hElimNe : __str_nary_elim replaced ≠ Term.Stuck := by
            simpa [body, hCond, eo_ite_false] using hBodyNe
          have hRecNe : replaced ≠ Term.Stuck :=
            str_nary_elim_arg_ne_stuck_of_ne_stuck replaced hElimNe
          have hZeroTy :
              __smtx_typeof (__eo_to_smt (Term.Numeral 0)) =
                SmtType.Int := by
            change __smtx_typeof (SmtTerm.Numeral (0 : native_Int)) =
              SmtType.Int
            rw [__smtx_typeof.eq_2]
          have hLentNe : lent ≠ Term.Stuck :=
            seq_eval_replace_all_rec_lent_ne_stuck_of_ne_stuck a b repl
              (Term.Numeral 0) lent (by simpa [replaced] using hRecNe)
          have hLentTy :
              __smtx_typeof (__eo_to_smt lent) = SmtType.Int := by
            simpa [lent] using
              smt_typeof_str_value_len_of_ne_stuck s
                (by simpa [lent] using hLentNe)
          have hRecTy :
              __smtx_typeof (__eo_to_smt replaced) = SmtType.Seq T := by
            simpa [replaced] using
              smt_typeof_seq_eval_replace_all_rec_of_seq a b repl
                (Term.Numeral 0) lent T hATy hBTy hReplTy hZeroTy
                hLentTy (by simpa [replaced] using hRecNe)
          rcases seq_eval_of_seq_type M hM replaced T hRecTy with
            ⟨sReplaced, hReplacedEval⟩
          rcases str_value_len_eval_seq_length M hM s T hsTy
              (by simpa [lent] using hLentNe) with
            ⟨ssLen, nSLen, hSEvalLen, hLenSEq, hNSLenEq⟩
          have hSsLen : ssLen = ss := by
            rw [hSEval] at hSEvalLen
            injection hSEvalLen with hSeq
            exact hSeq.symm
          have hNSLenEqSs :
              nSLen = Int.ofNat (native_unpack_seq ss).length := by
            simpa [hSsLen] using hNSLenEq
          have hLenSTermSb :
              lent =
                Term.Numeral
                  (Int.ofNat (native_unpack_seq sb).length) := by
            have hLenSTerm :
                __str_value_len s =
                  Term.Numeral
                    (Int.ofNat (native_unpack_seq ss).length) := by
              rw [hLenSEq, hNSLenEqSs]
            simpa [lent, hBUnpack] using hLenSTerm
          have hPatNe : native_unpack_seq sb ≠ [] := by
            intro hNil
            have hLentZero : lent = Term.Numeral (0 : native_Int) := by
              rw [hLenSTermSb, hNil]
              rfl
            have hEmptyTrue : emptyPat = Term.Boolean true := by
              simp [emptyPat, hLentZero, __eo_eq, native_teq,
                SmtEval.native_ite, SmtEval.native_not]
            rw [hEmptyTrue] at hCond
            cases hCond
          have hAConst :
              __is_seq_const_rec a = Term.Boolean true := by
            simpa [a, replaced] using
              str_nary_intro_const_rec_true_of_guard_replace_all_ne
                t b repl lent T hTNN htTy
                (by simpa [guard] using hGuardTrue)
                (by simpa [a, replaced] using hRecNe)
          have hRecUnpack :
              native_unpack_seq sReplaced =
                native_seq_replace_all_chain (native_unpack_seq sb)
                  (native_unpack_seq srepl) 0 (native_unpack_seq sa) :=
            seq_eval_replace_all_rec_unpack_eq_chain M hM a b repl
              (Term.Numeral 0) lent T sa sb srepl sReplaced 0 hTNN
              hAConst hATy hBTy hReplTy hAEval hBEval hReplEval rfl
              hLenSTermSb hPatNe (by simpa [replaced] using hRecNe)
              (by simpa [replaced] using hReplacedEval)
          have hReplaceAllChain :
              native_seq_replace_all (native_unpack_seq sa)
                  (native_unpack_seq sb) (native_unpack_seq srepl) =
                native_seq_replace_all_chain (native_unpack_seq sb)
                  (native_unpack_seq srepl) 0 (native_unpack_seq sa) := by
            cases hPat : native_unpack_seq sb with
            | nil =>
                exact False.elim (hPatNe hPat)
            | cons p ps =>
                simpa [hPat] using
                  native_seq_replace_all_eq_chain_cons
                    (native_unpack_seq sa) (native_unpack_seq srepl) p ps
          have hOutBranch : out = __str_nary_elim replaced := by
            rw [hOutEq]
            simp [body, hCond, eo_ite_false]
          rcases seq_eval_of_seq_type M hM out T hOutTy with
            ⟨sOut, hOutEval⟩
          have hElimEval :
              __smtx_model_eval M
                  (__eo_to_smt (__str_nary_elim replaced)) =
                SmtValue.Seq sOut := by
            rw [← hOutBranch]
            exact hOutEval
          have hElimRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (__str_nary_elim replaced)))
                (__smtx_model_eval M (__eo_to_smt replaced)) :=
            smt_value_rel_str_nary_elim M hM replaced T hRecTy hElimNe
          have hOutReplacedUnpack :
              native_unpack_seq sOut = native_unpack_seq sReplaced :=
            smt_value_rel_seq_unpack_eq
              (by simpa [hElimEval, hReplacedEval] using hElimRel)
          have hSOutUnpack :
              native_unpack_seq sOut =
                native_seq_replace_all (native_unpack_seq st)
                  (native_unpack_seq ss) (native_unpack_seq sr) := by
            calc
              native_unpack_seq sOut = native_unpack_seq sReplaced :=
                hOutReplacedUnpack
              _ = native_seq_replace_all_chain (native_unpack_seq sb)
                    (native_unpack_seq srepl) 0 (native_unpack_seq sa) :=
                hRecUnpack
              _ = native_seq_replace_all (native_unpack_seq sa)
                    (native_unpack_seq sb) (native_unpack_seq srepl) := by
                rw [← hReplaceAllChain]
              _ = native_seq_replace_all (native_unpack_seq st)
                    (native_unpack_seq ss) (native_unpack_seq sr) := by
                rw [hAUnpack, hBUnpack, hReplUnpack]
          have hSOutTy :
              __smtx_typeof_seq_value sOut = SmtType.Seq T :=
            smt_typeof_seq_value_of_eval_seq M hM out T sOut hOutTy
              hOutEval
          rw [hOutEval, hOrigEval]
          exact smt_value_rel_seq_pack_of_unpack_eq sOut st
            (native_seq_replace_all (native_unpack_seq st)
              (native_unpack_seq ss) (native_unpack_seq sr)) T
            hSOutTy hStTyVal hSOutUnpack
  | case9 t s n =>
      let a := __str_nary_intro t
      let len := __str_value_len t
      let substr :=
        __eo_ite (__eo_is_neg len)
          (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
          (__seq_subsequence_rec n len a)
      let b := __str_nary_intro s
      let find := __seq_find substr b n
      let inRange := __eo_ite (__eo_gt n len) (Term.Numeral (-1 : native_Int))
        find
      let body := __eo_ite (__eo_is_neg n) (Term.Numeral (-1 : native_Int))
        inRange
      let guard := __is_seq_const s
      let out := __eo_requires guard (Term.Boolean true) body
      have hOutNe : out ≠ Term.Stuck := by
        simpa [__seq_eval, a, len, substr, b, find, inRange, body, guard,
          out] using hEvalNe
      have hBodyNe : body ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          body (by simpa [out] using hOutNe)
      have hOutEq : out = body := by
        have hsimpa :=
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) body
            (by simpa [out] using hOutNe)
        try simp [out] at hsimpa ⊢
        exact hsimpa
      have hEvalEq :
          __seq_eval
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_indexof) t) s) n) =
            out := by
        simp [__seq_eval, a, len, substr, b, find, inRange, body, guard,
          out, hOutEq]
      have hIndexNN :
          term_has_non_none_type
            (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt n)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases str_indexof_args_of_non_none hIndexNN with
        ⟨T, htTy, hsTy, hnTy⟩
      have hIntroTNe : a ≠ Term.Stuck := by
        simpa [a] using str_nary_intro_ne_stuck_of_seq_type t T htTy
      have hIntroSNe : b ≠ Term.Stuck := by
        simpa [b] using str_nary_intro_ne_stuck_of_seq_type s T hsTy
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq T := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      have hSubstrTy :
          substr ≠ Term.Stuck ->
            __smtx_typeof (__eo_to_smt substr) = SmtType.Seq T := by
        intro hSubstrNe
        simpa [substr] using
          smt_typeof_seq_substr_body_of_seq a n len T hATy
            (by have hsimpa := hSubstrNe; (try simp [substr] at hsimpa ⊢); exact hsimpa)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Int := by
        rw [hOutEq]
        rcases eo_ite_cases_of_ne_stuck (__eo_is_neg n)
            (Term.Numeral (-1 : native_Int)) inRange hBodyNe with
          hNeg | hNeg
        · have hsimpa := (show __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int by rw [__smtx_typeof.eq_2]); (try simp [body, hNeg, eo_ite_true] at hsimpa ⊢); exact hsimpa
        · have hInRangeNe : inRange ≠ Term.Stuck := by
            simpa [body, hNeg, eo_ite_false] using hBodyNe
          have hInRangeTy :
              __smtx_typeof (__eo_to_smt inRange) = SmtType.Int := by
            rcases eo_ite_cases_of_ne_stuck (__eo_gt n len)
                (Term.Numeral (-1 : native_Int)) find hInRangeNe with
              hGt | hGt
            · have hsimpa := (show __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int by rw [__smtx_typeof.eq_2]); (try simp [inRange, hGt, eo_ite_true] at hsimpa ⊢); exact hsimpa
            · have hFindNe : find ≠ Term.Stuck := by
                simpa [inRange, hGt, eo_ite_false] using hInRangeNe
              have hSubstrNe : substr ≠ Term.Stuck := by
                simpa [substr, b, find] using
                  seq_find_left_ne_stuck_of_ne_stuck substr b n hFindNe
              have hFindTy :
                  __smtx_typeof (__eo_to_smt find) = SmtType.Int :=
                smt_typeof_seq_find_of_seq substr b n T
                  (hSubstrTy hSubstrNe) hBTy hnTy hFindNe
              simpa [inRange, hGt, eo_ite_false] using hFindTy
          simpa [body, hNeg, eo_ite_false] using hInRangeTy
      constructor
      · change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
              (__eo_to_smt n))
        rw [hOutTy]
        rw [typeof_str_indexof_eq, htTy, hsTy, hnTy]
        simp [__smtx_typeof_str_indexof, native_Teq, native_ite]
      · rw [hEvalEq, hOutEq]
        have hGuard : guard = Term.Boolean true :=
          eo_requires_eq_of_ne_stuck guard (Term.Boolean true) body
            (by simpa [out] using hOutNe)
        rcases seq_eval_of_seq_type M hM t T htTy with
          ⟨st, hTEval⟩
        rcases seq_eval_of_seq_type M hM s T hsTy with
          ⟨ss, hSEval⟩
        rcases seq_eval_of_seq_type M hM a T hATy with
          ⟨sa, hAEval⟩
        rcases seq_eval_of_seq_type M hM b T hBTy with
          ⟨sb, hBEval⟩
        have hIntroTRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy
            (by simpa [a] using hIntroTNe)
        have hIntroSRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt s)) :=
          smt_value_rel_str_nary_intro M hM s T hsTy
            (by simpa [b] using hIntroSNe)
        have hAUnpack :
            native_unpack_seq sa = native_unpack_seq st :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hAEval, hTEval] using hIntroTRel)
        have hBUnpack :
            native_unpack_seq sb = native_unpack_seq ss :=
          smt_value_rel_seq_unpack_eq
            (by simpa [hBEval, hSEval] using hIntroSRel)
        rcases eo_ite_cases_of_ne_stuck (__eo_is_neg n)
            (Term.Numeral (-1 : native_Int)) inRange hBodyNe with
          hNeg | hNeg
        · rcases int_arg_numeral_of_eo_is_neg_bool n true hnTy hNeg with
            ⟨i, hnEq, hiNegBool⟩
          have hiNeg : i < 0 := by
            exact of_decide_eq_true
              (by simpa [native_zlt] using hiNegBool)
          have hBodyEq :
              body = Term.Numeral (-1 : native_Int) := by
            simp [body, hNeg, eo_ite_true]
          rw [hBodyEq]
          have hNEval :
              __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral i := by
            rw [hnEq]
            change __smtx_model_eval M (SmtTerm.Numeral i) =
              SmtValue.Numeral i
            rw [__smtx_model_eval.eq_2]
          have hOrig :
              __smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_indexof) t) s) n)) =
                SmtValue.Numeral (-1 : native_Int) := by
            change __smtx_model_eval M
                (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                  (__eo_to_smt n)) =
              SmtValue.Numeral (-1 : native_Int)
            rw [show
                __smtx_model_eval M
                    (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                      (__eo_to_smt n)) =
                  __smtx_model_eval_str_indexof
                    (__smtx_model_eval M (__eo_to_smt t))
                    (__smtx_model_eval M (__eo_to_smt s))
                    (__smtx_model_eval M (__eo_to_smt n)) by
              rw [__smtx_model_eval.eq_def] <;> simp only]
            simp [hTEval, hSEval, hNEval, __smtx_model_eval_str_indexof,
              native_seq_indexof, hiNeg]
          rw [hOrig]
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M (SmtTerm.Numeral (-1 : native_Int)))
            (SmtValue.Numeral (-1 : native_Int))
          rw [__smtx_model_eval.eq_2]
          exact RuleProofs.smt_value_rel_refl _
        · have hInRangeNe : inRange ≠ Term.Stuck := by
            simpa [body, hNeg, eo_ite_false] using hBodyNe
          rcases int_arg_numeral_of_eo_is_neg_bool n false hnTy hNeg with
            ⟨i, hnEq, hiNegBool⟩
          have hiNonneg : 0 ≤ i := by
            have hiNot : ¬ i < 0 := by
              intro hiLt
              have hTrue : native_zlt i 0 = true := by
                simp [native_zlt, hiLt]
              rw [hTrue] at hiNegBool
              cases hiNegBool
            exact Int.not_lt.mp hiNot
          rcases eo_ite_cases_of_ne_stuck (__eo_gt n len)
              (Term.Numeral (-1 : native_Int)) find hInRangeNe with
            hGt | hGt
          · have hLenNe : len ≠ Term.Stuck :=
              eo_gt_right_ne_stuck_of_bool n len true hGt
            have hLenTy :
                __smtx_typeof (__eo_to_smt len) = SmtType.Int := by
              simpa [len] using
                smt_typeof_str_value_len_of_ne_stuck t
                  (by simpa [len] using hLenNe)
            rcases str_value_len_eval_seq_length M hM t T htTy
                (by simpa [len] using hLenNe) with
              ⟨stLen, nLen, hTEvalLen, hLenEq, hnLenEq⟩
            have hStLen : stLen = st := by
              rw [hTEval] at hTEvalLen
              injection hTEvalLen with hSeq
              exact hSeq.symm
            subst stLen
            rcases int_args_numerals_of_eo_gt_bool n len true hnTy hLenTy
                hGt with
              ⟨i', j, hnEq', hLenEq', hGtBool⟩
            have hiEq : i' = i := by
              rw [hnEq] at hnEq'
              injection hnEq' with h
              exact h.symm
            subst i'
            have hjEq : j = Int.ofNat (native_unpack_seq st).length := by
              have hLenEqLen : len = Term.Numeral nLen := by
                simpa [len] using hLenEq
              rw [hLenEq'] at hLenEqLen
              injection hLenEqLen with h
              rw [h]
              exact hnLenEq
            subst j
            have hLenLt : Int.ofNat (native_unpack_seq st).length < i := by
              exact of_decide_eq_true
                (by simpa [native_zlt] using hGtBool)
            have hInRangeEq :
                inRange = Term.Numeral (-1 : native_Int) := by
              simp [inRange, hGt, eo_ite_true]
            have hBodyEq :
                body = Term.Numeral (-1 : native_Int) := by
              simp [body, hNeg, eo_ite_false, hInRangeEq]
            rw [hBodyEq]
            have hNEval :
                __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral i := by
              rw [hnEq]
              change __smtx_model_eval M (SmtTerm.Numeral i) =
                SmtValue.Numeral i
              rw [__smtx_model_eval.eq_2]
            have hOrig :
                __smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_indexof) t) s) n)) =
                  SmtValue.Numeral (-1 : native_Int) := by
              change __smtx_model_eval M
                  (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                    (__eo_to_smt n)) =
                SmtValue.Numeral (-1 : native_Int)
              rw [show
                  __smtx_model_eval M
                      (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                        (__eo_to_smt n)) =
                    __smtx_model_eval_str_indexof
                      (__smtx_model_eval M (__eo_to_smt t))
                      (__smtx_model_eval M (__eo_to_smt s))
                      (__smtx_model_eval M (__eo_to_smt n)) by
                rw [__smtx_model_eval.eq_def] <;> simp only]
              simp [hTEval, hSEval, hNEval, __smtx_model_eval_str_indexof,
                native_seq_indexof_eq_neg_one_of_gt_len
                  (native_unpack_seq st) (native_unpack_seq ss) i hLenLt]
            rw [hOrig]
            change RuleProofs.smt_value_rel
              (__smtx_model_eval M (SmtTerm.Numeral (-1 : native_Int)))
              (SmtValue.Numeral (-1 : native_Int))
            rw [__smtx_model_eval.eq_2]
            exact RuleProofs.smt_value_rel_refl _
          · have hFindNe : find ≠ Term.Stuck := by
              simpa [inRange, hGt, eo_ite_false] using hInRangeNe
            have hSubstrNe : substr ≠ Term.Stuck := by
              simpa [substr, b, find] using
                seq_find_left_ne_stuck_of_ne_stuck substr b n hFindNe
            have hLenNe : len ≠ Term.Stuck :=
              eo_gt_right_ne_stuck_of_bool n len false hGt
            have hLenTy :
                __smtx_typeof (__eo_to_smt len) = SmtType.Int := by
              simpa [len] using
                smt_typeof_str_value_len_of_ne_stuck t
                  (by simpa [len] using hLenNe)
            rcases str_value_len_eval_seq_length M hM t T htTy
                (by simpa [len] using hLenNe) with
              ⟨stLen, nLen, hTEvalLen, hLenEq, hnLenEq⟩
            have hStLen : stLen = st := by
              rw [hTEval] at hTEvalLen
              injection hTEvalLen with hSeq
              exact hSeq.symm
            subst stLen
            have hLenTerm :
                len =
                  Term.Numeral
                    (Int.ofNat (native_unpack_seq st).length) := by
              have hLenEqLen : len = Term.Numeral nLen := by
                simpa [len] using hLenEq
              rw [hLenEqLen, hnLenEq]
            rcases int_args_numerals_of_eo_gt_bool n len false hnTy hLenTy
                hGt with
              ⟨i', j, hnEq', hLenEq', hGtBool⟩
            have hiEq : i' = i := by
              rw [hnEq] at hnEq'
              injection hnEq' with h
              exact h.symm
            subst i'
            have hjEq : j = Int.ofNat (native_unpack_seq st).length := by
              rw [hLenEq'] at hLenTerm
              injection hLenTerm
            subst j
            have hILeLen :
                i ≤ Int.ofNat (native_unpack_seq st).length := by
              have hNotLt :
                  ¬ Int.ofNat (native_unpack_seq st).length < i := by
                intro hLt
                have hTrue :
                    native_zlt
                        (Int.ofNat (native_unpack_seq st).length) i =
                      true := by
                  unfold native_zlt
                  exact decide_eq_true hLt
                rw [hTrue] at hGtBool
                cases hGtBool
              exact Int.not_lt.mp hNotLt
            let off := Int.toNat i
            have hOffEq : (Int.ofNat off : Int) = i :=
              Int.toNat_of_nonneg hiNonneg
            have hOffLe : off ≤ (native_unpack_seq st).length := by
              exact Int.ofNat_le.mp (by
                change (Int.ofNat off : Int) ≤
                  Int.ofNat (native_unpack_seq st).length
                rw [hOffEq]
                exact hILeLen)
            have hLenNegFalse :
                __eo_is_neg len = Term.Boolean false := by
              rw [hLenTerm]
              simp [__eo_is_neg, native_zlt]
            have hSubstrEq :
                substr = __seq_subsequence_rec n len a := by
              simp [substr, hLenNegFalse, eo_ite_false]
            have hSubseqNe :
                __seq_subsequence_rec n len a ≠ Term.Stuck := by
              rw [hSubstrEq] at hSubstrNe
              exact hSubstrNe
            rcases seq_eval_of_seq_type M hM substr T
                (hSubstrTy hSubstrNe) with
              ⟨sSub, hSubstrEval⟩
            have hSubseqEval :
                __smtx_model_eval M
                    (__eo_to_smt (__seq_subsequence_rec n len a)) =
                  SmtValue.Seq sSub := by
              rw [← hSubstrEq]
              exact hSubstrEval
            have hTNN : T ≠ SmtType.None :=
              smt_seq_component_ne_none_of_typeof_seq t T htTy
            have hPattern : SeqFindPatternOk b T sb := by
              simpa [b] using
                guarded_intro_pattern_ok M hM s T sb hTNN hsTy hGuard
                  (by simpa [b] using hBTy)
                  (by simpa [b] using hBEval)
            have hSubstrConst :
                __is_seq_const_rec substr = Term.Boolean true := by
              rw [hSubstrEq]
              exact
                is_seq_const_rec_seq_subsequence_rec_true_of_seq n len a T
                  hATy hSubseqNe
            have hnOff : n = Term.Numeral (Int.ofNat off) := by
              rw [hnEq, hOffEq]
            have hFindEqNative :
                find =
                  Term.Numeral
                    (native_seq_indexof_offset (native_unpack_seq sSub)
                      (native_unpack_seq sb) off) := by
              simpa [find] using
                seq_find_const_rec_eq_native_indexof_offset M hM substr b n T
                  sSub sb off hTNN hSubstrConst (hSubstrTy hSubstrNe)
                  hBTy hSubstrEval hBEval hPattern hnOff hFindNe
            have hSaTy :
                __smtx_typeof_seq_value sa = SmtType.Seq T :=
              smt_typeof_seq_value_of_eval_seq M hM a T sa hATy hAEval
            have hSaElem : __smtx_elem_typeof_seq_value sa = T :=
              elem_typeof_seq_value_of_typeof_seq_value hSaTy
            have hEndNonneg :
                0 ≤ (Int.ofNat (native_unpack_seq st).length : Int) :=
              Int.natCast_nonneg (native_unpack_seq st).length
            have hSubseqRel :=
              smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
                M hM n len a T i
                (Int.ofNat (native_unpack_seq st).length)
                hnEq hLenTerm hEndNonneg hATy hSubseqNe
            have hExtractDrop :
                native_seq_extract (native_unpack_seq sa) i
                    (Int.ofNat (native_unpack_seq st).length - i) =
                  (native_unpack_seq st).drop off := by
              rw [hAUnpack]
              rw [← hOffEq]
              have hLenSub :
                  Int.ofNat (native_unpack_seq st).length -
                      Int.ofNat off =
                    Int.ofNat ((native_unpack_seq st).length - off) := by
                exact (Int.ofNat_sub hOffLe).symm
              rw [hLenSub]
              exact native_seq_extract_to_end_nat
                (native_unpack_seq st) off hOffLe
            have hSubstrUnpack :
                native_unpack_seq sSub =
                  (native_unpack_seq st).drop off := by
              have hPackRel :
                  RuleProofs.smt_value_rel (SmtValue.Seq sSub)
                    (SmtValue.Seq
                      (native_pack_seq T
                        (native_seq_extract (native_unpack_seq sa) i
                          (Int.ofNat (native_unpack_seq st).length - i)))) := by
                simpa [hSubseqEval, hAEval,
                  __smtx_model_eval_str_substr, hSaElem] using hSubseqRel
              have hUnpack := smt_value_rel_seq_unpack_eq hPackRel
              calc
                native_unpack_seq sSub =
                    native_seq_extract (native_unpack_seq sa) i
                      (Int.ofNat (native_unpack_seq st).length - i) := by
                  simpa [Smtm.native_unpack_pack_seq] using hUnpack
                _ = (native_unpack_seq st).drop off := hExtractDrop
            have hInRangeEq : inRange = find := by
              simp [inRange, hGt, eo_ite_false]
            have hBodyEq : body = find := by
              simp [body, hNeg, eo_ite_false, hInRangeEq]
            rw [hBodyEq, hFindEqNative]
            have hNativeEq :
                native_seq_indexof_offset (native_unpack_seq sSub)
                    (native_unpack_seq sb) off =
                  native_seq_indexof (native_unpack_seq st)
                    (native_unpack_seq ss) i := by
              rw [hSubstrUnpack, hBUnpack]
              rw [native_seq_indexof_offset_drop_eq
                (native_unpack_seq st) (native_unpack_seq ss) off hOffLe]
              rw [hOffEq]
            rw [hNativeEq]
            have hNEval :
                __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral i := by
              rw [hnEq]
              change __smtx_model_eval M (SmtTerm.Numeral i) =
                SmtValue.Numeral i
              rw [__smtx_model_eval.eq_2]
            have hOrig :
                __smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_indexof) t) s) n)) =
                  SmtValue.Numeral
                    (native_seq_indexof (native_unpack_seq st)
                      (native_unpack_seq ss) i) := by
              change __smtx_model_eval M
                  (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                    (__eo_to_smt n)) =
                SmtValue.Numeral
                  (native_seq_indexof (native_unpack_seq st)
                    (native_unpack_seq ss) i)
              rw [show
                  __smtx_model_eval M
                      (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt s)
                        (__eo_to_smt n)) =
                    __smtx_model_eval_str_indexof
                      (__smtx_model_eval M (__eo_to_smt t))
                      (__smtx_model_eval M (__eo_to_smt s))
                      (__smtx_model_eval M (__eo_to_smt n)) by
                rw [__smtx_model_eval.eq_def] <;> simp only]
              simp [hTEval, hSEval, hNEval, __smtx_model_eval_str_indexof]
            rw [hOrig]
            change RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (SmtTerm.Numeral
                  (native_seq_indexof (native_unpack_seq st)
                    (native_unpack_seq ss) i)))
              (SmtValue.Numeral
                (native_seq_indexof (native_unpack_seq st)
                  (native_unpack_seq ss) i))
            rw [__smtx_model_eval.eq_2]
            exact RuleProofs.smt_value_rel_refl _
  | case10 t s =>
      let a := __str_nary_intro t
      let b := __str_nary_intro s
      have hPrefixNe : __seq_is_prefix a b ≠ Term.Stuck := by
        simpa [__seq_eval, a, b] using hEvalNe
      have hPrefixNN :
          term_has_non_none_type
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_prefixof)
          (typeof_str_prefixof_eq (__eo_to_smt t) (__eo_to_smt s))
          hPrefixNN with
        ⟨T, htTy, hsTy⟩
      have hIntroTNe : a ≠ Term.Stuck :=
        seq_is_prefix_left_ne_stuck_of_ne_stuck a b hPrefixNe
      have hIntroSNe : b ≠ Term.Stuck :=
        seq_is_prefix_right_ne_stuck_of_ne_stuck a b hPrefixNe
      have hTComponents :
          type_inhabited T ∧
            __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
        simpa [b] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [b] using hIntroSNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroTNN) (by simpa [a] using hIntroTNe)
      have hBTy :
          __smtx_typeof (__eo_to_smt b) = SmtType.Seq T := by
        simpa [b] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [b] using hIntroSNN) (by simpa [b] using hIntroSNe)
      rcases seq_eval_of_seq_type M hM a T hATy with
        ⟨sx, hAEval⟩
      rcases seq_eval_of_seq_type M hM b T hBTy with
        ⟨sy, hBEval⟩
      have hPrefixEq :
          __seq_is_prefix a b =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        seq_prefix_eq_bool_native M hM a b T sx sy
          (type_wf_non_none hTComponents.2) hATy hBTy hAEval hBEval hPrefixNe
      constructor
      · change __smtx_typeof (__eo_to_smt (__seq_is_prefix a b)) =
          __smtx_typeof
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s))
        rw [hPrefixEq]
        change __smtx_typeof
            (SmtTerm.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))) =
          __smtx_typeof
            (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s))
        rw [__smtx_typeof.eq_1, typeof_str_prefixof_eq]
        simp [__smtx_typeof_seq_op_2_ret, htTy, hsTy, native_Teq, native_ite]
      · have hSxTy :
            __smtx_typeof_seq_value sx = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM a T sx
            hATy hAEval
        have hSyTy :
            __smtx_typeof_seq_value sy = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM b T sy
            hBTy hBEval
        have hSeqPrefixEval :
            __smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)) =
              SmtValue.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy)) := by
          rw [hAEval, hBEval]
          exact smtx_model_eval_str_prefixof_seq_eq sx sy T
            hSxTy hSyTy
        have hIntroTRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy
            (by simpa [a] using hIntroTNe)
        have hIntroSRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt s)) :=
          smt_value_rel_str_nary_intro M hM s T hsTy
            (by simpa [b] using hIntroSNe)
        have hPrefixRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b)))
              (__smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s))) :=
          smt_value_rel_model_eval_str_prefixof_of_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s))
            hIntroTRel hIntroSRel
        have hEvalEq :
            __seq_eval
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) t) s) =
              __seq_is_prefix a b := by
          simp [__seq_eval, a, b]
        have hOrigEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) t) s)) =
              __smtx_model_eval_str_prefixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s)) := by
          have hsimpa :=
            (show
              __smtx_model_eval M
                  (SmtTerm.str_prefixof (__eo_to_smt t) (__eo_to_smt s)) =
                __smtx_model_eval_str_prefixof
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt s)) by
              rw [__smtx_model_eval.eq_87])
          try simp at hsimpa ⊢
          exact hsimpa
        rw [hEvalEq]
        rw [hOrigEval]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_is_prefix a b)))
          (__smtx_model_eval_str_prefixof
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s)))
        rw [hPrefixEq]
        have hBoolEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Boolean
                    (native_seq_prefix_eq (native_unpack_seq sx)
                      (native_unpack_seq sy)))) =
              SmtValue.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy)) := by
          change __smtx_model_eval M
              (SmtTerm.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy))) =
            SmtValue.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))
          rw [__smtx_model_eval.eq_1]
        rw [hBoolEval]
        change RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (native_seq_prefix_eq (native_unpack_seq sx)
              (native_unpack_seq sy)))
          (__smtx_model_eval_str_prefixof
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s)))
        rw [← hSeqPrefixEval]
        exact hPrefixRel
  | case11 t s =>
      let guardT := __is_seq_const t
      let guardS := __is_seq_const s
      let it := __str_nary_intro t
      let is := __str_nary_intro s
      let rt := __eo_list_rev (Term.UOp UserOp.str_concat) it
      let rs := __eo_list_rev (Term.UOp UserOp.str_concat) is
      have hReqNe :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true)
                (__seq_is_prefix rt rs)) ≠ Term.Stuck := by
        simpa [__seq_eval, guardT, guardS, it, is, rt, rs] using hEvalNe
      have hGuardT : guardT = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs))
          hReqNe
      have hReqSNe :
          __eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs) ≠
            Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs))
          hReqNe
      have hReqTEq :
          __eo_requires guardT (Term.Boolean true)
              (__eo_requires guardS (Term.Boolean true)
                (__seq_is_prefix rt rs)) =
            __eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs) :=
        eo_requires_eq_result_of_ne_stuck guardT (Term.Boolean true)
          (__eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs))
          hReqNe
      have hGuardS : guardS = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guardS (Term.Boolean true)
          (__seq_is_prefix rt rs) hReqSNe
      have hReqSEq :
          __eo_requires guardS (Term.Boolean true) (__seq_is_prefix rt rs) =
            __seq_is_prefix rt rs :=
        eo_requires_eq_result_of_ne_stuck guardS (Term.Boolean true)
          (__seq_is_prefix rt rs) hReqSNe
      have hPrefixNe : __seq_is_prefix rt rs ≠ Term.Stuck := by
        exact eo_requires_result_ne_stuck_of_ne_stuck guardS
          (Term.Boolean true) (__seq_is_prefix rt rs) hReqSNe
      have hSuffixNN :
          term_has_non_none_type
            (SmtTerm.str_suffixof (__eo_to_smt t) (__eo_to_smt s)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_suffixof)
          (typeof_str_suffixof_eq (__eo_to_smt t) (__eo_to_smt s))
          hSuffixNN with
        ⟨T, htTy, hsTy⟩
      have hRTNe : rt ≠ Term.Stuck :=
        seq_is_prefix_left_ne_stuck_of_ne_stuck rt rs hPrefixNe
      have hRSNe : rs ≠ Term.Stuck :=
        seq_is_prefix_right_ne_stuck_of_ne_stuck rt rs hPrefixNe
      have hIntroTNe : it ≠ Term.Stuck :=
        eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
          it hRTNe
      have hIntroSNe : is ≠ Term.Stuck :=
        eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
          is hRSNe
      have hListT :
          __eo_is_list (Term.UOp UserOp.str_concat) it = Term.Boolean true :=
        eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
          it hRTNe
      have hListS :
          __eo_is_list (Term.UOp UserOp.str_concat) is = Term.Boolean true :=
        eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
          is hRSNe
      have hTComponents :
          type_inhabited T ∧
            __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroTNN :
          __smtx_typeof (__eo_to_smt it) ≠ SmtType.None := by
        simpa [it] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [it] using hIntroTNe)
      have hIntroSNN :
          __smtx_typeof (__eo_to_smt is) ≠ SmtType.None := by
        simpa [is] using
          str_nary_intro_has_smt_translation_of_seq_wf s T hsTy
            hTComponents.1 hTComponents.2 (by simpa [is] using hIntroSNe)
      have hIntroTTy :
          __smtx_typeof (__eo_to_smt it) = SmtType.Seq T := by
        simpa [it] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [it] using hIntroTNN) (by simpa [it] using hIntroTNe)
      have hIntroSTy :
          __smtx_typeof (__eo_to_smt is) = SmtType.Seq T := by
        simpa [is] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy
            (by simpa [is] using hIntroSNN) (by simpa [is] using hIntroSNe)
      have hRTTy :
          __smtx_typeof (__eo_to_smt rt) = SmtType.Seq T := by
        simpa [it, rt] using
          smt_typeof_list_rev_str_concat_of_seq it T
            hListT hIntroTTy hRTNe
      have hRSTy :
          __smtx_typeof (__eo_to_smt rs) = SmtType.Seq T := by
        simpa [is, rs] using
          smt_typeof_list_rev_str_concat_of_seq is T
            hListS hIntroSTy hRSNe
      have hElimRT :
          __str_nary_elim rt ≠ Term.Stuck := by
        simpa [it, rt] using
          str_nary_elim_list_rev_str_nary_intro_ne_stuck_of_seq
            t T htTy hIntroTNN hIntroTNe hRTNe
      have hElimRS :
          __str_nary_elim rs ≠ Term.Stuck := by
        simpa [is, rs] using
          str_nary_elim_list_rev_str_nary_intro_ne_stuck_of_seq
            s T hsTy hIntroSNN hIntroSNe hRSNe
      have hElimRTTy :
          __smtx_typeof (__eo_to_smt (__str_nary_elim rt)) =
            SmtType.Seq T :=
        smt_typeof_str_nary_elim_of_seq_ne_stuck rt T
          hRTTy hElimRT
      have hElimRSTy :
          __smtx_typeof (__eo_to_smt (__str_nary_elim rs)) =
            SmtType.Seq T :=
        smt_typeof_str_nary_elim_of_seq_ne_stuck rs T
          hRSTy hElimRS
      have hRTElimRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt rt))
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rt))) :=
        RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rt)))
          (__smtx_model_eval M (__eo_to_smt rt))
          (smt_value_rel_str_nary_elim M hM rt T hRTTy
            hElimRT)
      have hRSElimRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt rs))
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rs))) :=
        RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rs)))
          (__smtx_model_eval M (__eo_to_smt rs))
          (smt_value_rel_str_nary_elim M hM rs T hRSTy
            hElimRS)
      rcases seq_eval_of_seq_type M hM rt T hRTTy with
        ⟨sx, hRTEval⟩
      rcases seq_eval_of_seq_type M hM rs T hRSTy with
        ⟨sy, hRSEval⟩
      have hPrefixEq :
          __seq_is_prefix rt rs =
            Term.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy)) :=
        seq_prefix_eq_bool_native M hM rt rs T sx sy
          (type_wf_non_none hTComponents.2) hRTTy hRSTy hRTEval hRSEval hPrefixNe
      have hEvalEq :
          __seq_eval
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) t) s) =
            __seq_is_prefix rt rs := by
        rw [show __seq_eval
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) t) s) =
              __eo_requires guardT (Term.Boolean true)
                (__eo_requires guardS (Term.Boolean true)
                  (__seq_is_prefix rt rs)) by
            simp [__seq_eval, guardT, guardS, it, is, rt, rs]]
        rw [hReqTEq, hReqSEq]
      constructor
      · rw [hEvalEq]
        change __smtx_typeof (__eo_to_smt (__seq_is_prefix rt rs)) =
          __smtx_typeof
            (SmtTerm.str_suffixof (__eo_to_smt t) (__eo_to_smt s))
        rw [hPrefixEq]
        change __smtx_typeof
            (SmtTerm.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))) =
          __smtx_typeof
            (SmtTerm.str_suffixof (__eo_to_smt t) (__eo_to_smt s))
        rw [__smtx_typeof.eq_1, typeof_str_suffixof_eq]
        simp [__smtx_typeof_seq_op_2_ret, htTy, hsTy, native_Teq, native_ite]
      · rcases seq_eval_of_seq_type M hM t T htTy with
          ⟨st, hTEval⟩
        rcases seq_eval_of_seq_type M hM s T hsTy with
          ⟨ss, hSEval⟩
        have hStTy :
            __smtx_typeof_seq_value st = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM t T st
            htTy hTEval
        have hSsTy :
            __smtx_typeof_seq_value ss = SmtType.Seq T :=
          smt_typeof_seq_value_of_eval_seq M hM s T ss
            hsTy hSEval
        have hSuffixEval :
            __smtx_model_eval_str_suffixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s)) =
              SmtValue.Boolean
                (native_seq_prefix_eq
                  (native_seq_rev (native_unpack_seq st))
                  (native_seq_rev (native_unpack_seq ss))) := by
          rw [hTEval, hSEval]
          exact smtx_model_eval_str_suffixof_seq_eq st ss T
            hStTy hSsTy
        have hOrigEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) t) s)) =
              __smtx_model_eval_str_suffixof
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt s)) := by
          have hsimpa :=
            (show
              __smtx_model_eval M
                  (SmtTerm.str_suffixof (__eo_to_smt t) (__eo_to_smt s)) =
                __smtx_model_eval_str_suffixof
                  (__smtx_model_eval M (__eo_to_smt t))
                  (__smtx_model_eval M (__eo_to_smt s)) by
              rw [__smtx_model_eval.eq_88])
          try simp at hsimpa ⊢
          exact hsimpa
        rw [hEvalEq]
        rw [hOrigEval]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__seq_is_prefix rt rs)))
          (__smtx_model_eval_str_suffixof
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt s)))
        rw [hPrefixEq]
        have hBoolEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Boolean
                    (native_seq_prefix_eq (native_unpack_seq sx)
                      (native_unpack_seq sy)))) =
              SmtValue.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy)) := by
          change __smtx_model_eval M
              (SmtTerm.Boolean
                (native_seq_prefix_eq (native_unpack_seq sx)
                  (native_unpack_seq sy))) =
            SmtValue.Boolean
              (native_seq_prefix_eq (native_unpack_seq sx)
                (native_unpack_seq sy))
          rw [__smtx_model_eval.eq_1]
        rw [hBoolEval, hSuffixEval]
        have hNativeSuffix :
            native_seq_prefix_eq (native_unpack_seq sx) (native_unpack_seq sy) =
              native_seq_prefix_eq
                (native_seq_rev (native_unpack_seq st))
                (native_seq_rev (native_unpack_seq ss)) := by
          have hRTToRevT :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt rt))
                (__smtx_model_eval M
                  (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t))) :=
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt rt))
              (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rt)))
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)))
              hRTElimRel
              (by
                simpa [it, rt] using
                  smt_value_rel_elim_rev_str_nary_intro_to_str_rev M hM
                    t T htTy (by simpa [guardT] using hGuardT)
                    hIntroTNN hIntroTNe hRTNe hElimRT)
          have hRSToRevS :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt rs))
                (__smtx_model_eval M
                  (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) s))) :=
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt rs))
              (__smtx_model_eval M (__eo_to_smt (__str_nary_elim rs)))
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) s)))
              hRSElimRel
              (by
                simpa [is, rs] using
                  smt_value_rel_elim_rev_str_nary_intro_to_str_rev M hM
                    s T hsTy (by simpa [guardS] using hGuardS)
                    hIntroSNN hIntroSNe hRSNe hElimRS)
          have hRevTEval :
              __smtx_model_eval M
                  (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)) =
                SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value st)
                    (native_seq_rev (native_unpack_seq st))) := by
            change __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt t)) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_rev (native_unpack_seq st)))
            rw [__smtx_model_eval.eq_89, hTEval]
            rfl
          have hRevSEval :
              __smtx_model_eval M
                  (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) s)) =
                SmtValue.Seq
                  (native_pack_seq (__smtx_elem_typeof_seq_value ss)
                    (native_seq_rev (native_unpack_seq ss))) := by
            change __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt s)) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value ss)
                  (native_seq_rev (native_unpack_seq ss)))
            rw [__smtx_model_eval.eq_89, hSEval]
            rfl
          have hRTUnpack :
              native_unpack_seq sx =
                native_seq_rev (native_unpack_seq st) := by
            have hRel :
                RuleProofs.smt_value_rel
                  (SmtValue.Seq sx)
                  (SmtValue.Seq
                    (native_pack_seq (__smtx_elem_typeof_seq_value st)
                      (native_seq_rev (native_unpack_seq st)))) := by
              simpa [hRTEval, hRevTEval] using hRTToRevT
            have hUnpack := smt_value_rel_seq_unpack_eq hRel
            simpa [Smtm.native_unpack_pack_seq] using hUnpack
          have hRSUnpack :
              native_unpack_seq sy =
                native_seq_rev (native_unpack_seq ss) := by
            have hRel :
                RuleProofs.smt_value_rel
                  (SmtValue.Seq sy)
                  (SmtValue.Seq
                    (native_pack_seq (__smtx_elem_typeof_seq_value ss)
                      (native_seq_rev (native_unpack_seq ss)))) := by
              simpa [hRSEval, hRevSEval] using hRSToRevS
            have hUnpack := smt_value_rel_seq_unpack_eq hRel
            simpa [Smtm.native_unpack_pack_seq] using hUnpack
          rw [hRTUnpack, hRSUnpack]
        rw [hNativeSuffix]
        exact RuleProofs.smt_value_rel_refl _
  | case12 t n =>
      let a := __str_nary_intro t
      let u := __eo_add n (Term.Numeral 1)
      let body :=
        __eo_ite (__eo_is_neg u)
          (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
          (__seq_subsequence_rec n u a)
      let out := __str_nary_elim body
      have hOutNe : out ≠ Term.Stuck := by
        simpa [__seq_eval, a, u, body, out] using hEvalNe
      have hBodyNe : body ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck body hOutNe
      have hAtNN :
          term_has_non_none_type
            (SmtTerm.str_at (__eo_to_smt t) (__eo_to_smt n)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases str_at_args_of_non_none hAtNN with ⟨T, htTy, hnTy⟩
      have hIntroNe : a ≠ Term.Stuck := by
        simpa [a] using str_nary_intro_ne_stuck_of_seq_type t T htTy
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF :
            __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
      have hATy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
      have hBodyTy :
          __smtx_typeof (__eo_to_smt body) = SmtType.Seq T := by
        simpa [body] using
          smt_typeof_seq_substr_body_of_seq a n u T hATy
            (by simpa [body] using hBodyNe)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
        simpa [out] using
          smt_typeof_str_nary_elim_of_seq_ne_stuck body T hBodyTy
            (by simpa [out] using hOutNe)
      constructor
      · change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (SmtTerm.str_at (__eo_to_smt t) (__eo_to_smt n))
        rw [hOutTy, typeof_str_at_eq, htTy, hnTy]
        simp [__smtx_typeof_str_at]
      · have hOutRelBody :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt out))
              (__smtx_model_eval M (__eo_to_smt body)) := by
          simpa [out] using
            smt_value_rel_str_nary_elim M hM body T hBodyTy
              (by simpa [out] using hOutNe)
        have hIntroRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt t)) :=
          smt_value_rel_str_nary_intro M hM t T htTy
            (by simpa [a] using hIntroNe)
        have hAtCong :
            RuleProofs.smt_value_rel
              (__smtx_model_eval_str_at
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt n)))
              (__smtx_model_eval_str_at
                (__smtx_model_eval M (__eo_to_smt t))
                (__smtx_model_eval M (__eo_to_smt n))) :=
          smt_value_rel_model_eval_str_at_of_rel
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt n))
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt n))
            hIntroRel (RuleProofs.smt_value_rel_refl _)
        have hBodyRelAtA :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt body))
              (__smtx_model_eval_str_at
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt n))) := by
          unfold __smtx_model_eval_str_at
          rcases eo_ite_cases_of_ne_stuck (__eo_is_neg u)
              (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))
              (__seq_subsequence_rec n u a)
              (by simpa [body] using hBodyNe) with hCond | hCond
          · have hAddNe : u ≠ Term.Stuck := by
              intro hu
              rw [hu] at hCond
              simp [__eo_is_neg] at hCond
            have hOneTy :
                __smtx_typeof
                    (__eo_to_smt (Term.Numeral (1 : native_Int))) =
                  SmtType.Int := by
              change __smtx_typeof (SmtTerm.Numeral (1 : native_Int)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            rcases eo_add_int_args_numerals_of_ne_stuck n
                (Term.Numeral (1 : native_Int)) hnTy hOneTy
                (by simpa [u] using hAddNe) with
              ⟨i, j, rfl, hOneEq, hUEq⟩
            cases hOneEq
            have hNegBool :
                native_zlt (native_zplus i 1) 0 = true := by
              simpa [u, hUEq, __eo_is_neg] using hCond
            have hEnd : i + 1 < 0 := by
              have hsimpa :=
                hNegBool
              try simp [native_zlt, SmtEval.native_zlt, native_zplus] at hsimpa ⊢
              exact of_decide_eq_true hsimpa
            have hBodyEq :
                body = Term.UOp1 UserOp1.seq_empty (__eo_typeof a) := by
              simp [body, u, hUEq, __eo_is_neg, hNegBool, eo_ite_true]
            rw [hBodyEq]
            change RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.UOp1 UserOp1.seq_empty (__eo_typeof a))))
              (__smtx_model_eval_str_substr
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (SmtTerm.Numeral i))
                (SmtValue.Numeral 1))
            rw [__smtx_model_eval.eq_2]
            exact
              smt_value_rel_raw_empty_str_substr_of_end_neg
                M hM a T i 1 hATy hEnd
          · have hAddNe : u ≠ Term.Stuck := by
              intro hu
              rw [hu] at hCond
              simp [__eo_is_neg] at hCond
            have hOneTy :
                __smtx_typeof
                    (__eo_to_smt (Term.Numeral (1 : native_Int))) =
                  SmtType.Int := by
              change __smtx_typeof (SmtTerm.Numeral (1 : native_Int)) =
                SmtType.Int
              rw [__smtx_typeof.eq_2]
            rcases eo_add_int_args_numerals_of_ne_stuck n
                (Term.Numeral (1 : native_Int)) hnTy hOneTy
                (by simpa [u] using hAddNe) with
              ⟨i, j, rfl, hOneEq, hUEq⟩
            cases hOneEq
            have hNegFalse :
                native_zlt (native_zplus i 1) 0 = false := by
              simpa [u, hUEq, __eo_is_neg] using hCond
            have hEndNonneg : 0 <= native_zplus i 1 := by
              have hNotLt : ¬ native_zplus i 1 < 0 := by
                simpa [native_zlt, SmtEval.native_zlt] using hNegFalse
              exact Int.le_of_not_gt hNotLt
            have hBodyEq :
                body =
                  __seq_subsequence_rec (Term.Numeral i)
                    (Term.Numeral (native_zplus i 1)) a := by
              simp [body, u, hUEq, __eo_is_neg, hNegFalse, eo_ite_false]
            have hSubseqNe :
                __seq_subsequence_rec (Term.Numeral i)
                    (Term.Numeral (native_zplus i 1)) a ≠
                  Term.Stuck := by
              simpa [hBodyEq] using hBodyNe
            rw [hBodyEq]
            have hLenEq : native_zplus i 1 - i = 1 := by
              calc
                native_zplus i 1 - i = (i + 1) - i := by
                  simp [native_zplus, SmtEval.native_zplus]
                _ = (1 + i) - i := by rw [Int.add_comm i 1]
                _ = 1 := by simp
            change RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (__seq_subsequence_rec (Term.Numeral i)
                    (Term.Numeral (native_zplus i 1)) a)))
              (__smtx_model_eval_str_substr
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (SmtTerm.Numeral i))
                (SmtValue.Numeral 1))
            rw [__smtx_model_eval.eq_2]
            simpa [hLenEq] using
              smt_value_rel_seq_subsequence_rec_str_substr_of_numerals
                M hM (Term.Numeral i) (Term.Numeral (native_zplus i 1))
                a T i (native_zplus i 1) rfl rfl hEndNonneg hATy
                hSubseqNe
        rw [smtx_model_eval_str_at_term_eq M t n]
        exact RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt out))
          (__smtx_model_eval M (__eo_to_smt body))
          (__smtx_model_eval_str_at
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M (__eo_to_smt n)))
          hOutRelBody
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt body))
            (__smtx_model_eval_str_at
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt n)))
            (__smtx_model_eval_str_at
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval M (__eo_to_smt n)))
            hBodyRelAtA hAtCong)
  | case13 t =>
      let guard := __is_seq_const t
      let a := __str_nary_intro t
      let r := __eo_list_rev (Term.UOp UserOp.str_concat) a
      let out := __str_nary_elim r
      have hReqNe : __eo_requires guard (Term.Boolean true) out ≠
          Term.Stuck := by
        simpa [__seq_eval, guard, a, r, out] using hEvalNe
      have hGuard : guard = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck guard (Term.Boolean true) out hReqNe
      have hSeqEq :
          __seq_eval (Term.Apply (Term.UOp UserOp.str_rev) t) = out := by
        simpa [__seq_eval, guard, a, r, out] using
          eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) out
            hReqNe
      have hOutNe : out ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck guard (Term.Boolean true)
          out hReqNe
      have hRevNe : r ≠ Term.Stuck :=
        str_nary_elim_arg_ne_stuck_of_ne_stuck r hOutNe
      have hList :
          __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true :=
        eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
          a hRevNe
      have hIntroNe : a ≠ Term.Stuck :=
        eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
          a hRevNe
      have hRevNN :
          term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        have hsimpa := hNN
        try simp at hsimpa ⊢
        exact hsimpa
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq (__eo_to_smt t)) hRevNN with
        ⟨T, htTy⟩
      have hTComponents :
          type_inhabited T ∧ __smtx_type_wf T = true := by
        have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
          have hGood :=
            smt_term_result_seq_components_wf_of_non_none
              (__eo_to_smt t)
              (by
                unfold term_has_non_none_type
                rw [htTy]
                exact seq_ne_none T)
          simpa [htTy, type_result_seq_components_wf] using hGood
        exact seq_component_inhabited_wf_of_seq_wf T hSeqWF
      have hIntroNN :
          __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        simpa [a] using
          str_nary_intro_has_smt_translation_of_seq_wf t T htTy
            hTComponents.1 hTComponents.2 (by simpa [a] using hIntroNe)
      have hIntroTy :
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        simpa [a] using
          smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy
            (by simpa [a] using hIntroNN) (by simpa [a] using hIntroNe)
      have hOutTy :
          __smtx_typeof (__eo_to_smt out) = SmtType.Seq T := by
        simpa [r, out] using
          smt_typeof_str_nary_elim_list_rev_of_seq a T hList hIntroTy
            (by simpa [r] using hRevNe) (by simpa [r, out] using hOutNe)
      have hStrRevTy :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)) =
            SmtType.Seq T :=
        smt_typeof_str_rev_of_seq t T htTy
      constructor
      · rw [hSeqEq]
        change __smtx_typeof (__eo_to_smt out) =
          __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t))
        rw [hOutTy, hStrRevTy]
      · rw [hSeqEq]
        change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt out))
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) t)))
        rcases str_value_len_numeral_of_is_seq_const_true t
            (by simpa [guard] using hGuard) with
          ⟨n, hLen⟩
        rcases RuleProofs.value_len_numeral_cases t n hLen with
          ⟨w, ht⟩ | ⟨e, ss, ht⟩ | ⟨U, ht⟩ | ⟨e, ht⟩
        · subst t
          simp [guard, __is_seq_const, __is_seq_const_rec] at hGuard
        · subst t
          let head := Term.Apply (Term.UOp UserOp.seq_unit) e
          have hTailSeq :=
            RuleProofs.seq_const_rec_tail_true_of_concat_seqUnit_value_len_numeral
              e ss n (by simpa [head] using hLen)
          have hRawSeq :
              __is_seq_const_rec (mkConcat head ss) = Term.Boolean true := by
            simp [mkConcat, head, __is_seq_const_rec, hTailSeq]
          have hRawList :
              __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head ss) =
                Term.Boolean true :=
            RuleProofs.is_seq_const_rec_true_is_str_concat_list
              (mkConcat head ss) hRawSeq
          have hIntroEq : a = mkConcat head ss := by
            simp [a, head, __str_nary_intro, __eo_list_singleton_intro,
              hRawList, eo_ite_true]
          simpa [out, r, a, head, hIntroEq, mkConcat] using
            (smt_value_rel_elim_rev_seq_unit_list M hM ss e T
            hRawList
            (by simpa [head] using htTy)
            ⟨n, by simpa [head] using hLen⟩).2
        · subst t
          let nil :=
            Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
          have hNil :
              __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
                Term.Boolean true := by
            simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat]
          have hNotConcat : ¬ ∃ head tail : Term, nil = mkConcat head tail := by
            intro hConcat
            rcases hConcat with ⟨head, tail, hEq⟩
            change
              Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) =
                Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail
              at hEq
            cases hEq
          have hRevEq :
              __eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_nary_intro nil) =
                __str_nary_intro nil :=
            eo_list_rev_str_nary_intro_eq_of_not_str_concat nil hNotConcat
              (by simpa [nil, a] using hIntroNe)
              (by simpa [nil, a, r] using hRevNe)
          have hElimIntroNe :
              __str_nary_elim (__str_nary_intro nil) ≠ Term.Stuck := by
            simpa [nil, a, r, out, hRevEq] using hOutNe
          have hInterp :=
            eo_interprets_str_nary_elim_intro_eq_of_seq M hM nil T
              (by simpa [nil] using htTy)
              (by simpa [nil, a] using hIntroNN)
              (by simpa [nil, a] using hIntroNe)
              hElimIntroNe
          have hOutToNil : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt out))
              (__smtx_model_eval M (__eo_to_smt nil)) := by
            have hRel :=
              RuleProofs.eo_interprets_eq_rel M
                (__str_nary_elim (__str_nary_intro nil)) nil hInterp
            simpa [nil, a, r, out, hRevEq] using hRel
          have hNilToRev :=
            smt_value_rel_seq_nil_to_str_rev M nil T hNil
              (by simpa [nil] using htTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt out))
            (__smtx_model_eval M (__eo_to_smt nil))
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) nil)))
            hOutToNil hNilToRev
        · subst t
          let head := Term.Apply (Term.UOp UserOp.seq_unit) e
          have hNotConcat : ¬ ∃ x y : Term, head = mkConcat x y := by
            intro hConcat
            rcases hConcat with ⟨x, y, hEq⟩
            change Term.Apply (Term.UOp UserOp.seq_unit) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y at hEq
            injection hEq with hFun _hArg
            cases hFun
          have hRevEq :
              __eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_nary_intro head) =
                __str_nary_intro head :=
            eo_list_rev_str_nary_intro_eq_of_not_str_concat head hNotConcat
              (by simpa [head, a] using hIntroNe)
              (by simpa [head, a, r] using hRevNe)
          have hElimIntroNe :
              __str_nary_elim (__str_nary_intro head) ≠ Term.Stuck := by
            simpa [head, a, r, out, hRevEq] using hOutNe
          have hInterp :=
            eo_interprets_str_nary_elim_intro_eq_of_seq M hM head T
              (by simpa [head] using htTy)
              (by simpa [head, a] using hIntroNN)
              (by simpa [head, a] using hIntroNe)
              hElimIntroNe
          have hOutToHead : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt out))
              (__smtx_model_eval M (__eo_to_smt head)) := by
            have hRel :=
              RuleProofs.eo_interprets_eq_rel M
                (__str_nary_elim (__str_nary_intro head)) head hInterp
            simpa [head, a, r, out, hRevEq] using hRel
          have hHeadToRev :=
            smt_value_rel_seq_unit_to_str_rev M hM e T
              (by simpa [head] using htTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt out))
            (__smtx_model_eval M (__eo_to_smt head))
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) head)))
            hOutToHead hHeadToRev
  | case14 t _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      constructor
      · simp [__seq_eval]
      · simpa [__seq_eval] using
          RuleProofs.smt_value_rel_refl
            (__smtx_model_eval M (__eo_to_smt t))

private theorem seq_eval_smt_value_rel
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hEvalNe : __seq_eval t ≠ Term.Stuck)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
      (__smtx_model_eval M (__eo_to_smt t)) :=
  (seq_eval_smt_type_and_value_rel M hM t hEvalNe hNN).2

public theorem cmd_step_seq_eval_op_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_eval_op args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_eval_op args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_eval_op args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              change __eo_typeof (__eo_prog_seq_eval_op a1) = Term.Bool at hResultTy
              change __eo_prog_seq_eval_op a1 ≠ Term.Stuck at hProg
              cases a1 with
              | Apply f u =>
                  cases f with
                  | Apply eqop t =>
                      cases eqop with
                      | UOp op =>
                          cases op with
                          | eq =>
                              obtain ⟨hReqEq, hProgEq⟩ := seq_eval_op_shape hProg
                              have hArgTrans :
                                  RuleProofs.eo_has_smt_translation
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) := by
                                simpa [RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans.1
                              have hBodyTy :
                                  __eo_typeof
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) =
                                    Term.Bool := by
                                rw [← hProgEq]
                                exact hResultTy
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u) :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type _
                                  hArgTrans hBodyTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                  true
                                rw [hProgEq]
                                subst u
                                exact RuleProofs.eo_interprets_eq_of_rel M t
                                  (__seq_eval t) hEqBool <| by
                                    exact RuleProofs.smt_value_rel_symm
                                      (__smtx_model_eval M (__eo_to_smt (__seq_eval t)))
                                      (__smtx_model_eval M (__eo_to_smt t))
                                      (seq_eval_smt_value_rel M hM t
                                        (by
                                          intro hStuck
                                          rw [hStuck] at hEqBool
                                          rcases
                                            RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                              t Term.Stuck hEqBool with
                                            ⟨hSame, hNN⟩
                                          have hStuckTy :
                                              __smtx_typeof (__eo_to_smt Term.Stuck) =
                                                SmtType.None := by
                                            change __smtx_typeof SmtTerm.None = SmtType.None
                                            exact TranslationProofs.smtx_typeof_none
                                          rw [hStuckTy] at hSame
                                          exact hNN hSame)
                                        ((RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                          t (__seq_eval t) hEqBool).2))
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_seq_eval_op
                                    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) u))
                                rw [hProgEq]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hEqBool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
