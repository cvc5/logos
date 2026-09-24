module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

private abbrev mkNot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) x

private abbrev mkNeg (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y

private abbrev mkSubstr (s i n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) i) n

private abbrev concatCSplitNormalize (rev x : Term) : Term :=
  __eo_ite rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
    (__str_nary_intro x)

private abbrev concatCSplitHead (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatCSplitNormalize rev x)
    (Term.Numeral 0)

private abbrev concatCSplitLenMinusOne (u : Term) : Term :=
  mkNeg (mkStrLen u) (Term.Numeral 1)

private abbrev concatCSplitPrefix (u : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify)
    (mkSubstr u (Term.Numeral 0) (concatCSplitLenMinusOne u))

private abbrev concatCSplitSuffix (u : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify)
    (mkSubstr u (Term.Numeral 1) (concatCSplitLenMinusOne u))

private abbrev concatCSplitFormula (rev u sc : Term) : Term :=
  let pfx := concatCSplitPrefix u
  let suffix := concatCSplitSuffix u
  let scCons := __eo_mk_apply (Term.UOp UserOp.str_concat) sc
  let pfxCons := Term.Apply (Term.UOp UserOp.str_concat) pfx
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) u)
    (__eo_ite rev
      (__eo_mk_apply pfxCons
        (__eo_mk_apply scCons
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx))))
      (__eo_mk_apply scCons
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix)
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sc)))))

private abbrev concatCSplitBody (rev t s u : Term) : Term :=
  let sc := concatCSplitHead rev s
  __eo_requires (concatCSplitHead rev t) u <|
    __eo_requires (__eo_is_eq (__eo_len sc) (Term.Numeral 1))
      (Term.Boolean true) <|
        concatCSplitFormula rev u sc

private theorem native_seq_extract_zero_nat_csplit
    (xs : List SmtValue) (n : Nat) (hle : n <= xs.length) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  unfold native_seq_extract
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : Int) < Int.ofNat n := Int.ofNat_lt.mpr hnPosNat
    have hxsPosNat : 0 < xs.length := Nat.lt_of_lt_of_le hnPosNat hle
    have hxsNe : xs ≠ [] := by
      intro h
      subst xs
      simp at hxsPosNat
    have hmin : min (Int.ofNat n) (Int.ofNat xs.length) = Int.ofNat n :=
      Int.min_eq_left (Int.ofNat_le.mpr hle)
    have hminToNat :
        (min (Int.ofNat n) (Int.ofNat xs.length)).toNat = n := by
      rw [hmin]
      simp
    have hminNat : min n xs.length = n := Nat.min_eq_left hle
    simp [hn, hxsNe]
    change
      min ((min (Int.ofNat n) (Int.ofNat xs.length)).toNat) xs.length =
        min n xs.length
    rw [hminToNat, hminNat]

private theorem native_seq_extract_to_end_nat_csplit
    (xs : List SmtValue) (i : Nat) (hle : i <= xs.length) :
    native_seq_extract xs (Int.ofNat i) (Int.ofNat (xs.length - i)) =
      xs.drop i := by
  unfold native_seq_extract
  by_cases hend : xs.length - i = 0
  · have hLenLe : xs.length <= i := by omega
    have hcast : (Int.ofNat i >= Int.ofNat xs.length) = true := by
      simp [hLenLe]
    simp [hend,List.drop_eq_nil_of_le hLenLe]
  · have htailPosNat : 0 < xs.length - i := Nat.pos_of_ne_zero hend
    have hiltNat : i < xs.length := by omega
    have htailPos : (0 : Int) < Int.ofNat (xs.length - i) :=
      Int.ofNat_lt.mpr htailPosNat
    have hilt : Int.ofNat i < Int.ofNat xs.length :=
      Int.ofNat_lt.mpr hiltNat
    have hcastSub : Int.ofNat (xs.length - i) = Int.ofNat xs.length - Int.ofNat i :=
      Int.ofNat_sub hle
    have hmin :
        min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i) =
          Int.ofNat (xs.length - i) := by
      rw [← hcastSub]
      exact Int.min_eq_left (Int.le_refl _)
    have htake :
        (xs.drop i).take (xs.length - i) = xs.drop i := by
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    have hLenNotLe : ¬ xs.length <= i := Nat.not_le_of_gt hiltNat
    have hiNonneg : ¬ ((i : native_Int) < (0 : native_Int)) := by
      exact Int.not_lt_of_ge (Int.natCast_nonneg i)
    have hminToNat :
        (min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i)).toNat =
          xs.length - i := by
      rw [hmin]
      simp
    simp [hend, hLenNotLe]
    rw [if_neg hiNonneg]
    change
      List.take
          ((min (Int.ofNat (xs.length - i))
              (Int.ofNat xs.length - Int.ofNat i)).toNat)
          (List.drop i xs) =
        List.drop i xs
    rw [hminToNat]
    exact htake

private theorem list_eq_singleton_append_drop_one_of_append_eq
    {α : Type} {xs ys xsTail ysTail : List α}
    (hxs : xs ≠ []) (hysLen : ys.length = 1)
    (h : xs ++ xsTail = ys ++ ysTail) :
    xs = ys ++ xs.drop 1 := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons x xs =>
      cases ys with
      | nil => simp at hysLen
      | cons y ys =>
          cases ys with
          | nil =>
              simp at h
              rw [h.1]
              simp
          | cons _ _ => simp at hysLen

private theorem list_eq_take_init_append_singleton_of_append_eq
    {α : Type} {xs ys xsPrefix ysPrefix : List α}
    (hxs : xs ≠ []) (hysLen : ys.length = 1)
    (h : xsPrefix ++ xs = ysPrefix ++ ys) :
    xs = xs.take (xs.length - 1) ++ ys := by
  have hRev :
      xs.reverse ++ xsPrefix.reverse = ys.reverse ++ ysPrefix.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse h
  have hxsRev : xs.reverse ≠ [] := by
    intro hnil
    exact hxs (by simpa using congrArg List.reverse hnil)
  have hysRevLen : ys.reverse.length = 1 := by
    simpa using hysLen
  have hPrefix := list_eq_singleton_append_drop_one_of_append_eq
    (xs := xs.reverse) (ys := ys.reverse) (xsTail := xsPrefix.reverse)
    (ysTail := ysPrefix.reverse) hxsRev hysRevLen hRev
  have hRevBack := congrArg List.reverse hPrefix
  simpa [List.reverse_append, List.drop_reverse] using hRevBack

private theorem len_nonzero_seq_type_of_bool (u : Term)
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) :
    ∃ T, __smtx_typeof (__eo_to_smt u) = SmtType.Seq T := by
  have hEqBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen u) (Term.Numeral 0)) :=
    RuleProofs.eo_has_bool_type_not_arg
      (mkEq (mkStrLen u) (Term.Numeral 0)) hNonzeroBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen u) (Term.Numeral 0) hEqBool with
    ⟨_hSame, hLeftNN⟩
  have hLenTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt u)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen, __eo_to_smt, __smtx_typeof] using hLeftNN
  exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
    (typeof_str_len_eq (__eo_to_smt u)) hLenTerm

private theorem sc_string_length_one_of_seq_type
    (sc : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hReq : __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true) :
    ∃ str, sc = Term.String str ∧ str.length = 1 := by
  cases sc <;>
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hReq ⊢
  case String str =>
    have hInt : (str.length : Int) = 1 := by
      simpa [native_str_len] using hReq.symm
    exact_mod_cast hInt
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hTy
    rw [__smtx_typeof.eq_5] at hTy
    cases hCond :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hCond] at hTy

private theorem sc_eval_length_one_of_seq_type
    (M : SmtModel) (sc : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hReq : __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true) :
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss ∧
      (native_unpack_seq ss).length = 1 := by
  rcases sc_string_length_one_of_seq_type sc T hTy hReq with
    ⟨str, rfl, hLen⟩
  refine ⟨native_pack_string str, ?_, ?_⟩
  · change __smtx_model_eval M (SmtTerm.String str) =
      SmtValue.Seq (native_pack_string str)
    rw [__smtx_model_eval.eq_4]
  · simp [native_pack_string, _root_.native_unpack_pack_seq, hLen]

private theorem length_ne_zero_of_not_len_eq_eval
    (M : SmtModel) (u : Term) (su : SmtSeq)
    (huEval : __smtx_model_eval M (__eo_to_smt u) = SmtValue.Seq su)
    (hLenNe :
      eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true) :
    (native_unpack_seq su).length ≠ 0 := by
  have hEqFalse :
      eo_interprets M (mkEq (mkStrLen u) (Term.Numeral 0)) false :=
    RuleProofs.eo_interprets_not_true_implies_false M
      (mkEq (mkStrLen u) (Term.Numeral 0)) hLenNe
  have hEval :
      __smtx_model_eval M (__eo_to_smt (mkEq (mkStrLen u) (Term.Numeral 0))) =
        SmtValue.Boolean false := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (mkEq (mkStrLen u) (Term.Numeral 0)) false).mp hEqFalse with
    | intro_false _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt u)) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean false at hEval
  rw [smtx_eval_eq_term_eq] at hEval
  rw [smtx_eval_str_len_term_eq] at hEval
  simp [huEval, __smtx_model_eval_str_len, __smtx_model_eval_eq,
    __smtx_model_eval, native_seq_len, native_veq] at hEval
  intro hLen
  apply hEval
  exact List.eq_nil_of_length_eq_zero hLen

private theorem eo_prog_concat_csplit_eq_of_ne_stuck
    (rev t s u : Term)
    (hProg :
      __eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) =
      concatCSplitFormula rev u (concatCSplitHead rev s) ∧
      concatCSplitHead rev t = u ∧
      __eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1) =
        Term.Boolean true := by
  have hProgBody :
      __eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) =
        concatCSplitBody rev t s u := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals
      simp [__eo_prog_concat_csplit, concatCSplitBody, concatCSplitFormula,
        concatCSplitHead, concatCSplitNormalize, concatCSplitPrefix,
        concatCSplitSuffix, concatCSplitLenMinusOne, mkEq, mkNot, mkStrLen,
        mkNeg, mkSubstr]
  have hBodyNe : concatCSplitBody rev t s u ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadT :
      concatCSplitHead rev t = u :=
    eo_requires_eq_of_ne_stuck (concatCSplitHead rev t) u
      (__eo_requires
        (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
        (Term.Boolean true)
        (concatCSplitFormula rev u (concatCSplitHead rev s))) hBodyNe
  have hInnerNe :
      __eo_requires
          (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
          (Term.Boolean true)
          (concatCSplitFormula rev u (concatCSplitHead rev s)) ≠
        Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (concatCSplitHead rev t) u
      _ hBodyNe
  have hLenReq :
      __eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1) =
        Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
      (Term.Boolean true) _ hInnerNe
  have hOuterEq :
      concatCSplitBody rev t s u =
        __eo_requires
          (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
          (Term.Boolean true)
          (concatCSplitFormula rev u (concatCSplitHead rev s)) :=
    eo_requires_eq_result_of_ne_stuck (concatCSplitHead rev t) u
      (__eo_requires
        (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
        (Term.Boolean true)
        (concatCSplitFormula rev u (concatCSplitHead rev s))) hBodyNe
  have hInnerEq :
      __eo_requires
          (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
          (Term.Boolean true)
          (concatCSplitFormula rev u (concatCSplitHead rev s)) =
        concatCSplitFormula rev u (concatCSplitHead rev s) :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_eq (__eo_len (concatCSplitHead rev s)) (Term.Numeral 1))
      (Term.Boolean true) (concatCSplitFormula rev u (concatCSplitHead rev s))
      hInnerNe
  exact ⟨by rw [hProgBody, hOuterEq, hInnerEq], hHeadT, hLenReq⟩

private theorem eo_prog_concat_csplit_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_csplit rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s u,
      x1 = mkEq t s ∧ x2 = mkNot (mkEq (mkStrLen u) (Term.Numeral 0)) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 t =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply notOp eqTerm =>
                      cases notOp with
                      | UOp notU =>
                          cases notU with
                          | not =>
                              cases eqTerm with
                              | Apply lhs2 zero =>
                                  cases lhs2 with
                                  | Apply op2 lenTerm =>
                                      cases op2 with
                                      | UOp eqU =>
                                          cases eqU with
                                          | eq =>
                                              cases lenTerm with
                                              | Apply lenOp u =>
                                                  cases lenOp with
                                                  | UOp lenU =>
                                                      cases lenU with
                                                      | str_len =>
                                                          cases zero with
                                                          | Numeral z =>
                                                              by_cases hz : z = 0
                                                              · subst z
                                                                exact
                                                                  ⟨t, rhs1, u,
                                                                    rfl, rfl⟩
                                                              · cases rev <;>
                                                                  simp [__eo_prog_concat_csplit, hz]
                                                                    at hProg
                                                          | _ =>
                                                              cases rev <;>
                                                                simp [__eo_prog_concat_csplit]
                                                                  at hProg
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_csplit]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_csplit]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_csplit]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_csplit] at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_csplit] at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_csplit] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_csplit] at hProg
                          | _ =>
                              cases rev <;>
                                simp [__eo_prog_concat_csplit] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_csplit] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_csplit] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_csplit] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_csplit] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_csplit] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_csplit] at hProg

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

private theorem concatCSplitNormalize_ne_stuck_of_head_ne_stuck
    (rev x : Term)
    (hHead : concatCSplitHead rev x ≠ Term.Stuck) :
    concatCSplitNormalize rev x ≠ Term.Stuck :=
  eo_list_nth_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.str_concat) (concatCSplitNormalize rev x)
    (Term.Numeral 0) hHead

private theorem concatCSplit_rev_cases_of_prog_ne_stuck
    (rev t s u : Term)
    (hProg :
      __eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (huNe : u ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck rev t s u hProg with
    ⟨_, hHeadT, _⟩
  have hHeadNe : concatCSplitHead rev t ≠ Term.Stuck := by
    rw [hHeadT]
    exact huNe
  have hNormNe : concatCSplitNormalize rev t ≠ Term.Stuck :=
    concatCSplitNormalize_ne_stuck_of_head_ne_stuck rev t hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (__str_nary_intro t) ≠ Term.Stuck := by
    simpa [concatCSplitNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
    (__str_nary_intro t) hIteNe

private theorem smtx_typeof_str_len_seq
    (s : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_len s) = SmtType.Int := by
  rw [typeof_str_len_eq]
  simp [hs, __smtx_typeof_seq_op_1_ret]

private theorem smtx_typeof_str_substr_seq
    (s i n : SmtTerm) (T : SmtType)
    (hs : __smtx_typeof s = SmtType.Seq T)
    (hi : __smtx_typeof i = SmtType.Int)
    (hn : __smtx_typeof n = SmtType.Int) :
    __smtx_typeof (SmtTerm.str_substr s i n) = SmtType.Seq T := by
  rw [typeof_str_substr_eq]
  simp [__smtx_typeof_str_substr, hs, hi, hn]

private theorem smtx_typeof_str_concat_seq
    (x y : SmtTerm) (T : SmtType)
    (hx : __smtx_typeof x = SmtType.Seq T)
    (hy : __smtx_typeof y = SmtType.Seq T) :
    __smtx_typeof (SmtTerm.str_concat x y) = SmtType.Seq T := by
  rw [typeof_str_concat_eq]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hx, hy]

private theorem smtx_typeof_neg_int
    (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.neg x y) = SmtType.Int := by
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hx, hy]

private theorem smt_typeof_nil_str_concat_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem eval_nil_str_concat_typeof_of_smt_type_seq
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact eval_seq_empty_typeof M x T hxTy

private theorem eo_has_bool_type_eq_of_seq_type
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq x y) := by
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hxTy, hyTy]
  · rw [hxTy]
    exact seq_ne_none T

private theorem smt_typeof_mkConcat_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  simpa [mkConcat] using
    smtx_typeof_str_concat_seq (__eo_to_smt x) (__eo_to_smt y) T hxTy hyTy

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
    smt_typeof_mkConcat_seq head nil T hHeadTy hNilTy
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
    exact smt_typeof_mkConcat_seq nil head T hNilTy hHeadTy
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

private theorem concat_csplit_append_eq_of_concat_eq
    (M : SmtModel) (hM : model_wf M)
    (x xtail y ytail : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxtailTy : __smtx_typeof (__eo_to_smt xtail) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hytailTy : __smtx_typeof (__eo_to_smt ytail) = SmtType.Seq T)
    (hEq : eo_interprets M (mkEq (mkConcat x xtail) (mkConcat y ytail)) true) :
    ∃ sx sxtail sy sytail : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt xtail) = SmtValue.Seq sxtail ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      __smtx_model_eval M (__eo_to_smt ytail) = SmtValue.Seq sytail ∧
      native_unpack_seq sx ++ native_unpack_seq sxtail =
        native_unpack_seq sy ++ native_unpack_seq sytail := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxtailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xtail)
    (SmtType.Seq T) hxtailTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hytailValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ytail)
    (SmtType.Seq T) hytailTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxtailValTy with ⟨sxtail, hxtailEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hytailValTy with ⟨sytail, hytailEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat x xtail) (mkConcat y ytail) hEq
  unfold RuleProofs.smt_value_rel at hRel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxEval, hxtailEval, hyEval, hytailEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxtail)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sytail))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxtail))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sytail)) at hRel
  have hPackEq :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hRel
  have hListEq := congrArg native_unpack_seq hPackEq
  exact
    ⟨sx, sxtail, sy, sytail, hxEval, hxtailEval, hyEval, hytailEval,
      by simpa [_root_.native_unpack_pack_seq] using hListEq⟩

private theorem eval_mkConcat_right_nested
    (M : SmtModel) (a b c : Term) (T : SmtType)
    (sa sb sc : SmtSeq)
    (haEval : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Seq sa)
    (hbEval : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Seq sb)
    (hcEval : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq sc)
    (haElem : __smtx_elem_typeof_seq_value sa = T) :
    __smtx_model_eval M (__eo_to_smt (mkConcat a (mkConcat b c))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_unpack_seq sa ++ native_unpack_seq sb ++ native_unpack_seq sc)) := by
  rw [smtx_model_eval_str_concat_term_eq M a (mkConcat b c)]
  rw [smtx_model_eval_str_concat_term_eq M b c]
  rw [haEval, hbEval, hcEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    _root_.native_unpack_pack_seq, haElem, List.append_assoc]

private theorem smt_typeof_concatCSplitLenMinusOne
    (u : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (concatCSplitLenMinusOne u)) = SmtType.Int := by
  change
    __smtx_typeof
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt u)) (SmtTerm.Numeral 1)) =
      SmtType.Int
  exact smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt u))
    (SmtTerm.Numeral 1)
    (smtx_typeof_str_len_seq (__eo_to_smt u) T huTy)
    (by simp [__smtx_typeof])

private theorem smt_typeof_concatCSplitPrefix
    (u : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (concatCSplitPrefix u)) = SmtType.Seq T := by
  have hLen := smt_typeof_concatCSplitLenMinusOne u T huTy
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt u) (SmtTerm.Numeral 0)
            (__eo_to_smt (concatCSplitLenMinusOne u)))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt u) (SmtTerm.Numeral 0)
      (__eo_to_smt (concatCSplitLenMinusOne u)) T huTy
      (by simp [__smtx_typeof]) hLen

private theorem smt_typeof_concatCSplitSuffix
    (u : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (concatCSplitSuffix u)) = SmtType.Seq T := by
  have hLen := smt_typeof_concatCSplitLenMinusOne u T huTy
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt u) (SmtTerm.Numeral 1)
            (__eo_to_smt (concatCSplitLenMinusOne u)))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using
    smtx_typeof_str_substr_seq (__eo_to_smt u) (SmtTerm.Numeral 1)
      (__eo_to_smt (concatCSplitLenMinusOne u)) T huTy
      (by simp [__smtx_typeof]) hLen

private theorem csplit_context_false
    (M : SmtModel) (hM : model_wf M)
    (t s u : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_csplit (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tTail sTail,
      sc = concatCSplitHead (Term.Boolean false) s ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true ∧
      eo_interprets M (mkEq (mkConcat u tTail) (mkConcat sc sTail)) true := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck
      (Term.Boolean false) t s u hProg with
    ⟨_, hHeadT, hScLenHead⟩
  rcases len_nonzero_seq_type_of_bool u hNonzeroBool with ⟨T, huTy⟩
  let sc := concatCSplitHead (Term.Boolean false) s
  have hScLen :
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true := by
    simpa [sc] using hScLenHead
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck := by
    intro h
    have hBad := hScLen
    rw [h] at hBad
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hBad
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = u := by
    simpa [concatCSplitHead, concatCSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCSplitHead, concatCSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact huNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) u
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t u tTail T
      hIntroT huTy hTNN with
    ⟨htTy, htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroS]
    simp
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hIntroSTy
    rw [hIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hIntroSConsTy with
    ⟨hscTy, hsTailTy⟩
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck := by
    rw [hIntroT]
    simp
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T := by
    rw [hIntroT]
    exact smt_typeof_mkConcat_seq u tTail T huTy htTailTy
  have hIntroBool :
      RuleProofs.eo_has_bool_type
        (mkEq (__str_nary_intro t) (__str_nary_intro s)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroTTy, hIntroSTy]
    · rw [hIntroTTy]
      exact seq_ne_none T
  have hIntroEq :
      eo_interprets M (mkEq (__str_nary_intro t) (__str_nary_intro s)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM t s T htTy hsTy
      hIntroTNe hIntroSNe hST hIntroBool
  have hConcatEq :
      eo_interprets M (mkEq (mkConcat u tTail) (mkConcat sc sTail)) true := by
    simpa [hIntroT, hIntroS] using hIntroEq
  exact ⟨T, sc, tTail, sTail, rfl, huTy, hscTy, htTailTy, hsTailTy,
    hScLen, hConcatEq⟩

private theorem csplit_context_true
    (M : SmtModel) (hM : model_wf M)
    (t s u : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_csplit (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tPrefix sPrefix,
      sc = concatCSplitHead (Term.Boolean true) s ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T ∧
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true ∧
      eo_interprets M (mkEq (mkConcat tPrefix u) (mkConcat sPrefix sc)) true := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck
      (Term.Boolean true) t s u hProg with
    ⟨_, hHeadT, hScLenHead⟩
  rcases len_nonzero_seq_type_of_bool u hNonzeroBool with ⟨T, huTy⟩
  let sc := concatCSplitHead (Term.Boolean true) s
  have hScLen :
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true := by
    simpa [sc] using hScLenHead
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck := by
    intro h
    have hBad := hScLen
    rw [h] at hBad
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hBad
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = u := by
    simpa [concatCSplitHead, concatCSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCSplitHead, concatCSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact huNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      u hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t u tTail T
      hRevIntroT huTy hTNN with
    ⟨htTy, htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hRevIntroTNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck := by
    rw [hRevIntroT]
    simp
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntroTNe
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt t) T htTy with
    ⟨hTInh, hTWf⟩
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf t T htTy hTInh hTWf
      hIntroTNe
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  have hRevIntroSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevIntroSNe
  have hRevIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hRevIntroSTy
    rw [hRevIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hRevIntroSConsTy with
    ⟨hscTy, hsTailTy⟩
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroTNe
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroSNe
  have hDoubleT :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroTNe hRevIntroTNe
  have hDoubleS :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroSNe hRevIntroSNe
  have hDoubleEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))) true :=
    eo_interprets_double_rev_intros_of_elim_intros M hM t s T htTy hsTy
      hIntroTNN hIntroSNN hIntroTNe hIntroSNe hElimIntroT
      hElimIntroS hDoubleT hDoubleS hST
  have hRevConcatEq :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat u tTail)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true := by
    simpa [hRevIntroT, hRevIntroS] using hDoubleEq
  have hConsTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat u tTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      u tTail (by decide) hTTailList
  have hConsSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat sc sTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      sc sTail (by decide) hSTailList
  have hConsTTy :
      __smtx_typeof (__eo_to_smt (mkConcat u tTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq u tTail T huTy htTailTy
  have hConsSTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc sTail T hscTy hsTailTy
  have hRevConsT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u tTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat u tTail) hConsTList
  have hRevConsS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat sc sTail) hConsSList
  have hElimConsT :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat u tTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq u tTail T
      hConsTTy hRevConsT
  have hElimConsS :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat sc sTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq sc sTail T
      hConsSTy hRevConsS
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM u tTail T
      huTy hTTailList htTailTy hRevConsT hElimConsT with
    ⟨tPrefix, htPrefixTy, hSnocT⟩
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM sc sTail T
      hscTy hSTailList hsTailTy hRevConsS hElimConsS with
    ⟨sPrefix, hsPrefixTy, hSnocS⟩
  have hSnocTSymm :
      eo_interprets M
        (mkEq (mkConcat tPrefix u)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat u tTail)))) true :=
    eo_interprets_eq_symm_local M
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u tTail)))
      (mkConcat tPrefix u) hSnocT
  have hLeftToRight :
      eo_interprets M
        (mkEq (mkConcat tPrefix u)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix u)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u tTail)))
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      hSnocTSymm hRevConcatEq
  have hSnocEq :
      eo_interprets M (mkEq (mkConcat tPrefix u) (mkConcat sPrefix sc)) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix u)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      (mkConcat sPrefix sc) hLeftToRight hSnocS
  exact ⟨T, sc, tPrefix, sPrefix, rfl, huTy, hscTy, htPrefixTy,
    hsPrefixTy, hScLen, hSnocEq⟩

private theorem concat_csplit_false_facts
    (M : SmtModel) (hM : model_wf M)
    (u sc tTail sTail : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hScLen : __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat u tTail) (mkConcat sc sTail)) true) :
    eo_interprets M
      (concatCSplitFormula (Term.Boolean false) u sc) true := by
  let suffix := concatCSplitSuffix u
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sc)
  let rhs := mkConcat sc (mkConcat suffix nil)
  have hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
    simpa [suffix] using smt_typeof_concatCSplitSuffix u T huTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq
      sc T hscTy
  have hRhsTailTy :
      __smtx_typeof (__eo_to_smt (mkConcat suffix nil)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq suffix nil T hSuffixTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq sc (mkConcat suffix nil) T
      hscTy hRhsTailTy
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hSuffixNe : suffix ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation suffix
      (by unfold RuleProofs.eo_has_smt_translation; rw [hSuffixTy]; exact seq_ne_none T)
  have hNilNe : nil ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nil
      (by unfold RuleProofs.eo_has_smt_translation; rw [hNilTy]; exact seq_ne_none T)
  have hFormulaEq : concatCSplitFormula (Term.Boolean false) u sc = mkEq u rhs := by
    simp [concatCSplitFormula, suffix, nil, rhs, mkEq, mkConcat, __eo_mk_apply,
      eo_ite_false]
  have hFormulaBool :
      RuleProofs.eo_has_bool_type (concatCSplitFormula (Term.Boolean false) u sc) := by
    rw [hFormulaEq]
    exact eo_has_bool_type_eq_of_seq_type u rhs T huTy hRhsTy
  rw [hFormulaEq] at hFormulaBool ⊢
  rcases concat_csplit_append_eq_of_concat_eq M hM u tTail sc sTail T
      huTy htTailTy hscTy hsTailTy hConcatEq with
    ⟨su, _suTail, ssc, _ssTail, huEval, _htTailEval, hscEval, _hsTailEval,
      hAppend⟩
  let xs := native_unpack_seq su
  let ys := native_unpack_seq ssc
  have hscLen : ys.length = 1 := by
    rcases sc_eval_length_one_of_seq_type M sc T hscTy hScLen with
      ⟨ssc0, hscEval0, hLen0⟩
    rw [hscEval] at hscEval0
    injection hscEval0 with hSeq
    cases hSeq
    simpa [ys] using hLen0
  have hUNonempty : xs.length ≠ 0 := by
    simpa [xs] using length_ne_zero_of_not_len_eq_eval M u su huEval hNonzero
  have hxsNe : xs ≠ [] := by
    intro h
    exact hUNonempty (by simp [xs, h])
  have hList : xs = ys ++ xs.drop 1 :=
    list_eq_singleton_append_drop_one_of_append_eq
      (xs := xs) (ys := ys) (xsTail := native_unpack_seq _suTail)
      (ysTail := native_unpack_seq _ssTail) hxsNe hscLen (by
        simpa [xs, ys] using hAppend)
  have huValTy := smt_model_eval_preserves_type M hM (__eo_to_smt u)
    (SmtType.Seq T) huTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hsuTy : __smtx_typeof_seq_value su = SmtType.Seq T := by
    simpa [huEval, __smtx_typeof_value] using huValTy
  have hsscTy : __smtx_typeof_seq_value ssc = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hsuElem : __smtx_elem_typeof_seq_value su = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsuTy
  have hsscElem : __smtx_elem_typeof_seq_value ssc = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsscTy
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M sc T hscTy
  have hOneLe : 1 <= xs.length := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hUNonempty)
  have hDiff : Int.ofNat (xs.length - 1) = Int.ofNat xs.length - (1 : Int) :=
    Int.ofNat_sub hOneLe
  have hExtract :
      native_seq_extract xs (Int.ofNat 1) (Int.ofNat xs.length + (-1 : Int)) =
        xs.drop 1 := by
    have h := native_seq_extract_to_end_nat_csplit xs 1 hOneLe
    rw [hDiff] at h
    simpa [Int.sub_eq_add_neg] using h
  have hExtractPacked :
      native_pack_seq T
          (native_seq_extract (native_unpack_seq su) (1 : Int)
            (Int.ofNat (native_unpack_seq su).length + (-1 : Int))) =
        native_pack_seq T (native_unpack_seq su).tail := by
    simpa [xs, List.drop] using congrArg (native_pack_seq T) hExtract
  have hSuffixEval :
      __smtx_model_eval M (__eo_to_smt suffix) =
        SmtValue.Seq (native_pack_seq T (xs.drop 1)) := by
    change
      __smtx_model_eval M
          (SmtTerm._at_purify
            (SmtTerm.str_substr (__eo_to_smt u) (SmtTerm.Numeral 1)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt u))
                (SmtTerm.Numeral 1)))) =
        SmtValue.Seq (native_pack_seq T (xs.drop 1))
    simp [xs, huEval, __smtx_model_eval,
      __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
      __smtx_model_eval__at_purify, __smtx_model_eval__, native_seq_len,
      native_zplus, native_zneg,hsuElem]
    exact hExtractPacked
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T xs) := by
    have hNested := eval_mkConcat_right_nested M sc suffix nil T ssc
      (native_pack_seq T (xs.drop 1)) (SmtSeq.empty T) hscEval
      hSuffixEval hNilEval hsscElem
    calc
      __smtx_model_eval M (__eo_to_smt rhs) =
          SmtValue.Seq
            (native_pack_seq T
              (native_unpack_seq ssc ++
                native_unpack_seq (native_pack_seq T (xs.drop 1)) ++
                native_unpack_seq (SmtSeq.empty T))) := by
        simpa only [rhs] using hNested
      _ = SmtValue.Seq (native_pack_seq T xs) := by
        rw [_root_.native_unpack_pack_seq]
        change SmtValue.Seq (native_pack_seq T (ys ++ xs.drop 1 ++ [])) =
          SmtValue.Seq (native_pack_seq T xs)
        rw [List.append_nil, ← hList]
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt u))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    unfold RuleProofs.smt_value_rel
    rw [huEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T su hsuElem
  exact RuleProofs.eo_interprets_eq_of_rel M u rhs hFormulaBool hEqRel

private theorem concat_csplit_true_facts
    (M : SmtModel) (hM : model_wf M)
    (u sc tPrefix sPrefix : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hScLen : __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tPrefix u) (mkConcat sPrefix sc)) true) :
    eo_interprets M
      (concatCSplitFormula (Term.Boolean true) u sc) true := by
  let pfx := concatCSplitPrefix u
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
  let rhs := mkConcat pfx (mkConcat sc nil)
  have hpfxTy :
      __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [pfx] using smt_typeof_concatCSplitPrefix u T huTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq
      pfx T hpfxTy
  have hRhsTailTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc nil)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc nil T hscTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq pfx (mkConcat sc nil) T
      hpfxTy hRhsTailTy
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  have hpfxNe : pfx ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation pfx
      (by unfold RuleProofs.eo_has_smt_translation; rw [hpfxTy]; exact seq_ne_none T)
  have hNilNe : nil ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nil
      (by unfold RuleProofs.eo_has_smt_translation; rw [hNilTy]; exact seq_ne_none T)
  have hFormulaEq : concatCSplitFormula (Term.Boolean true) u sc = mkEq u rhs := by
    simp [concatCSplitFormula, pfx, nil, rhs, mkEq, mkConcat, __eo_mk_apply,
      eo_ite_true]
  have hFormulaBool :
      RuleProofs.eo_has_bool_type (concatCSplitFormula (Term.Boolean true) u sc) := by
    rw [hFormulaEq]
    exact eo_has_bool_type_eq_of_seq_type u rhs T huTy hRhsTy
  rw [hFormulaEq] at hFormulaBool ⊢
  rcases concat_csplit_append_eq_of_concat_eq M hM tPrefix u sPrefix sc T
      htPrefixTy huTy hsPrefixTy hscTy hConcatEq with
    ⟨stPrefix, su, ssPrefix, ssc, htPrefixEval, huEval, _hsPrefixEval,
      hscEval, hAppend⟩
  let xs := native_unpack_seq su
  let ys := native_unpack_seq ssc
  have hscLen : ys.length = 1 := by
    rcases sc_eval_length_one_of_seq_type M sc T hscTy hScLen with
      ⟨ssc0, hscEval0, hLen0⟩
    rw [hscEval] at hscEval0
    injection hscEval0 with hSeq
    cases hSeq
    simpa [ys] using hLen0
  have hUNonempty : xs.length ≠ 0 := by
    simpa [xs] using length_ne_zero_of_not_len_eq_eval M u su huEval hNonzero
  have hxsNe : xs ≠ [] := by
    intro h
    exact hUNonempty (by simp [xs, h])
  have hList : xs = xs.take (xs.length - 1) ++ ys :=
    list_eq_take_init_append_singleton_of_append_eq
      (xs := xs) (ys := ys) (xsPrefix := native_unpack_seq stPrefix)
      (ysPrefix := native_unpack_seq ssPrefix) hxsNe hscLen (by
        simpa [xs, ys] using hAppend)
  have huValTy := smt_model_eval_preserves_type M hM (__eo_to_smt u)
    (SmtType.Seq T) huTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hsuTy : __smtx_typeof_seq_value su = SmtType.Seq T := by
    simpa [huEval, __smtx_typeof_value] using huValTy
  have hsscTy : __smtx_typeof_seq_value ssc = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hsuElem : __smtx_elem_typeof_seq_value su = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsuTy
  have hsscElem : __smtx_elem_typeof_seq_value ssc = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsscTy
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M pfx T hpfxTy
  have hOneLe : 1 <= xs.length := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hUNonempty)
  have hTakeLe : xs.length - 1 <= xs.length := Nat.sub_le _ _
  have hDiff : Int.ofNat (xs.length - 1) = Int.ofNat xs.length - (1 : Int) :=
    Int.ofNat_sub hOneLe
  have hExtract :
      native_seq_extract xs 0 (Int.ofNat xs.length + (-1 : Int)) =
        xs.take (xs.length - 1) := by
    have h := native_seq_extract_zero_nat_csplit xs (xs.length - 1) hTakeLe
    rw [hDiff] at h
    simpa [Int.sub_eq_add_neg] using h
  have hExtractPacked :
      native_pack_seq T
          (native_seq_extract (native_unpack_seq su) (0 : Int)
            (Int.ofNat (native_unpack_seq su).length + (-1 : Int))) =
        native_pack_seq T
          (List.take ((native_unpack_seq su).length - 1) (native_unpack_seq su)) := by
    simpa [xs] using congrArg (native_pack_seq T) hExtract
  have hpfxEval :
      __smtx_model_eval M (__eo_to_smt pfx) =
        SmtValue.Seq (native_pack_seq T (xs.take (xs.length - 1))) := by
    change
      __smtx_model_eval M
          (SmtTerm._at_purify
            (SmtTerm.str_substr (__eo_to_smt u) (SmtTerm.Numeral 0)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt u))
                (SmtTerm.Numeral 1)))) =
        SmtValue.Seq (native_pack_seq T (xs.take (xs.length - 1)))
    simp [xs, huEval, __smtx_model_eval,
      __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
      __smtx_model_eval__at_purify, __smtx_model_eval__, native_seq_len,
      native_zplus, native_zneg,hsuElem]
    exact hExtractPacked
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T xs) := by
    have hNested := eval_mkConcat_right_nested M pfx sc nil T
      (native_pack_seq T (xs.take (xs.length - 1))) ssc (SmtSeq.empty T)
      hpfxEval hscEval hNilEval (elem_typeof_pack_seq T _)
    calc
      __smtx_model_eval M (__eo_to_smt rhs) =
          SmtValue.Seq
            (native_pack_seq T
              (native_unpack_seq (native_pack_seq T (xs.take (xs.length - 1))) ++
                native_unpack_seq ssc ++ native_unpack_seq (SmtSeq.empty T))) := by
        simpa only [rhs] using hNested
      _ = SmtValue.Seq (native_pack_seq T xs) := by
        rw [_root_.native_unpack_pack_seq]
        change SmtValue.Seq
            (native_pack_seq T (xs.take (xs.length - 1) ++ ys ++ [])) =
          SmtValue.Seq (native_pack_seq T xs)
        rw [List.append_nil, ← hList]
  have hEqRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt u))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    unfold RuleProofs.smt_value_rel
    rw [huEval, hRhsEval]
    exact smt_seq_rel_pack_unpack T su hsuElem
  exact RuleProofs.eo_interprets_eq_of_rel M u rhs hFormulaBool hEqRel

private theorem concat_csplit_formula_has_bool_type
    (rev u sc : Term) (T : SmtType)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hRev : rev = Term.Boolean true ∨ rev = Term.Boolean false) :
    RuleProofs.eo_has_bool_type (concatCSplitFormula rev u sc) := by
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sc
      (by unfold RuleProofs.eo_has_smt_translation; rw [hscTy]; exact seq_ne_none T)
  rcases hRev with hRev | hRev
  · subst rev
    let pfx := concatCSplitPrefix u
    let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
    let rhs := mkConcat pfx (mkConcat sc nil)
    have hpfxTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
      simpa [pfx] using smt_typeof_concatCSplitPrefix u T huTy
    have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
      simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq
        pfx T hpfxTy
    have hScNilTy :
        __smtx_typeof (__eo_to_smt (mkConcat sc nil)) = SmtType.Seq T :=
      smt_typeof_mkConcat_seq sc nil T hscTy hNilTy
    have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
      simpa [rhs] using smt_typeof_mkConcat_seq pfx (mkConcat sc nil) T
        hpfxTy hScNilTy
    have hpfxNe : pfx ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation pfx
        (by unfold RuleProofs.eo_has_smt_translation; rw [hpfxTy]; exact seq_ne_none T)
    have hNilNe : nil ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation nil
        (by unfold RuleProofs.eo_has_smt_translation; rw [hNilTy]; exact seq_ne_none T)
    have hFormulaEq : concatCSplitFormula (Term.Boolean true) u sc = mkEq u rhs := by
      simp [concatCSplitFormula, pfx, nil, rhs, mkEq, mkConcat, __eo_mk_apply,
        eo_ite_true]
    rw [hFormulaEq]
    exact eo_has_bool_type_eq_of_seq_type u rhs T huTy hRhsTy
  · subst rev
    let suffix := concatCSplitSuffix u
    let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sc)
    let rhs := mkConcat sc (mkConcat suffix nil)
    have hSuffixTy : __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T := by
      simpa [suffix] using smt_typeof_concatCSplitSuffix u T huTy
    have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
      simpa [nil] using smt_typeof_nil_str_concat_typeof_of_smt_type_seq
        sc T hscTy
    have hSuffixNilTy :
        __smtx_typeof (__eo_to_smt (mkConcat suffix nil)) = SmtType.Seq T :=
      smt_typeof_mkConcat_seq suffix nil T hSuffixTy hNilTy
    have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
      simpa [rhs] using smt_typeof_mkConcat_seq sc (mkConcat suffix nil) T
        hscTy hSuffixNilTy
    have hSuffixNe : suffix ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation suffix
        (by unfold RuleProofs.eo_has_smt_translation; rw [hSuffixTy]; exact seq_ne_none T)
    have hNilNe : nil ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation nil
        (by unfold RuleProofs.eo_has_smt_translation; rw [hNilTy]; exact seq_ne_none T)
    have hFormulaEq : concatCSplitFormula (Term.Boolean false) u sc = mkEq u rhs := by
      simp [concatCSplitFormula, suffix, nil, rhs, mkEq, mkConcat, __eo_mk_apply,
        eo_ite_false]
    rw [hFormulaEq]
    exact eo_has_bool_type_eq_of_seq_type u rhs T huTy hRhsTy

private theorem csplit_context_false_head_type
    (t s u : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_csplit (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (concatCSplitHead (Term.Boolean false) s)) =
        SmtType.Seq T := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck
      (Term.Boolean false) t s u hProg with
    ⟨_, hHeadT, hScLenHead⟩
  rcases len_nonzero_seq_type_of_bool u hNonzeroBool with ⟨T, huTy⟩
  let sc := concatCSplitHead (Term.Boolean false) s
  have hScLen :
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true := by
    simpa [sc] using hScLenHead
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck := by
    intro h
    have hBad := hScLen
    rw [h] at hBad
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hBad
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = u := by
    simpa [concatCSplitHead, concatCSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCSplitHead, concatCSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact huNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) u
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t u tTail T
      hIntroT huTy hTNN with
    ⟨htTy, htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroS]
    simp
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hIntroSTy
    rw [hIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hIntroSConsTy with
    ⟨hscTy, _hsTailTy⟩
  exact ⟨T, huTy, by simpa [sc] using hscTy⟩

private theorem csplit_context_true_head_type
    (t s u : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_csplit (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt u) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (concatCSplitHead (Term.Boolean true) s)) =
        SmtType.Seq T := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck
      (Term.Boolean true) t s u hProg with
    ⟨_, hHeadT, hScLenHead⟩
  rcases len_nonzero_seq_type_of_bool u hNonzeroBool with ⟨T, huTy⟩
  let sc := concatCSplitHead (Term.Boolean true) s
  have hScLen :
      __eo_is_eq (__eo_len sc) (Term.Numeral 1) = Term.Boolean true := by
    simpa [sc] using hScLenHead
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by unfold RuleProofs.eo_has_smt_translation; rw [huTy]; exact seq_ne_none T)
  have hscNe : sc ≠ Term.Stuck := by
    intro h
    have hBad := hScLen
    rw [h] at hBad
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hBad
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = u := by
    simpa [concatCSplitHead, concatCSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCSplitHead, concatCSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact huNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      u hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t u tTail T
      hRevIntroT huTy hTNN with
    ⟨htTy, _htTailTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [← hTSSameTy]
    exact htTy
  have hRevIntroSNe :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck := by
    rw [hRevIntroS]
    simp
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt s) T hsTy with
    ⟨hTInh, hTWf⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroSNe
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroSNe
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntroSNe
  have hRevIntroSTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevIntroSNe
  have hRevIntroSConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T := by
    have h := hRevIntroSTy
    rw [hRevIntroS] at h
    simpa [mkConcat] using h
  rcases str_concat_args_of_seq_type sc sTail T hRevIntroSConsTy with
    ⟨hscTy, _hsTailTy⟩
  exact ⟨T, huTy, by simpa [sc] using hscTy⟩

private theorem step_concat_csplit_core
    (M : SmtModel) (hM : model_wf M)
    (rev t s u : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))))) =
        Term.Bool) :
    StepRuleProperties M [mkEq t s, mkNot (mkEq (mkStrLen u) (Term.Numeral 0))]
      (__eo_prog_concat_csplit rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ) := by
  rcases eo_prog_concat_csplit_eq_of_ne_stuck rev t s u hProg with
    ⟨hProgEq, _hHeadT, _hScLen⟩
  rcases len_nonzero_seq_type_of_bool u hNonzeroBool with ⟨T, huTy⟩
  have huNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [huTy]
        exact seq_ne_none T)
  rcases concatCSplit_rev_cases_of_prog_ne_stuck rev t s u hProg huNe with
    hRev | hRev
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true :=
        hPremisesTrue (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) (by simp)
      rcases csplit_context_true M hM t s u hPremBool hNonzeroBool hProg
          hST with
        ⟨U, sc, tPrefix, sPrefix, hScEq, huTy, hscTy, htPrefixTy, hsPrefixTy,
          hScLen, hConcatEq⟩
      rw [hProgEq]
      rw [← hScEq]
      exact concat_csplit_true_facts M hM u sc tPrefix sPrefix U
        huTy hscTy htPrefixTy hsPrefixTy hScLen hNonzero hConcatEq
    · rw [hProgEq]
      rcases csplit_context_true_head_type t s u hPremBool hNonzeroBool
          hProg with
        ⟨U, huTyU, hHeadTy⟩
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concat_csplit_formula_has_bool_type (Term.Boolean true) u
          (concatCSplitHead (Term.Boolean true) s) U huTyU
          hHeadTy (Or.inl rfl))
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) true :=
        hPremisesTrue (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) (by simp)
      rcases csplit_context_false M hM t s u hPremBool hNonzeroBool hProg
          hST with
        ⟨U, sc, tTail, sTail, hScEq, huTy, hscTy, htTailTy, hsTailTy,
          hScLen, hConcatEq⟩
      rw [hProgEq]
      rw [← hScEq]
      exact concat_csplit_false_facts M hM u sc tTail sTail U
        huTy hscTy htTailTy hsTailTy hScLen hNonzero hConcatEq
    · rw [hProgEq]
      rcases csplit_context_false_head_type t s u hPremBool hNonzeroBool
          hProg with
        ⟨U, huTyU, hHeadTy⟩
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concat_csplit_formula_has_bool_type (Term.Boolean false) u
          (concatCSplitHead (Term.Boolean false) s) U huTyU
          hHeadTy (Or.inr rfl))

public theorem cmd_step_concat_csplit_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_csplit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_csplit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_csplit args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_csplit args premises ≠
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
                          __eo_prog_concat_csplit a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_csplit a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_csplit_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, u, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkNot (mkEq (mkStrLen u) (Term.Numeral 0)) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hNonzeroBool :
                          RuleProofs.eo_has_bool_type
                            (mkNot (mkEq (mkStrLen u) (Term.Numeral 0))) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_csplit a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_csplit a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkNot
                                    (mkEq (mkStrLen u) (Term.Numeral 0))))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_csplit a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_csplit a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_csplit_core M hM a1 lhs rhs u
                        hA1Trans hPremEqBool hNonzeroBool hProgRule
                        hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
