module

public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatCPropNormalize (rev x : Term) : Term :=
  concatSplitNormalize rev x

private abbrev concatCPropHead (rev x : Term) : Term :=
  concatSplitHead rev x

private abbrev concatCPropSecond (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatCPropNormalize rev x)
    (Term.Numeral 1)

private abbrev concatCPropFlatSecond (rev x : Term) : Term :=
  __str_flatten (__str_nary_intro (concatCPropSecond rev x))

private abbrev concatCPropSHeadTailWord (rev s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let sHeadLen := __eo_len sHead
  __str_flatten
    (__str_nary_intro
      (__eo_ite rev
        (__eo_extract sHead (Term.Numeral 0)
          (__eo_add sHeadLen (Term.Numeral (-2 : native_Int))))
        (__eo_extract sHead (Term.Numeral 1) sHeadLen)))

private abbrev concatCPropOverlapLen (rev t s : Term) : Term :=
  __eo_add (Term.Numeral 1)
    (__str_overlap_rec
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropSHeadTailWord rev s))
        (concatCPropSHeadTailWord rev s))
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropFlatSecond rev t))
        (concatCPropFlatSecond rev t)))

private abbrev concatCPropPrefix (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  __eo_mk_apply
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (Term.Numeral 0))
    (concatCPropOverlapLen rev t s)

private abbrev concatCPropSuffix (rev t s tc : Term) : Term :=
  let pfx := concatCPropPrefix rev t s
  __eo_mk_apply (Term.UOp UserOp._at_purify)
    (__eo_mk_apply
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)))

private abbrev concatCPropReverseSuffix (rev t s tc : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  let endPart :=
    __eo_mk_apply
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
          k))
      k
  __eo_mk_apply (Term.UOp UserOp._at_purify)
    (__eo_mk_apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)))

private abbrev concatCPropReverseEnd (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.neg)
          (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
        k))
    k

private abbrev concatCPropFormula (rev t s tc : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
    (__eo_ite rev
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropReverseSuffix rev t s tc))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropReverseEnd rev t s))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropReverseSuffix rev t s tc)))))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropPrefix rev t s))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropSuffix rev t s tc))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropPrefix rev t s))))))

private abbrev concatCPropBody (rev t s tc : Term) : Term :=
  __eo_requires (concatCPropHead rev t) tc (concatCPropFormula rev t s tc)

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
    exact hLeftNN
  exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
    (typeof_str_len_eq (__eo_to_smt u)) hLenTerm

private theorem cprop_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem cprop_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem cprop_mk_apply_eq_apply_of_args_ne_stuck (f x : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem cprop_seq_type_ne_stuck (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    x ≠ Term.Stuck :=
  RuleProofs.term_ne_stuck_of_has_smt_translation x
    (by unfold RuleProofs.eo_has_smt_translation; rw [hxTy]; exact seq_ne_none T)

private theorem smt_typeof_eo_add_one_of_ne_stuck (x : Term)
    (h : __eo_add (Term.Numeral 1) x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_add (Term.Numeral 1) x)) =
      SmtType.Int := by
  cases x <;> simp [__eo_add] at h ⊢
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral (native_zplus 1 n)) = SmtType.Int
    rw [__smtx_typeof.eq_2]

private theorem cprop_eo_add_one_arg_ne_stuck (x : Term)
    (h : __eo_add (Term.Numeral 1) x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  cases x <;> simp [__eo_add] at h ⊢

private theorem str_overlap_rec_numeral_of_ne_stuck :
    ∀ (a b : Term), __str_overlap_rec a b ≠ Term.Stuck →
      ∃ n : Nat, __str_overlap_rec a b = Term.Numeral (Int.ofNat n) := by
  intro a b h
  cases a with
  | Stuck =>
      simp [__str_overlap_rec] at h
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at h
                · have hDef :
                      __str_overlap_rec
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat) y) x) b =
                        __eo_ite
                          (__str_is_compatible
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) y) x) b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [__str_overlap_rec] at hb ⊢
                  cases hCompat :
                      __str_is_compatible
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)
                        b with
                  | Boolean bv =>
                      cases bv
                      · have hRecNe : __str_overlap_rec x b ≠ Term.Stuck := by
                          apply cprop_eo_add_one_arg_ne_stuck
                          simpa [hDef, hCompat, __eo_ite, native_ite, native_teq] using h
                        rcases str_overlap_rec_numeral_of_ne_stuck x b hRecNe with
                          ⟨n, hRec⟩
                        refine ⟨n + 1, ?_⟩
                        rw [hDef, hCompat, hRec]
                        simp [__eo_ite, __eo_add, native_zplus, native_ite, native_teq]
                        rw [Int.add_comm]
                      · refine ⟨0, ?_⟩
                        rw [hDef, hCompat]
                        simp [__eo_ite, native_ite, native_teq]
                  | _ =>
                      simp [hDef, hCompat, __eo_ite, native_ite, native_teq] at h
              · cases b <;> simp [__str_overlap_rec, hOp] at h ⊢ <;>
                  try exact ⟨0, rfl⟩
          | _ =>
              cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
                try exact ⟨0, rfl⟩
      | _ =>
          cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
            try exact ⟨0, rfl⟩
  | _ =>
      cases b <;> simp [__str_overlap_rec] at h ⊢ <;>
        try exact ⟨0, rfl⟩
termination_by a b _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private def strConcatDrop : Term → Nat → Term
  | a, 0 => a
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) _) tail, n + 1 =>
      strConcatDrop tail n
  | a, _ + 1 => a

private theorem nat_zero_of_term_numeral_zero_eq (m : Nat)
    (h : Term.Numeral (0 : native_Int) = Term.Numeral (Int.ofNat m)) :
    m = 0 := by
  injection h with hInt
  exact Int.ofNat_eq_zero.mp hInt.symm

private theorem nat_succ_of_term_numeral_add_one_eq (m r : Nat)
    (h :
      Term.Numeral (native_zplus (1 : native_Int) (Int.ofNat r)) =
        Term.Numeral (Int.ofNat m)) :
    m = r + 1 := by
  injection h with hInt
  have hCast : Int.ofNat m = Int.ofNat (r + 1) := by
    rw [← hInt]
    simp [native_zplus]
    omega
  exact Int.ofNat_inj.mp hCast

private theorem str_overlap_rec_le_of_compatible_drop :
    ∀ (a b : Term) (m n : Nat),
      __str_overlap_rec a b = Term.Numeral (Int.ofNat m) →
      __str_is_compatible (strConcatDrop a n) b = Term.Boolean true →
      m <= n := by
  intro a b m n hRec hCompat
  cases a with
  | Stuck =>
      cases b <;> simp [__str_overlap_rec] at hRec
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at hRec
                · let aCons :=
                    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x
                  have hDef :
                      __str_overlap_rec aCons b =
                        __eo_ite (__str_is_compatible aCons b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [aCons, __str_overlap_rec] at hb ⊢
                  cases hComp : __str_is_compatible aCons b with
                  | Boolean bv =>
                      cases bv
                      · cases n with
                        | zero =>
                            simp [aCons, strConcatDrop, hComp] at hCompat
                        | succ n =>
                            have hRecArg :
                                __str_overlap_rec x b ≠ Term.Stuck := by
                              have hAddEq :
                                  __eo_add (Term.Numeral 1)
                                      (__str_overlap_rec x b) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp] at hRec
                                simpa [__eo_ite, native_ite, native_teq]
                                  using hRec
                              intro hStuck
                              rw [hStuck] at hAddEq
                              simp [__eo_add] at hAddEq
                            rcases str_overlap_rec_numeral_of_ne_stuck x b
                                hRecArg with
                              ⟨r, hTailRec⟩
                            have hm : m = r + 1 := by
                              have hTerm :
                                  Term.Numeral
                                      (native_zplus (1 : native_Int)
                                        (Int.ofNat r)) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp, hTailRec] at hRec
                                simpa [__eo_ite, __eo_add, native_ite,
                                  native_teq] using hRec
                              exact nat_succ_of_term_numeral_add_one_eq m r
                                hTerm
                            have hTailCompat :
                                __str_is_compatible (strConcatDrop x n) b =
                                  Term.Boolean true := by
                              simpa [aCons, strConcatDrop] using hCompat
                            have hrle :
                                r <= n :=
                              str_overlap_rec_le_of_compatible_drop x b r n
                                hTailRec hTailCompat
                            omega
                      · rw [hDef, hComp] at hRec
                        have hm0 : m = 0 :=
                          nat_zero_of_term_numeral_zero_eq m
                            (by
                              simpa [__eo_ite, native_ite, native_teq]
                                using hRec)
                        omega
                  | _ =>
                      rw [hDef, hComp] at hRec
                      simp [__eo_ite, native_ite, native_teq] at hRec
              · cases b <;>
                  simp [__str_overlap_rec, hOp] at hRec <;>
                  (have hm0 : m = 0 :=
                    nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                   omega)
          | _ =>
              cases b <;> simp [__str_overlap_rec] at hRec <;>
                (have hm0 : m = 0 :=
                  nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                 omega)
      | _ =>
          cases b <;> simp [__str_overlap_rec] at hRec <;>
            (have hm0 : m = 0 :=
              nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
             omega)
  | _ =>
      cases b <;> simp [__str_overlap_rec] at hRec <;>
        (have hm0 : m = 0 :=
          nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
         omega)
termination_by a b m n _ _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private theorem str_overlap_rec_compatible_drop_false_of_lt :
    ∀ (a b : Term) (m n : Nat),
      __str_overlap_rec a b = Term.Numeral (Int.ofNat m) →
      n < m →
      __str_is_compatible (strConcatDrop a n) b = Term.Boolean false := by
  intro a b m n hRec hLt
  cases a with
  | Stuck =>
      cases b <;> simp [__str_overlap_rec] at hRec
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              by_cases hOp : op = UserOp.str_concat
              · subst op
                by_cases hb : b = Term.Stuck
                · subst b
                  simp [__str_overlap_rec] at hRec
                · let aCons :=
                    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x
                  have hDef :
                      __str_overlap_rec aCons b =
                        __eo_ite (__str_is_compatible aCons b)
                          (Term.Numeral 0)
                          (__eo_add (Term.Numeral 1)
                            (__str_overlap_rec x b)) := by
                    cases b <;> simp [aCons, __str_overlap_rec] at hb ⊢
                  cases hComp : __str_is_compatible aCons b with
                  | Boolean bv =>
                      cases bv
                      · cases n with
                        | zero =>
                            simpa [aCons, strConcatDrop] using hComp
                        | succ n =>
                            have hRecArg :
                                __str_overlap_rec x b ≠ Term.Stuck := by
                              have hAddEq :
                                  __eo_add (Term.Numeral 1)
                                      (__str_overlap_rec x b) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp] at hRec
                                simpa [__eo_ite, native_ite, native_teq]
                                  using hRec
                              intro hStuck
                              rw [hStuck] at hAddEq
                              simp [__eo_add] at hAddEq
                            rcases str_overlap_rec_numeral_of_ne_stuck x b
                                hRecArg with
                              ⟨r, hTailRec⟩
                            have hm : m = r + 1 := by
                              have hTerm :
                                  Term.Numeral
                                      (native_zplus (1 : native_Int)
                                        (Int.ofNat r)) =
                                    Term.Numeral (Int.ofNat m) := by
                                rw [hDef, hComp, hTailRec] at hRec
                                simpa [__eo_ite, __eo_add, native_ite,
                                  native_teq] using hRec
                              exact nat_succ_of_term_numeral_add_one_eq m r
                                hTerm
                            have hnLt : n < r := by omega
                            have hTailFalse :
                                __str_is_compatible (strConcatDrop x n) b =
                                  Term.Boolean false :=
                              str_overlap_rec_compatible_drop_false_of_lt
                                x b r n hTailRec hnLt
                            simpa [aCons, strConcatDrop] using hTailFalse
                      · rw [hDef, hComp] at hRec
                        have hm0 : m = 0 :=
                          nat_zero_of_term_numeral_zero_eq m
                            (by
                              simpa [__eo_ite, native_ite, native_teq]
                                using hRec)
                        omega
                  | _ =>
                      rw [hDef, hComp] at hRec
                      simp [__eo_ite, native_ite, native_teq] at hRec
              · cases b <;>
                  simp [__str_overlap_rec, hOp] at hRec <;>
                  (have hm0 : m = 0 :=
                    nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                   omega)
          | _ =>
              cases b <;> simp [__str_overlap_rec] at hRec <;>
                (have hm0 : m = 0 :=
                  nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
                 omega)
      | _ =>
          cases b <;> simp [__str_overlap_rec] at hRec <;>
            (have hm0 : m = 0 :=
              nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
             omega)
  | _ =>
      cases b <;> simp [__str_overlap_rec] at hRec <;>
        (have hm0 : m = 0 :=
          nat_zero_of_term_numeral_zero_eq m (by simpa using hRec)
         omega)
termination_by a b m n _ _ => sizeOf a
decreasing_by
  all_goals
    subst_vars
    simp_wf
    omega

private theorem eo_list_nth_one_str_concat_cons_eq_tail_zero
    (head tail : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true) :
    __eo_list_nth (Term.UOp UserOp.str_concat) (mkConcat head tail)
        (Term.Numeral 1) =
      __eo_list_nth (Term.UOp UserOp.str_concat) tail (Term.Numeral 0) := by
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true := by
    simpa [mkConcat] using
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) head tail (by simp)
      hTailList
  simp [__eo_list_nth, __eo_list_nth_rec, mkConcat, hConsList,
    hTailList, __eo_add, native_zplus]

private theorem str_overlap_rec_left_ne_stuck_of_ne_stuck
    (a b : Term) (h : __str_overlap_rec a b ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro ha
  subst a
  cases b <;> simp [__str_overlap_rec] at h

private theorem str_overlap_rec_right_ne_stuck_of_ne_stuck
    (a b : Term) (h : __str_overlap_rec a b ≠ Term.Stuck) :
    b ≠ Term.Stuck := by
  intro hb
  subst b
  cases a <;> simp [__str_overlap_rec] at h

private theorem cprop_str_flatten_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_flatten x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_flatten] at h

private theorem cprop_false_head_string_of_tailword_ne
    (s sc : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean false) s ≠ Term.Stuck) :
    ∃ cs : native_String, sc = Term.String cs := by
  subst sc
  generalize hHead : concatCPropHead (Term.Boolean false) s = h
  have hhTy : __smtx_typeof (__eo_to_smt h) = SmtType.Seq T := by
    rw [← hHead]
    exact hscTy
  have hTail :
      __str_flatten
          (__str_nary_intro
            (__eo_extract h (Term.Numeral 1) (__eo_len h))) ≠
        Term.Stuck := by
    rw [← hHead]
    simpa [concatCPropSHeadTailWord, eo_ite_false] using hTailWordNe
  have hExtractNe :
      __eo_extract h (Term.Numeral 1) (__eo_len h) ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (__eo_extract h (Term.Numeral 1) (__eo_len h))
      (cprop_str_flatten_arg_ne_stuck_of_ne_stuck
        (__str_nary_intro
          (__eo_extract h (Term.Numeral 1) (__eo_len h))) hTail)
  cases h with
  | String cs =>
      exact ⟨cs, rfl⟩
  | Binary w n =>
      change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hhTy
      rw [__smtx_typeof.eq_5] at hhTy
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at hhTy
  | Stuck =>
      simp [__eo_extract] at hExtractNe
  | _ =>
      simp [__eo_extract] at hExtractNe

private theorem cprop_true_head_string_of_tailword_ne
    (s sc : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean true) s ≠ Term.Stuck) :
    ∃ cs : native_String, sc = Term.String cs := by
  subst sc
  generalize hHead : concatCPropHead (Term.Boolean true) s = h
  have hhTy : __smtx_typeof (__eo_to_smt h) = SmtType.Seq T := by
    rw [← hHead]
    exact hscTy
  have hTail :
      __str_flatten
          (__str_nary_intro
            (__eo_extract h (Term.Numeral 0)
              (__eo_add (__eo_len h) (Term.Numeral (-2 : native_Int))))) ≠
        Term.Stuck := by
    rw [← hHead]
    simpa [concatCPropSHeadTailWord, eo_ite_true] using hTailWordNe
  have hExtractNe :
      __eo_extract h (Term.Numeral 0)
          (__eo_add (__eo_len h) (Term.Numeral (-2 : native_Int))) ≠
        Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (__eo_extract h (Term.Numeral 0)
        (__eo_add (__eo_len h) (Term.Numeral (-2 : native_Int))))
      (cprop_str_flatten_arg_ne_stuck_of_ne_stuck
        (__str_nary_intro
          (__eo_extract h (Term.Numeral 0)
            (__eo_add (__eo_len h) (Term.Numeral (-2 : native_Int))))) hTail)
  cases h with
  | String cs =>
      exact ⟨cs, rfl⟩
  | Binary w n =>
      change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hhTy
      rw [__smtx_typeof.eq_5] at hhTy
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at hhTy
  | Stuck =>
      simp [__eo_extract] at hExtractNe
  | _ =>
      simp [__eo_extract] at hExtractNe

private theorem strConcatDrop_substrWord
    (s : native_String) :
    ∀ (n d : Nat) (start : native_Int),
      d <= n ->
      strConcatDrop (RuleProofs.substrWord s start n) d =
        RuleProofs.substrWord s (start + Int.ofNat d) (n - d)
  | _n, 0, _start, _h => by
      simp [strConcatDrop]
  | 0, d + 1, _start, h => by
      omega
  | n + 1, d + 1, start, h => by
      simp [RuleProofs.substrWord, strConcatDrop]
      have hdn : d <= n := Nat.succ_le_succ_iff.mp h
      have hDrop :=
        strConcatDrop_substrWord s n d (start + 1) hdn
      rw [hDrop]
      have hStart :
          start + 1 + Int.ofNat d = start + (Int.ofNat d + 1) := by
        ac_rfl
      rw [hStart]
      simp

private theorem strConcatDrop_string_empty (n : Nat) :
    strConcatDrop (Term.String []) n = Term.String [] := by
  cases n <;> rfl

private theorem take_length_sub_one_eq_dropLast {α : Type} :
    ∀ xs : List α, xs.take (xs.length - 1) = xs.dropLast
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
      simpa using take_length_sub_one_eq_dropLast (y :: xs)

private theorem take_dropLast_eq_take_of_le {α : Type}
    (xs : List α) (n : Nat) (hn : n <= xs.length - 1) :
    xs.dropLast.take n = xs.take n := by
  rw [← take_length_sub_one_eq_dropLast xs]
  rw [List.take_take]
  rw [Nat.min_eq_left hn]

private theorem native_str_substr_prefix_dropLast (s : native_String) :
    native_str_substr s 0 ((s.length : Int) - 1) = s.dropLast := by
  cases s with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons c cs =>
      cases cs with
      | nil =>
          simp [native_str_substr, native_str_len]
      | cons d ds =>
          have hIf :
              ¬ ((↑(List.length ds) : Int) + 1 <= 0 ∨
                  (↑(List.length ds) : Int) + 1 + 1 <= 0) := by
            omega
          have hMin :
              (min (↑(List.length ds) : Int)
                    ((↑(List.length ds) : Int) + 1) + 1).toNat =
                ds.length + 1 := by
            have h :
                min (↑(List.length ds) : Int)
                    ((↑(List.length ds) : Int) + 1) =
                  (↑(List.length ds) : Int) := by
              exact Int.min_eq_left (by omega)
            rw [h]
            simp
          simp [native_str_substr, native_str_len, hIf, hMin]
          simpa using take_length_sub_one_eq_dropLast (c :: d :: ds)

private theorem eo_extract_prefix_dropLast (s : native_String) :
    __eo_extract (Term.String s) (Term.Numeral 0)
        (__eo_add (__eo_len (Term.String s)) (Term.Numeral (-2))) =
      Term.String s.dropLast := by
  simp only [__eo_extract, __eo_add, __eo_len, native_str_len]
  rw [show
      native_zplus (native_zplus (native_zplus (Int.ofNat s.length) (-2))
          (native_zneg 0)) 1 =
        (s.length : Int) - 1 by
    change ((Int.ofNat s.length + (-2 : Int)) + -0 + 1) =
      (Int.ofNat s.length : Int) - 1
    omega]
  exact congrArg Term.String (native_str_substr_prefix_dropLast s)

private theorem eo_or_true_ne_false (b : Term) :
    __eo_or (Term.Boolean true) b ≠ Term.Boolean false := by
  cases b <;> simp [__eo_or, SmtEval.native_or]

private theorem eo_or_true_right_ne_false (b : Term) :
    __eo_or b (Term.Boolean true) ≠ Term.Boolean false := by
  cases b <;> simp [__eo_or, SmtEval.native_or]

private theorem str_is_compatible_empty_left_ne_false (b : Term) :
    __str_is_compatible (Term.String []) b ≠ Term.Boolean false := by
  cases b <;> try simp [__str_is_compatible]
  all_goals
    simp only [__eo_l_1___str_is_compatible, __str_is_empty]
    exact eo_or_true_ne_false _

private theorem str_is_compatible_empty_right_ne_false (a : Term) :
    __str_is_compatible a (Term.String []) ≠ Term.Boolean false := by
  cases a <;> try simp [__str_is_compatible]
  all_goals
    simp only [__eo_l_1___str_is_compatible, __str_is_empty]
    exact eo_or_true_right_ne_false _

private theorem str_is_compatible_str_is_empty_right_ne_false
    (a b : Term) (hb : __str_is_empty b = Term.Boolean true) :
    __str_is_compatible a b ≠ Term.Boolean false := by
  cases b with
  | String s =>
      cases s with
      | nil =>
          exact str_is_compatible_empty_right_ne_false a
      | cons c cs =>
          simp [__str_is_empty] at hb
  | UOp1 op A =>
      cases op <;> simp [__str_is_empty] at hb
      case seq_empty =>
        cases A with
        | Apply f U =>
            cases f with
            | UOp op =>
                cases op <;> simp at hb
                case Seq =>
                  cases a <;> try simp [__str_is_compatible]
                  all_goals
                    simp only [__eo_l_1___str_is_compatible, __str_is_empty]
                    exact eo_or_true_right_ne_false _
            | _ =>
                simp at hb
        | _ =>
            simp at hb
  | _ =>
      simp [__str_is_empty] at hb

private theorem str_is_empty_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_is_empty (__seq_empty (__eo_typeof x)) = Term.Boolean true := by
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
  cases U <;> simp [__seq_empty, __str_is_empty]
  case UOp op =>
    cases op <;> simp

private theorem str_is_compatible_seq_empty_typeof_right_ne_false
    (a x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_is_compatible a (__seq_empty (__eo_typeof x)) ≠
      Term.Boolean false :=
  str_is_compatible_str_is_empty_right_ne_false a
    (__seq_empty (__eo_typeof x))
    (str_is_empty_seq_empty_typeof_of_seq x T hxTy)

private theorem eo_typeof_string_local (s : native_String) :
    __eo_typeof (Term.String s) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  rfl

private theorem str_is_compatible_word_mkConcat_non_string_head_ne_false
    (c : native_Char) (cs : native_String) (x tail : Term)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s) :
    __str_is_compatible
        (RuleProofs.substrWord (c :: cs) 0 ((c :: cs).length))
        (mkConcat x tail) ≠
      Term.Boolean false := by
  change
    __str_is_compatible
        (mkConcat (Term.String (RuleProofs.extractString (c :: cs) 0))
          (RuleProofs.substrWord (c :: cs) (0 + 1) cs.length))
        (mkConcat x tail) ≠
      Term.Boolean false
  rw [RuleProofs.extractString_zero_cons]
  change
    __str_is_compatible
        (mkConcat (Term.String [c])
          (RuleProofs.substrWord (c :: cs) 1 cs.length))
        (mkConcat x tail) ≠
      Term.Boolean false
  rw [RuleProofs.substrWord_cons_tail c cs]
  cases x <;>
    simp [__str_is_compatible, __eo_l_1___str_is_compatible,
      __eo_eq, __are_distinct_terms_type.eq_def, __eo_and, __eo_is_str,
      __eo_is_str_internal, __eo_requires, eo_typeof_string_local,
      native_teq, native_ite, SmtEval.native_and, SmtEval.native_not]
  case String s =>
    exact False.elim (hxNotString ⟨s, rfl⟩)

private theorem substrWord_compatible_ne_false_of_append_eq :
    ∀ (word str : native_String) (xTail suffixTail : List SmtValue),
      str.map SmtValue.Char ++ xTail =
        word.map SmtValue.Char ++ suffixTail →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (RuleProofs.substrWord str 0 str.length) ≠
        Term.Boolean false
  | [], str, xTail, suffixTail, hAlign => by
      exact str_is_compatible_empty_left_ne_false
        (RuleProofs.substrWord str 0 str.length)
  | c :: cs, [], xTail, suffixTail, hAlign => by
      exact str_is_compatible_empty_right_ne_false
        (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length)
  | c :: cs, d :: ds, xTail, suffixTail, hAlign => by
      injection hAlign with hChar hTail
      injection hChar with hHead
      subst d
      have hTail :
          ds.map SmtValue.Char ++ xTail =
            cs.map SmtValue.Char ++ suffixTail := by
        simpa using hTail
      simp [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
      rw [RuleProofs.substrWord_cons_tail c cs,
        RuleProofs.substrWord_cons_tail c ds]
      simpa [__str_is_compatible, __eo_eq, native_teq, native_ite] using
        substrWord_compatible_ne_false_of_append_eq cs ds xTail suffixTail hTail

private theorem native_str_substr_tail_len_cons
    (c : native_Char) (cs : native_String) :
    native_str_substr (c :: cs) 1 (Int.ofNat (cs.length + 1)) = cs := by
  cases cs with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons d ds =>
      have hIf :
          ¬ (((↑(List.length ds) : Int) + 1 + 1) <= 0 ∨
              ((↑(List.length ds) : Int) + 1 + 1) <= 1) := by
        omega
      have hMin :
          (min (((↑(List.length ds) : Int) + 1))
              (↑(List.length ds) : Int) + 1).toNat =
            ds.length + 1 := by
        have h :
            min (((↑(List.length ds) : Int) + 1))
              (↑(List.length ds) : Int) =
              (↑(List.length ds) : Int) := by
          exact Int.min_eq_right (by omega)
        rw [h]
        simp
      simp [native_str_substr, native_str_len, hIf]
      rw [hMin]
      simp

private theorem eo_extract_tail_len_cons
    (c : native_Char) (cs : native_String) :
    __eo_extract (Term.String (c :: cs)) (Term.Numeral 1)
        (__eo_len (Term.String (c :: cs))) =
      Term.String cs := by
  simp only [__eo_extract, __eo_len, native_str_len]
  rw [show native_zplus
        (native_zplus (Int.ofNat ((c :: cs).length)) (native_zneg 1)) 1 =
      Int.ofNat (cs.length + 1) by
        change ((Int.ofNat (List.length (c :: cs)) : Int) + -1 + 1) =
          Int.ofNat (cs.length + 1)
        simp
        omega]
  exact congrArg Term.String (native_str_substr_tail_len_cons c cs)

private theorem extractString_cons_succ_nat_local
    (c : native_Char) (cs : native_String) (i : Nat) :
    RuleProofs.extractString (c :: cs) ((i : Int) + 1) =
      RuleProofs.extractString cs (i : Int) := by
  by_cases hLt : i < cs.length
  · have hLenNotLe : ¬ cs.length <= i := Nat.not_le_of_gt hLt
    have hLeftNonneg :
        ¬ (((i : Int) + 1 < 0) ∨
          ((i : Int) + 1 + -((i : Int) + 1) + 1 <= 0)) := by
      omega
    have hRightNonneg :
        ¬ (((i : Int) < 0) ∨ ((i : Int) + -(i : Int) + 1 <= 0)) := by
      omega
    have hMinLeft :
        (min ((i : Int) + 1 + -((i : Int) + 1) + 1)
            ((cs.length : Int) + 1 - ((i : Int) + 1))).toNat = 1 := by
      have h :
          min ((i : Int) + 1 + -((i : Int) + 1) + 1)
              ((cs.length : Int) + 1 - ((i : Int) + 1)) =
            1 := by
        omega
      simp [h]
    have hMinRight :
        (min ((i : Int) + -(i : Int) + 1)
            ((cs.length : Int) - (i : Int))).toNat = 1 := by
      have h :
          min ((i : Int) + -(i : Int) + 1)
              ((cs.length : Int) - (i : Int)) =
            1 := by
        omega
      simp [h]
    simp [RuleProofs.extractString, native_str_substr, native_str_len,
      native_zplus, native_zneg, hLenNotLe,
      hMinLeft, hMinRight, List.drop_succ_cons]
    -- both guards are false and both branches agree.  `rw [if_neg ..]` cannot
    -- be used: it must match the goal's `Decidable` instance syntactically,
    -- while `refine` unifies it up to defeq and hands us the exact conditions.
    refine Eq.trans (if_neg ?_) (Eq.symm (if_neg ?_))
    -- reuse the negations proved above; the goal's disjunct is the `Bool`
    -- form `decide _ = true`, which is only propositionally equal to theirs
    · rintro (h | h)
      · exact hLeftNonneg (Or.inl h)
      · exact hLeftNonneg (Or.inr (of_decide_eq_true h))
    · rintro (h | h)
      · exact hRightNonneg (Or.inl h)
      · exact hRightNonneg (Or.inr (of_decide_eq_true h))
  · have hLeft : ((i : Int) + 1) >= ((cs.length : Int) + 1) := by
      omega
    have hLenLe : cs.length <= i := Nat.le_of_not_gt hLt
    simp [RuleProofs.extractString, native_str_substr, native_str_len,
      native_zplus, native_zneg, hLeft, hLenLe]

private theorem substrWord_cons_succ_nat_local
    (c : native_Char) (cs : native_String) :
    ∀ (n i : Nat),
      RuleProofs.substrWord (c :: cs) (Int.ofNat (i + 1)) n =
        RuleProofs.substrWord cs (Int.ofNat i) n
  | 0, _i => by rfl
  | n + 1, i => by
      simp only [RuleProofs.substrWord]
      have hHeadStart :
          Int.ofNat (i + 1) = (i : Int) + 1 := by
        simp
      rw [hHeadStart, extractString_cons_succ_nat_local c cs i]
      have hRightStart :
          Int.ofNat i + 1 = Int.ofNat (i + 1) := by
        simp
      have hLeftStart :
          (i : Int) + 1 + 1 = Int.ofNat (i + 1 + 1) := by
        simp
      rw [hRightStart, hLeftStart,
        substrWord_cons_succ_nat_local c cs n (i + 1)]
      rfl

private theorem substrWord_drop_suffix :
    ∀ (s : native_String) (i : Nat), i <= s.length ->
      RuleProofs.substrWord s (Int.ofNat i) (s.length - i) =
        RuleProofs.substrWord (s.drop i) 0 (s.drop i).length
  | _s, 0, _h => by simp
  | [], i + 1, h => by simp at h
  | c :: cs, i + 1, h => by
      have hi : i <= cs.length := by
        simpa using Nat.succ_le_succ_iff.mp h
      have hLen : (c :: cs).length - (i + 1) = cs.length - i := by
        simp
      rw [hLen]
      rw [substrWord_cons_succ_nat_local c cs (cs.length - i) i]
      simpa using substrWord_drop_suffix cs i hi

private theorem cprop_eo_requires_refl_local
    (x z : Term) (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, native_ite, native_teq, native_not, hx]

private theorem substrWord_is_list_local
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __eo_is_list (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord s start n) =
        Term.Boolean true
  | 0, _start => by
      simp [RuleProofs.substrWord, __eo_is_list, __eo_get_nil_rec,
        __eo_requires, __eo_is_ok, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, native_teq, native_ite,
        native_not, SmtEval.native_not]
  | n + 1, start => by
      simp only [RuleProofs.substrWord, __eo_is_list, __eo_get_nil_rec]
      rw [cprop_eo_requires_refl_local (Term.UOp UserOp.str_concat)
        (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord s (start + 1) n)) (by simp)]
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord s (start + 1) n)) =
          Term.Boolean true
      have hTail := substrWord_is_list_local s n (start + 1)
      unfold __eo_is_list at hTail
      cases hSub : RuleProofs.substrWord s (start + 1) n <;>
        simp [hSub] at hTail ⊢ <;>
        exact hTail

private def intRangeTermLocal : native_Int -> Nat -> Term
  | _start, 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | start, n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral start))
        (intRangeTermLocal (start + 1) n)

private theorem str_flatten_word_rec_range_eq_substrWord_local
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      __str_flatten_word_rec (intRangeTermLocal start n) (Term.String s) =
        RuleProofs.substrWord s start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [intRangeTermLocal, RuleProofs.substrWord,
        __str_flatten_word_rec, __eo_extract, RuleProofs.extractString]
      rw [str_flatten_word_rec_range_eq_substrWord_local s n (start + 1)]
      simp [__eo_mk_apply, RuleProofs.substrWord_ne_stuck]

private def zeroIntListTermLocal : Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (Term.UOp UserOp.Int)
  | n + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (zeroIntListTermLocal n)

private theorem zeroIntListTermLocal_ne_stuck :
    ∀ n, zeroIntListTermLocal n ≠ Term.Stuck
  | 0 => by simp [zeroIntListTermLocal]
  | _n + 1 => by simp [zeroIntListTermLocal]

private theorem eo_list_repeat_rec_zero_eq_local :
    ∀ n,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) n =
        zeroIntListTermLocal n
  | 0 => by rfl
  | n + 1 => by
      simp [__eo_list_repeat_rec, zeroIntListTermLocal,
        eo_list_repeat_rec_zero_eq_local n, __eo_mk_apply,
        zeroIntListTermLocal_ne_stuck]

private theorem eo_list_repeat_zero_eq_local (n : Nat) :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) (Term.Numeral (Int.ofNat n)) =
      zeroIntListTermLocal n := by
  have hnot : native_zlt (↑n : native_Int) 0 = false := by
    simp [native_zlt]
  simp [__eo_list_repeat, native_ite, native_int_to_nat, hnot,
    eo_list_repeat_rec_zero_eq_local]

private theorem eo_list_repeat_zero_eq_local_zero :
    __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
        (Term.Numeral 0) (Term.Numeral 0) =
      zeroIntListTermLocal 0 := by
  simpa using eo_list_repeat_zero_eq_local 0

private theorem intRangeTermLocal_ne_stuck :
    ∀ n start, intRangeTermLocal start n ≠ Term.Stuck
  | 0, _start => by simp [intRangeTermLocal]
  | _n + 1, _start => by simp [intRangeTermLocal]

private theorem iota_zero_list_eq_range_local :
    ∀ (n : Nat) (start : native_Int),
      __iota_rec (zeroIntListTermLocal n) (Term.Numeral start) =
        intRangeTermLocal start n
  | 0, _start => by rfl
  | n + 1, start => by
      simp only [zeroIntListTermLocal, intRangeTermLocal, __iota_rec,
        __eo_add, native_zplus]
      rw [iota_zero_list_eq_range_local n (start + 1)]
      simp [__eo_mk_apply, intRangeTermLocal_ne_stuck]

private theorem str_flatten_concat_string_eq
    (s : native_String) (tail : Term) :
    __str_flatten (mkConcat (Term.String s) tail) =
      __eo_list_concat (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord s 0 s.length) (__str_flatten tail) := by
  cases s with
  | nil =>
      change
        __eo_ite (__eo_is_str (Term.String []))
            (__eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten_word_rec
                (__eo_requires (__eo_is_neg (Term.Numeral 0))
                  (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0) (Term.Numeral 0))
                    (Term.Numeral 0)))
                (Term.String []))
              (__str_flatten tail))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String []))
              (__str_flatten tail)) =
          __eo_list_concat (Term.UOp UserOp.str_concat) (Term.String [])
            (__str_flatten tail)
      have hIsStr :
          __eo_is_str (Term.String []) = Term.Boolean true := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not,
          SmtEval.native_and]
      have hReqLen :
          __eo_requires (__eo_is_neg (Term.Numeral 0))
              (Term.Boolean false)
              (__iota_rec
                (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral 0) (Term.Numeral 0))
                (Term.Numeral 0)) =
            __iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) (Term.Numeral 0))
              (Term.Numeral 0) := by
        rw [show __eo_is_neg (Term.Numeral 0) = Term.Boolean false by
          rfl]
        exact cprop_eo_requires_refl_local (Term.Boolean false) _ (by simp)
      rw [hIsStr, eo_ite_true, hReqLen, eo_list_repeat_zero_eq_local_zero,
        iota_zero_list_eq_range_local,
        str_flatten_word_rec_range_eq_substrWord_local]
      simp [RuleProofs.substrWord]
  | cons c cs =>
      change
        __eo_ite (__eo_is_str (Term.String (c :: cs)))
            (__eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten_word_rec
                (__eo_requires
                  (__eo_is_neg
                    (Term.Numeral (Int.ofNat (List.length cs + 1))))
                  (Term.Boolean false)
                  (__iota_rec
                    (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.Numeral 0)
                      (Term.Numeral (Int.ofNat (List.length cs + 1))))
                    (Term.Numeral 0)))
                (Term.String (c :: cs)))
              (__str_flatten tail))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs)))
              (__str_flatten tail)) =
          __eo_list_concat (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord (c :: cs) 0 (List.length cs + 1))
            (__str_flatten tail)
      have hIsStr :
          __eo_is_str (Term.String (c :: cs)) = Term.Boolean true := by
        simp [__eo_is_str, __eo_is_str_internal, native_teq, native_not,
          SmtEval.native_and]
      have hReqLen :
          __eo_requires
              (__eo_is_neg
                (Term.Numeral (Int.ofNat (List.length cs + 1))))
              (Term.Boolean false)
              (__iota_rec
                (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral 0)
                  (Term.Numeral (Int.ofNat (List.length cs + 1))))
                (Term.Numeral 0)) =
            __iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0)
                (Term.Numeral (Int.ofNat (List.length cs + 1))))
              (Term.Numeral 0) := by
        rw [show
            __eo_is_neg (Term.Numeral (Int.ofNat (List.length cs + 1))) =
              Term.Boolean false by
            change
              Term.Boolean (native_zlt (Int.ofNat (List.length cs + 1)) 0) =
                Term.Boolean false
            have hCountLen :
                native_zlt (Int.ofNat (List.length cs + 1)) 0 = false := by
              change decide ((Int.ofNat (List.length cs + 1) : Int) < 0) =
                false
              simp
              omega
            rw [hCountLen]]
        exact cprop_eo_requires_refl_local (Term.Boolean false) _ (by simp)
      rw [hIsStr, eo_ite_true, hReqLen, eo_list_repeat_zero_eq_local,
        iota_zero_list_eq_range_local,
        str_flatten_word_rec_range_eq_substrWord_local]

private theorem term_ne_stuck_of_eo_is_list_true_local (f x : Term)
    (hList : __eo_is_list f x = Term.Boolean true) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_is_list] at hList

private theorem eo_list_concat_substrWord_eq_rec_of_tail_list
    (str : native_String) (tail : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord str 0 str.length) tail =
      __eo_list_concat_rec (RuleProofs.substrWord str 0 str.length) tail := by
  have hWordList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord str 0 str.length) =
        Term.Boolean true :=
    substrWord_is_list_local str str.length 0
  simp [__eo_list_concat, hWordList, hTailList, __eo_requires,
    native_ite, native_teq, native_not]

private theorem eo_list_concat_substrWord_eq_stuck_of_tail_not_list
    (str : native_String) (tail : Term)
    (hTailList :
      ¬ __eo_is_list (Term.UOp UserOp.str_concat) tail =
        Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord str 0 str.length) tail =
      Term.Stuck := by
  have hWordList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord str 0 str.length) =
        Term.Boolean true :=
    substrWord_is_list_local str str.length 0
  simp [__eo_list_concat, hWordList, hTailList, __eo_requires,
    native_ite, native_teq, native_not]

private theorem eo_list_rev_rec_list_concat_rec_substrWord_eq :
    ∀ (str : native_String) (tail acc : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true →
      acc ≠ Term.Stuck →
      __eo_list_rev_rec
          (__eo_list_concat_rec
            (RuleProofs.substrWord str 0 str.length) tail) acc =
        __eo_list_rev_rec tail
          (__eo_list_rev_rec
            (RuleProofs.substrWord str 0 str.length) acc)
  | [], tail, acc, hTailList, hAccNe => by
      change
        __eo_list_rev_rec (__eo_list_concat_rec (Term.String []) tail) acc =
          __eo_list_rev_rec tail (__eo_list_rev_rec (Term.String []) acc)
      have hNilNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []) =
            Term.Boolean true := by
        simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
        change decide (Term.String [] = Term.String []) = true
        simp
      rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
        (Term.String []) tail hNilNil]
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true
        (Term.String []) acc hNilNil]
  | c :: cs, tail, acc, hTailList, hAccNe => by
      have hTailWordList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord cs 0 cs.length) =
            Term.Boolean true :=
        substrWord_is_list_local cs cs.length 0
      have hTailNe : tail ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true_local
          (Term.UOp UserOp.str_concat) tail hTailList
      have hTailConcatNe :
          __eo_list_concat_rec (RuleProofs.substrWord cs 0 cs.length)
              tail ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord cs 0 cs.length) tail hTailWordList hTailNe
      have hCons :
          RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
            mkConcat (Term.String [c])
              (RuleProofs.substrWord cs 0 cs.length) := by
        change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [c])
            (RuleProofs.substrWord (c :: cs) 1 cs.length) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        rw [RuleProofs.substrWord_cons_tail]
      rw [hCons]
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        (Term.String [c]) (RuleProofs.substrWord cs 0 cs.length) tail
        hTailConcatNe]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
        (Term.String [c])
        (__eo_list_concat_rec (RuleProofs.substrWord cs 0 cs.length) tail)
        acc hAccNe]
      have hConsAccNe :
          mkConcat (Term.String [c]) acc ≠ Term.Stuck := by
        intro h
        cases h
      rw [eo_list_rev_rec_list_concat_rec_substrWord_eq cs tail
        (mkConcat (Term.String [c]) acc) hTailList hConsAccNe]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
        (Term.String [c]) (RuleProofs.substrWord cs 0 cs.length) acc
        hAccNe]

private theorem eo_get_nil_rec_list_concat_rec_substrWord_eq :
    ∀ (str : native_String) (tail : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true →
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_concat_rec
            (RuleProofs.substrWord str 0 str.length) tail) =
        __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
  | [], tail, hTailList => by
      change
        __eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (__eo_list_concat_rec (Term.String []) tail) =
          __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
      have hNilNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []) =
            Term.Boolean true := by
        simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
        change decide (Term.String [] = Term.String []) = true
        simp
      rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
        (Term.String []) tail hNilNil]
  | c :: cs, tail, hTailList => by
      have hTailWordList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord cs 0 cs.length) =
            Term.Boolean true :=
        substrWord_is_list_local cs cs.length 0
      have hTailNe : tail ≠ Term.Stuck :=
        term_ne_stuck_of_eo_is_list_true_local
          (Term.UOp UserOp.str_concat) tail hTailList
      have hTailConcatNe :
          __eo_list_concat_rec (RuleProofs.substrWord cs 0 cs.length)
              tail ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord cs 0 cs.length) tail hTailWordList hTailNe
      have hTailConcatList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__eo_list_concat_rec
                (RuleProofs.substrWord cs 0 cs.length) tail) =
            Term.Boolean true :=
        eo_list_concat_rec_is_list_true_of_lists
          (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord cs 0 cs.length) tail hTailWordList
          hTailList
      have hCons :
          RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
            mkConcat (Term.String [c])
              (RuleProofs.substrWord cs 0 cs.length) := by
        change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [c])
            (RuleProofs.substrWord (c :: cs) 1 cs.length) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        rw [RuleProofs.substrWord_cons_tail]
      rw [hCons]
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        (Term.String [c]) (RuleProofs.substrWord cs 0 cs.length) tail
        hTailConcatNe]
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list
        (Term.UOp UserOp.str_concat) (Term.String [c])
        (__eo_list_concat_rec (RuleProofs.substrWord cs 0 cs.length)
          tail) (by decide) hTailConcatList]
      exact eo_get_nil_rec_list_concat_rec_substrWord_eq cs tail hTailList

private theorem str_is_compatible_substrWord_rev_rec_substrWord_acc_ne_false :
    ∀ (word str : native_String) (acc : Term)
      (accVals suffixTail : List SmtValue),
      str.reverse.map SmtValue.Char ++ accVals =
        word.map SmtValue.Char ++ suffixTail →
      (∀ (word' : native_String) (suffixTail' : List SmtValue),
        accVals = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) acc ≠
            Term.Boolean false) →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (__eo_list_rev_rec
            (RuleProofs.substrWord str 0 str.length) acc) ≠
        Term.Boolean false
  | word, [], acc, accVals, suffixTail, hAlign, hAccCompat => by
      change
        __str_is_compatible (RuleProofs.substrWord word 0 word.length)
            (__eo_list_rev_rec (Term.String []) acc) ≠
          Term.Boolean false
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true
        (Term.String []) acc]
      · exact hAccCompat word suffixTail (by simpa using hAlign)
      · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
        change decide (Term.String [] = Term.String []) = true
        simp
  | [], c :: cs, acc, accVals, suffixTail, hAlign, hAccCompat => by
      exact str_is_compatible_empty_left_ne_false
        (__eo_list_rev_rec
          (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length) acc)
  | wc :: wcs, c :: cs, acc, accVals, suffixTail, hAlign, hAccCompat => by
      by_cases hAccNe : acc ≠ Term.Stuck
      · have hCons :
            RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
              mkConcat (Term.String [c])
                (RuleProofs.substrWord cs 0 cs.length) := by
          change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
            mkConcat (Term.String [c])
              (RuleProofs.substrWord cs 0 cs.length)
          simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
          change mkConcat (Term.String [c])
              (RuleProofs.substrWord (c :: cs) 1 cs.length) =
            mkConcat (Term.String [c])
              (RuleProofs.substrWord cs 0 cs.length)
          rw [RuleProofs.substrWord_cons_tail]
        rw [hCons]
        rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
          (Term.String [c]) (RuleProofs.substrWord cs 0 cs.length) acc
          hAccNe]
        exact
          str_is_compatible_substrWord_rev_rec_substrWord_acc_ne_false
            (wc :: wcs) cs (mkConcat (Term.String [c]) acc)
            ((SmtValue.Char c) :: accVals) suffixTail
            (by
              simpa [List.reverse_cons, List.map_append, List.append_assoc]
                using hAlign)
            (by
              intro word' suffixTail' hAccAlign
              cases word' with
              | nil =>
                  exact str_is_compatible_empty_left_ne_false
                    (mkConcat (Term.String [c]) acc)
              | cons d ds =>
                  injection hAccAlign with hChar hTail
                  injection hChar with hHead
                  subst d
                  have hLeftCons :
                      RuleProofs.substrWord (c :: ds) 0 (c :: ds).length =
                        mkConcat (Term.String [c])
                          (RuleProofs.substrWord ds 0 ds.length) := by
                    change RuleProofs.substrWord (c :: ds) 0
                        (ds.length + 1) =
                      mkConcat (Term.String [c])
                        (RuleProofs.substrWord ds 0 ds.length)
                    simp only [RuleProofs.substrWord,
                      RuleProofs.extractString_zero_cons]
                    change mkConcat (Term.String [c])
                        (RuleProofs.substrWord (c :: ds) 1 ds.length) =
                      mkConcat (Term.String [c])
                        (RuleProofs.substrWord ds 0 ds.length)
                    rw [RuleProofs.substrWord_cons_tail]
                  rw [hLeftCons]
                  simpa [__str_is_compatible, __eo_eq, native_teq,
                    native_ite] using hAccCompat ds suffixTail' hTail)
      · have hAcc : acc = Term.Stuck := by
          by_cases h : acc = Term.Stuck
          · exact h
          · exact False.elim (hAccNe h)
        rw [hAcc]
        have hRight :
            __eo_list_rev_rec
                (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length)
                Term.Stuck =
              Term.Stuck := by
          cases hSub :
              RuleProofs.substrWord (c :: cs) 0 (c :: cs).length <;>
            simp [__eo_list_rev_rec]
        rw [hRight]
        cases hLeft :
            RuleProofs.substrWord (wc :: wcs) 0 (wc :: wcs).length <;>
          simp [__str_is_compatible]

private theorem eo_list_concat_substrWord_nil_eq_of_tail_list
    (tail : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) (Term.String []) tail =
      tail := by
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) (Term.String []) =
        Term.Boolean true :=
    substrWord_is_list_local [] 0 0
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []) =
        Term.Boolean true := by
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
    change decide (Term.String [] = Term.String []) = true
    simp
  simp [__eo_list_concat, hNilList, hTailList, __eo_requires, native_ite,
    native_teq, native_not,
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true
      (Term.String []) tail hNilNil]

private theorem eo_list_concat_substrWord_nil_eq_stuck_of_tail_not_list
    (tail : Term)
    (hTailList :
      ¬ __eo_is_list (Term.UOp UserOp.str_concat) tail =
        Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) (Term.String []) tail =
      Term.Stuck := by
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) (Term.String []) =
        Term.Boolean true :=
    substrWord_is_list_local [] 0 0
  simp [__eo_list_concat, hNilList, hTailList, __eo_requires, native_ite,
    native_teq, native_not]

private theorem eo_list_concat_substrWord_cons_eq
    (c : native_Char) (cs : native_String) (tail : Term) :
    __eo_list_concat (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length) tail =
      __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (__eo_list_concat (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord cs 0 cs.length) tail) := by
  by_cases hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true
  · let tailWord := RuleProofs.substrWord cs 0 cs.length
    have hTailWordList :
        __eo_is_list (Term.UOp UserOp.str_concat) tailWord =
          Term.Boolean true := by
      simpa [tailWord] using substrWord_is_list_local cs cs.length 0
    have hCons :
        RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
          mkConcat (Term.String [c]) tailWord := by
      change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
        mkConcat (Term.String [c]) tailWord
      simp only [tailWord, RuleProofs.substrWord,
        RuleProofs.extractString_zero_cons]
      change mkConcat (Term.String [c])
          (RuleProofs.substrWord (c :: cs) 1 cs.length) =
        mkConcat (Term.String [c]) tailWord
      rw [RuleProofs.substrWord_cons_tail]
    have hConsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (mkConcat (Term.String [c]) tailWord) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) (Term.String [c]) tailWord
        (by decide) hTailWordList
    have hTailNe : tail ≠ Term.Stuck :=
      term_ne_stuck_of_eo_is_list_true_local
        (Term.UOp UserOp.str_concat) tail hTailList
    have hInnerRecNe :
        __eo_list_concat_rec tailWord tail ≠ Term.Stuck :=
      eo_list_concat_rec_ne_stuck_of_list
        (Term.UOp UserOp.str_concat) tailWord tail hTailWordList hTailNe
    have hLeftEq :
      __eo_list_concat (Term.UOp UserOp.str_concat)
          (mkConcat (Term.String [c]) tailWord) tail =
        __eo_list_concat_rec (mkConcat (Term.String [c]) tailWord) tail := by
      simp [__eo_list_concat, hConsList, hTailList, __eo_requires,
        native_ite, native_teq, native_not]
    have hRightEq :
        __eo_list_concat (Term.UOp UserOp.str_concat) tailWord tail =
          __eo_list_concat_rec tailWord tail := by
      simp [__eo_list_concat, hTailWordList, hTailList, __eo_requires,
        native_ite, native_teq, native_not]
    rw [hCons, hLeftEq, hRightEq]
    rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
      (Term.String [c]) tailWord tail hInnerRecNe]
    cases hRec : __eo_list_concat_rec tailWord tail <;>
      simp [__eo_mk_apply, mkConcat, hRec] at hInnerRecNe ⊢
  · have hConsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length) =
          Term.Boolean true :=
      substrWord_is_list_local (c :: cs) (c :: cs).length 0
    have hTailWordList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord cs 0 cs.length) =
          Term.Boolean true :=
      substrWord_is_list_local cs cs.length 0
    have hLeft :
        __eo_list_concat (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord (c :: cs) 0 (c :: cs).length) tail =
          Term.Stuck := by
      simp [__eo_list_concat, hTailList, __eo_requires,
        native_ite, native_teq, native_not]
    have hRight :
        __eo_list_concat (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord cs 0 cs.length) tail =
          Term.Stuck := by
      simp [__eo_list_concat, hTailWordList, hTailList, __eo_requires,
        native_ite, native_teq, native_not]
    rw [hLeft, hRight]
    simp [__eo_mk_apply]

private theorem str_is_compatible_substrWord_list_concat_ne_false :
    ∀ (word str : native_String) (tail : Term)
      (xTail suffixTail : List SmtValue),
      str.map SmtValue.Char ++ xTail =
        word.map SmtValue.Char ++ suffixTail →
      (∀ (word' : native_String) (suffixTail' : List SmtValue),
        xTail = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) tail ≠
            Term.Boolean false) →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (__eo_list_concat (Term.UOp UserOp.str_concat)
            (RuleProofs.substrWord str 0 str.length) tail) ≠
        Term.Boolean false
  | [], str, tail, xTail, suffixTail, hAlign, hTailCompat => by
      exact str_is_compatible_empty_left_ne_false
        (__eo_list_concat (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord str 0 str.length) tail)
  | wc :: wcs, [], tail, xTail, suffixTail, hAlign, hTailCompat => by
      have hAlignTail :
          xTail = (wc :: wcs).map SmtValue.Char ++ suffixTail := by
        simpa using hAlign
      change
        __str_is_compatible
            (RuleProofs.substrWord (wc :: wcs) 0 (wc :: wcs).length)
            (__eo_list_concat (Term.UOp UserOp.str_concat)
              (Term.String []) tail) ≠
          Term.Boolean false
      by_cases hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true
      · rw [eo_list_concat_substrWord_nil_eq_of_tail_list tail hTailList]
        exact hTailCompat (wc :: wcs) suffixTail hAlignTail
      · rw [eo_list_concat_substrWord_nil_eq_stuck_of_tail_not_list
          tail hTailList]
        cases hSub :
            RuleProofs.substrWord (wc :: wcs) 0 (wc :: wcs).length <;>
          simp [__str_is_compatible]
  | wc :: wcs, c :: cs, tail, xTail, suffixTail, hAlign, hTailCompat => by
      injection hAlign with hChar hTail
      injection hChar with hHead
      subst c
      have hTailAlign :
          cs.map SmtValue.Char ++ xTail =
            wcs.map SmtValue.Char ++ suffixTail := by
        simpa using hTail
      rw [eo_list_concat_substrWord_cons_eq wc cs tail]
      have hLeftCons :
          RuleProofs.substrWord (wc :: wcs) 0 (wc :: wcs).length =
            mkConcat (Term.String [wc])
              (RuleProofs.substrWord wcs 0 wcs.length) := by
        change RuleProofs.substrWord (wc :: wcs) 0 (wcs.length + 1) =
          mkConcat (Term.String [wc])
            (RuleProofs.substrWord wcs 0 wcs.length)
        simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [wc])
            (RuleProofs.substrWord (wc :: wcs) 1 wcs.length) =
          mkConcat (Term.String [wc])
            (RuleProofs.substrWord wcs 0 wcs.length)
        rw [RuleProofs.substrWord_cons_tail]
      rw [hLeftCons]
      by_cases hRightTail :
          __eo_list_concat (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord cs 0 cs.length) tail =
            Term.Stuck
      · rw [hRightTail]
        simp [__eo_mk_apply, __str_is_compatible]
      · have hRightMk :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String [wc]))
                (__eo_list_concat (Term.UOp UserOp.str_concat)
                  (RuleProofs.substrWord cs 0 cs.length) tail) =
              mkConcat (Term.String [wc])
                (__eo_list_concat (Term.UOp UserOp.str_concat)
                  (RuleProofs.substrWord cs 0 cs.length) tail) := by
          cases hRight :
              __eo_list_concat (Term.UOp UserOp.str_concat)
                (RuleProofs.substrWord cs 0 cs.length) tail <;>
            simp [__eo_mk_apply, mkConcat, hRight] at hRightTail ⊢
        rw [hRightMk]
        simp [__str_is_compatible, __eo_eq, native_teq, native_ite]
        exact
          str_is_compatible_substrWord_list_concat_ne_false wcs cs tail
            xTail suffixTail hTailAlign hTailCompat

private theorem substrWord_get_nil_local
    (s : native_String) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord s 0 s.length) =
      Term.String [] := by
  induction s with
  | nil =>
      exact eo_get_nil_rec_str_concat_eq_of_nil_true (Term.String [])
        (by
          simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
          change decide (Term.String [] = Term.String []) = true
          simp)
  | cons c cs ih =>
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord cs 0 cs.length) =
            Term.Boolean true :=
        substrWord_is_list_local cs cs.length 0
      have hCons :
          RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
            mkConcat (Term.String [c])
              (RuleProofs.substrWord cs 0 cs.length) := by
        change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [c])
            (RuleProofs.substrWord (c :: cs) 1 cs.length) =
          mkConcat (Term.String [c])
            (RuleProofs.substrWord cs 0 cs.length)
        rw [RuleProofs.substrWord_cons_tail]
      rw [hCons]
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list
        (Term.UOp UserOp.str_concat) (Term.String [c])
        (RuleProofs.substrWord cs 0 cs.length) (by decide) hTailList]
      exact ih

private theorem substrWord_append_singleton_local
    (s : native_String) (c : native_Char) :
    __eo_list_concat_rec
        (RuleProofs.substrWord s 0 s.length)
        (mkConcat (Term.String [c]) (Term.String [])) =
      RuleProofs.substrWord (s ++ [c]) 0 (s ++ [c]).length := by
  induction s with
  | nil =>
      change __eo_list_concat_rec (Term.String [])
          (mkConcat (Term.String [c]) (Term.String [])) =
        RuleProofs.substrWord ([c] : native_String) 0 1
      rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
        (Term.String []) (mkConcat (Term.String [c]) (Term.String []))]
      · change mkConcat (Term.String [c]) (Term.String []) =
          RuleProofs.substrWord ([c] : native_String) 0 1
        simp [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
      · simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
        change decide (Term.String [] = Term.String []) = true
        simp
  | cons h t ih =>
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (RuleProofs.substrWord t 0 t.length) =
            Term.Boolean true :=
        substrWord_is_list_local t t.length 0
      have hZNe :
          mkConcat (Term.String [c]) (Term.String []) ≠ Term.Stuck := by
        intro hz
        cases hz
      have hTailConcatNe :
          __eo_list_concat_rec (RuleProofs.substrWord t 0 t.length)
              (mkConcat (Term.String [c]) (Term.String [])) ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord t 0 t.length)
          (mkConcat (Term.String [c]) (Term.String []))
          hTailList hZNe
      have hCons :
          RuleProofs.substrWord (h :: t) 0 (h :: t).length =
            mkConcat (Term.String [h])
              (RuleProofs.substrWord t 0 t.length) := by
        change RuleProofs.substrWord (h :: t) 0 (t.length + 1) =
          mkConcat (Term.String [h])
            (RuleProofs.substrWord t 0 t.length)
        simp only [RuleProofs.substrWord, RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [h])
            (RuleProofs.substrWord (h :: t) 1 t.length) =
          mkConcat (Term.String [h])
            (RuleProofs.substrWord t 0 t.length)
        rw [RuleProofs.substrWord_cons_tail]
      rw [hCons]
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        (Term.String [h]) (RuleProofs.substrWord t 0 t.length)
        (mkConcat (Term.String [c]) (Term.String [])) hTailConcatNe]
      rw [ih]
      have hConsAppend :
          RuleProofs.substrWord (h :: t ++ [c]) 0 (h :: t ++ [c]).length =
            mkConcat (Term.String [h])
              (RuleProofs.substrWord (t ++ [c]) 0 (t ++ [c]).length) := by
        change RuleProofs.substrWord (h :: t ++ [c]) 0
            ((t ++ [c]).length + 1) =
          mkConcat (Term.String [h])
            (RuleProofs.substrWord (t ++ [c]) 0 (t ++ [c]).length)
        simp only [RuleProofs.substrWord]
        have hExtract :
            RuleProofs.extractString (h :: t ++ [c]) 0 = [h] := by
          simpa using RuleProofs.extractString_zero_cons h (t ++ [c])
        rw [hExtract]
        change mkConcat (Term.String [h])
            (RuleProofs.substrWord (h :: t ++ [c]) 1
              (t ++ [c]).length) =
          mkConcat (Term.String [h])
            (RuleProofs.substrWord (t ++ [c]) 0 (t ++ [c]).length)
        have hTailSub :
            RuleProofs.substrWord (h :: t ++ [c]) 1
                (t ++ [c]).length =
              RuleProofs.substrWord (t ++ [c]) 0 (t ++ [c]).length := by
          simpa using RuleProofs.substrWord_cons_tail h (t ++ [c])
        rw [hTailSub]
      exact hConsAppend.symm

private theorem eo_list_rev_substrWord_local
    (s : native_String) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord s 0 s.length) =
      RuleProofs.substrWord s.reverse 0 s.reverse.length := by
  induction s with
  | nil =>
      exact eo_list_rev_str_concat_nil_eq_of_nil_true (Term.String [])
        (by
          simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
          change decide (Term.String [] = Term.String []) = true
          simp)
  | cons c cs ih =>
      let tail := RuleProofs.substrWord cs 0 cs.length
      let nil := Term.String []
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true := by
        simpa [tail] using substrWord_is_list_local cs cs.length 0
      have hNilList :
          __eo_is_list (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true := by
        simp [nil, __eo_is_list, __eo_get_nil_rec, __eo_requires,
          __eo_is_ok, __eo_is_list_nil, __eo_is_list_nil_str_concat,
          __eo_eq, native_teq, native_ite, native_not, SmtEval.native_not]
      have hNilGet :
          __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail = nil := by
        simpa [tail, nil] using substrWord_get_nil_local cs
      have hCons :
          RuleProofs.substrWord (c :: cs) 0 (c :: cs).length =
            mkConcat (Term.String [c]) tail := by
        change RuleProofs.substrWord (c :: cs) 0 (cs.length + 1) =
          mkConcat (Term.String [c]) tail
        simp only [tail, RuleProofs.substrWord,
          RuleProofs.extractString_zero_cons]
        change mkConcat (Term.String [c])
            (RuleProofs.substrWord (c :: cs) 1 cs.length) =
          mkConcat (Term.String [c]) tail
        rw [RuleProofs.substrWord_cons_tail]
      have hConsList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (mkConcat (Term.String [c]) tail) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) (Term.String [c]) tail
          (by decide) hTailList
      have hRevConsNe :
          __eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat (Term.String [c]) tail) ≠ Term.Stuck :=
        eo_list_rev_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) (mkConcat (Term.String [c]) tail)
          hConsList
      have hRevTailNe :
          __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck :=
        eo_list_rev_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList
      have hRevTailEq :
          __eo_list_rev (Term.UOp UserOp.str_concat) tail =
            __eo_list_rev_rec tail nil := by
        rw [eo_list_rev_eq_rec_of_ne_stuck
          (Term.UOp UserOp.str_concat) tail hRevTailNe]
        rw [hNilGet]
      have hRevConsEq :
          __eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat (Term.String [c]) tail) =
            __eo_list_rev_rec tail (mkConcat (Term.String [c]) nil) := by
        rw [eo_list_rev_str_concat_cons_eq_of_ne_stuck
          (Term.String [c]) tail hRevConsNe]
        rw [hNilGet]
      rw [hCons]
      rw [hRevConsEq]
      have hNilNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true := by
        simp [nil, __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
        change decide (Term.String [] = Term.String []) = true
        simp
      rw [← eo_list_concat_rec_str_concat_nil_eq_of_nil_true nil
        (mkConcat (Term.String [c]) nil) hNilNil]
      rw [eo_list_rev_rec_list_concat_rec_singleton_eq tail nil
        (Term.String [c]) nil hTailList hNilList]
      rw [← hRevTailEq]
      rw [ih]
      simpa [List.reverse_cons, nil] using
        substrWord_append_singleton_local cs.reverse c

private theorem strConcatDrop_rev_substrWord_eq_rev_take
    (s : native_String) (d : Nat) (hd : d <= s.length) :
    strConcatDrop
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord s 0 s.length)) d =
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (RuleProofs.substrWord (s.take (s.length - d)) 0
          (s.take (s.length - d)).length) := by
  rw [eo_list_rev_substrWord_local s]
  have hdRev : d <= s.reverse.length := by
    simpa using hd
  rw [strConcatDrop_substrWord s.reverse s.reverse.length d 0 hdRev]
  have hDrop :
      RuleProofs.substrWord s.reverse (0 + Int.ofNat d)
          (s.reverse.length - d) =
        RuleProofs.substrWord (s.reverse.drop d) 0
          (s.reverse.drop d).length := by
    simpa using substrWord_drop_suffix s.reverse d hdRev
  rw [hDrop]
  have hDropEq :
      s.reverse.drop d = (s.take (s.length - d)).reverse := by
    simpa using (List.drop_reverse (xs := s) (i := d))
  rw [hDropEq]
  rw [← eo_list_rev_substrWord_local (s.take (s.length - d))]

private theorem string_eval_unpack_eq
    (M : SmtModel) (s : native_String) (ss : SmtSeq)
    (hEval :
      __smtx_model_eval M (__eo_to_smt (Term.String s)) =
        SmtValue.Seq ss) :
    native_unpack_seq ss = s.map SmtValue.Char := by
  change __smtx_model_eval M (SmtTerm.String s) = SmtValue.Seq ss at hEval
  rw [__smtx_model_eval.eq_4] at hEval
  injection hEval with hSeq
  rw [← hSeq]
  simp [native_pack_string, _root_.native_unpack_pack_seq]

private theorem mkConcat_eval_unpack_eq_local
    (M : SmtModel) (x y : Term) (sxy sx sy : SmtSeq)
    (hxyEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    native_unpack_seq sxy =
      native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hyEval] at hxyEval
  simp [__smtx_model_eval_str_concat, native_seq_concat] at hxyEval
  rw [← hxyEval]
  simp [_root_.native_unpack_pack_seq]

private theorem mkConcat_args_eval_unpack_of_concat_eval
    (M : SmtModel) (x y : Term) (sxy : SmtSeq)
    (hxyEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy) :
    ∃ sx sy,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
          native_unpack_seq sxy =
            native_unpack_seq sx ++ native_unpack_seq sy := by
  rcases strConcat_args_seq_eval_of_concat_seq_eval M x y
      ⟨sxy, hxyEval⟩ with
    ⟨⟨sx, hxEval⟩, ⟨sy, hyEval⟩⟩
  exact ⟨sx, sy, hxEval, hyEval,
    mkConcat_eval_unpack_eq_local M x y sxy sx sy hxyEval hxEval hyEval⟩

private theorem str_flatten_eq_default_of_not_str_concat (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_flatten x =
      __eo_requires x (__seq_empty (__eo_typeof x)) x := by
  cases x with
  | Stuck =>
      rfl
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · simp [__str_flatten, hop]
          | _ =>
              simp [__str_flatten]
      | _ =>
          simp [__str_flatten]
  | _ =>
      simp [__str_flatten]

private theorem str_nary_intro_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_nary_intro x ≠ Term.Stuck := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, rfl⟩
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

private theorem eo_is_str_false_of_not_string_ne_stuck (x : Term)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s)
    (hxNe : x ≠ Term.Stuck) :
    __eo_is_str x = Term.Boolean false := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq,
      SmtEval.native_and, SmtEval.native_not] at hxNe ⊢
  case String s =>
    exact False.elim (hxNotString ⟨s, rfl⟩)

private theorem eo_list_concat_eq_rec_of_lists_local
    (a z : Term)
    (hListA :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hListZ :
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true) :
    __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_list_concat_rec a z := by
  have hzNe : z ≠ Term.Stuck := by
    intro hz
    subst z
    simp [__eo_is_list] at hListZ
  have hRecNe : __eo_list_concat_rec a z ≠ Term.Stuck :=
    eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
      a z hListA hzNe
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) =
    __eo_list_concat_rec a z
  rw [hListA, hListZ]
  simp [eo_requires_self_eq_of_ne_stuck]

private theorem eo_list_concat_args_list_of_result_list_local
    (a z : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_concat (Term.UOp UserOp.str_concat) a z) =
        Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) z = Term.Boolean true := by
  have hConcatNe :
      __eo_list_concat (Term.UOp UserOp.str_concat) a z ≠ Term.Stuck := by
    intro h
    rw [h] at hList
    simp [__eo_is_list] at hList
  change __eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) a)
      (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) ≠ Term.Stuck at hConcatNe
  have hA := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) hConcatNe
  have hInnerNe := eo_requires_result_ne_stuck_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
    (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
      (Term.Boolean true) (__eo_list_concat_rec a z)) hConcatNe
  have hZ := eo_requires_eq_of_ne_stuck
    (__eo_is_list (Term.UOp UserOp.str_concat) z) (Term.Boolean true)
    (__eo_list_concat_rec a z) hInnerNe
  exact ⟨hA, hZ⟩

private theorem eo_list_concat_rec_assoc_local :
    ∀ (a b c : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) b = Term.Boolean true →
      c ≠ Term.Stuck →
      __eo_list_concat_rec (__eo_list_concat_rec a b) c =
        __eo_list_concat_rec a (__eo_list_concat_rec b c) := by
  intro a b
  induction a, b using __eo_list_concat_rec.induct with
  | case1 b =>
      intro c hA hB hC
      simp [__eo_is_list] at hA
  | case2 a hA =>
      intro c hListA hB hC
      simp [__eo_is_list] at hB
  | case3 f head tail b hB0 ih =>
      intro c hA hB hC
      have hf : f = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.str_concat) f head tail hA
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) head tail hA
      have hBNe : b ≠ Term.Stuck := by
        intro hb
        subst b
        simp [__eo_is_list] at hB
      have hBCNe : __eo_list_concat_rec b c ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) b c hB hC
      have hTailBNe : __eo_list_concat_rec tail b ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) tail b hTailList hBNe
      have hTailBList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__eo_list_concat_rec tail b) = Term.Boolean true :=
        eo_list_concat_rec_is_list_true_of_lists
          (Term.UOp UserOp.str_concat) tail b hTailList hB
      have hTailBCNe :
          __eo_list_concat_rec tail (__eo_list_concat_rec b c) ≠
            Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) tail (__eo_list_concat_rec b c)
          hTailList hBCNe
      have hNestedNe :
          __eo_list_concat_rec (__eo_list_concat_rec tail b) c ≠
            Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) (__eo_list_concat_rec tail b) c
          hTailBList hC
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head tail b hTailBNe]
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head (__eo_list_concat_rec tail b) c hNestedNe]
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head tail (__eo_list_concat_rec b c) hTailBCNe]
      rw [ih c hTailList hB hC]
  | case4 nil b hNilNe hBNe hNotCons =>
      intro c hA hB hC
      rw [__eo_list_concat_rec.eq_4 nil b hNilNe hNotCons hBNe]
      have hBCNe : __eo_list_concat_rec b c ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) b c hB hC
      rw [__eo_list_concat_rec.eq_4 nil (__eo_list_concat_rec b c)
        hNilNe hNotCons hBCNe]

private theorem eo_list_rev_rec_concat_rec_local :
    ∀ (a b acc : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) b = Term.Boolean true →
      acc ≠ Term.Stuck →
      __eo_list_rev_rec (__eo_list_concat_rec a b) acc =
        __eo_list_rev_rec b (__eo_list_rev_rec a acc) := by
  intro a b
  induction a, b using __eo_list_concat_rec.induct with
  | case1 b =>
      intro acc hA hB hAccNe
      simp [__eo_is_list] at hA
  | case2 a hA =>
      intro acc hListA hB hAccNe
      simp [__eo_is_list] at hB
  | case3 f head tail b hBNe ih =>
      intro acc hA hB hAccNe
      have hf : f = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.str_concat) f head tail hA
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) head tail hA
      have hBNonStuck : b ≠ Term.Stuck := by
        intro hb
        subst b
        simp [__eo_is_list] at hB
      have hTailBNe : __eo_list_concat_rec tail b ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) tail b hTailList hBNonStuck
      have hNewAccNe : mkConcat head acc ≠ Term.Stuck := by
        intro h
        cases h
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head tail b hTailBNe]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) head
        (__eo_list_concat_rec tail b) acc hAccNe]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) head tail acc
        hAccNe]
      exact ih (mkConcat head acc) hTailList hB hNewAccNe
  | case4 nil b hNilNe hBNe hNotCons =>
      intro acc hA hB hAccNe
      rw [__eo_list_concat_rec.eq_4 nil b hNilNe hNotCons hBNe]
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true :=
        eo_is_list_nil_str_concat_of_list_true_not_concat_local nil hA
          (by
            intro h
            rcases h with ⟨head, tail, hEq⟩
            exact hNotCons _ _ _ hEq)
      rw [show __eo_list_rev_rec nil acc = acc by
        exact eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil acc hNil]

private theorem eo_get_nil_rec_concat_rec_local :
    ∀ (a b : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) b = Term.Boolean true →
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_concat_rec a b) =
        __eo_get_nil_rec (Term.UOp UserOp.str_concat) b := by
  intro a b
  induction a, b using __eo_list_concat_rec.induct with
  | case1 b =>
      intro hA hB
      simp [__eo_is_list] at hA
  | case2 a hA =>
      intro hListA hB
      simp [__eo_is_list] at hB
  | case3 f head tail b hBNe ih =>
      intro hA hB
      have hf : f = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.str_concat) f head tail hA
      subst f
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) head tail hA
      have hBNonStuck : b ≠ Term.Stuck := by
        intro hb
        subst b
        simp [__eo_is_list] at hB
      have hTailBNe : __eo_list_concat_rec tail b ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) tail b hTailList hBNonStuck
      have hTailBList :
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__eo_list_concat_rec tail b) = Term.Boolean true :=
        eo_list_concat_rec_is_list_true_of_lists
          (Term.UOp UserOp.str_concat) tail b hTailList hB
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        head tail b hTailBNe]
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list
        (Term.UOp UserOp.str_concat) head (__eo_list_concat_rec tail b)
        (by decide) hTailBList]
      exact ih hTailList hB
  | case4 nil b hNilNe hBNe hNotCons =>
      intro hA hB
      rw [__eo_list_concat_rec.eq_4 nil b hNilNe hNotCons hBNe]

private theorem str_is_compatible_full_word_flatten_concat_raw_non_string_head_ne_false
    (head tail : Term) (T : SmtType) (wc : native_Char) (wcs : native_String)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hHeadNotString : ¬ ∃ s : native_String, head = Term.String s)
    (hHeadNotConcat : ∀ h t : Term, head ≠ mkConcat h t) :
    __str_is_compatible
        (RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length))
        (__str_flatten (mkConcat head tail)) ≠
      Term.Boolean false := by
  have hHeadNe : head ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq head T hHeadTy
  have hIsStr : __eo_is_str head = Term.Boolean false :=
    eo_is_str_false_of_not_string_ne_stuck head hHeadNotString hHeadNe
  rw [__str_flatten.eq_3 head tail hHeadNotConcat, hIsStr, eo_ite_false]
  by_cases hTail : __str_flatten tail = Term.Stuck
  · rw [hTail]
    change
      __str_is_compatible
          (mkConcat (Term.String [wc])
            (RuleProofs.substrWord wcs 0 wcs.length))
          Term.Stuck ≠
        Term.Boolean false
    simp [__str_is_compatible]
  · have hApply :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) head)
            (__str_flatten tail) =
          mkConcat head (__str_flatten tail) := by
      simp [__eo_mk_apply, mkConcat]
    rw [hApply]
    exact str_is_compatible_word_mkConcat_non_string_head_ne_false
      wc wcs head (__str_flatten tail) hHeadNotString

private theorem str_is_compatible_full_word_flatten_non_concat_ne_false
    (x : Term) (T : SmtType) (wc : native_Char) (wcs : native_String)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_is_compatible
        (RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length))
        (__str_flatten x) ≠
      Term.Boolean false := by
  rw [str_flatten_eq_default_of_not_str_concat x hNotConcat]
  by_cases hReq :
      __eo_requires x (__seq_empty (__eo_typeof x)) x = Term.Stuck
  · rw [hReq]
    cases hSub :
        RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length) <;>
      simp [__str_is_compatible]
  · have hReqEq :
        __eo_requires x (__seq_empty (__eo_typeof x)) x = x :=
      RuleProofs.eo_requires_result_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    have hEmptyEq : x = __seq_empty (__eo_typeof x) :=
      RuleProofs.eo_requires_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    rw [hReqEq, hEmptyEq]
    exact str_is_compatible_seq_empty_typeof_right_ne_false
      (RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length)) x T hxTy

private theorem str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
    (x : Term) (T : SmtType) (wc : native_Char) (wcs : native_String)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s) :
    __str_is_compatible
        (RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length))
        (__str_flatten (__str_nary_intro x)) ≠
      Term.Boolean false := by
  have hIntroNe :
      __str_nary_intro x ≠ Term.Stuck :=
    str_nary_intro_ne_stuck_of_smt_type_seq x T hxTy
  rcases str_nary_intro_not_str_concat_cases_nil x hNotConcat hIntroNe with
    ⟨hIntroEq, _hXNil⟩ | ⟨empty, hIntroEq, _hEmptyNil⟩
  · rw [hIntroEq]
    exact str_is_compatible_full_word_flatten_non_concat_ne_false x T wc wcs
      hxTy hNotConcat
  · rw [hIntroEq]
    exact str_is_compatible_full_word_flatten_concat_raw_non_string_head_ne_false
      x empty T wc wcs hxTy hxNotString
      (by
        intro h t hEq
        exact hNotConcat ⟨h, t, hEq⟩)

private theorem str_is_empty_eval_unpack_nil_local
    (M : SmtModel) (e : Term) (s : SmtSeq)
    (hemp : __str_is_empty e = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt e) = SmtValue.Seq s) :
    native_unpack_seq s = [] := by
  unfold __str_is_empty at hemp
  split at hemp
  · exact Term.noConfusion hemp
  · rename_i U
    rw [show
      __eo_to_smt
          (Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U)) =
        __eo_to_smt_seq_empty
          (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U)) from rfl]
      at hev
    simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at hev
    split at hev
    · simp only [__eo_to_smt_seq_empty, __smtx_model_eval] at hev
      exact SmtValue.noConfusion hev
    · rw [show
          __eo_to_smt_seq_empty (SmtType.Seq (__eo_to_smt_type U)) =
            SmtTerm.seq_empty (__eo_to_smt_type U) from rfl,
        show
          __smtx_model_eval M (SmtTerm.seq_empty (__eo_to_smt_type U)) =
            SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) from by
              simp only [__smtx_model_eval]] at hev
      injection hev with hev
      rw [← hev]
      rfl
  · rw [show __eo_to_smt (Term.String []) = SmtTerm.String [] from rfl,
      show
        __smtx_model_eval M (SmtTerm.String []) =
          SmtValue.Seq (native_pack_string []) from by
            simp only [__smtx_model_eval]] at hev
    injection hev with hev
    rw [← hev]
    simp [native_pack_string, native_pack_seq, native_unpack_seq]
  · simp at hemp

private theorem str_is_compatible_full_word_flatten_rec_non_concat_ne_false
    (M : SmtModel) (x : Term) (T : SmtType) (sx : SmtSeq)
    (word : native_String) (acc : Term) (accVals suffixTail : List SmtValue)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hAlign :
      native_unpack_seq sx ++ accVals =
        word.map SmtValue.Char ++ suffixTail)
    (hNotConcat : ¬ ∃ h t : Term, x = mkConcat h t)
    (hFlatList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_flatten x) =
        Term.Boolean true)
    (hAccCompat :
      ∀ (word' : native_String) (suffixTail' : List SmtValue),
        accVals = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) acc ≠
            Term.Boolean false) :
    __str_is_compatible
        (RuleProofs.substrWord word 0 word.length)
        (__eo_list_concat_rec (__str_flatten x) acc) ≠
      Term.Boolean false := by
  rw [str_flatten_eq_default_of_not_str_concat x hNotConcat] at hFlatList ⊢
  by_cases hReq :
      __eo_requires x (__seq_empty (__eo_typeof x)) x = Term.Stuck
  · rw [hReq] at hFlatList
    simp [__eo_is_list] at hFlatList
  · have hReqEq :
        __eo_requires x (__seq_empty (__eo_typeof x)) x = x :=
      RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hReq
    have hEmptyEq : x = __seq_empty (__eo_typeof x) :=
      RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ hReq
    rw [hReqEq, hEmptyEq]
    rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
      (__seq_empty (__eo_typeof x)) acc
      (eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy)]
    apply hAccCompat word suffixTail
    have hEmpty : __str_is_empty x = Term.Boolean true := by
      rw [hEmptyEq]
      exact str_is_empty_seq_empty_typeof_of_seq x T hxTy
    have hUnpack := str_is_empty_eval_unpack_nil_local M x sx
      hEmpty hxEval
    simpa [hUnpack] using hAlign

private theorem str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ (x : Term) (T : SmtType) (sx : SmtSeq) (word : native_String)
      (acc : Term) (accVals suffixTail : List SmtValue),
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T →
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx →
      native_unpack_seq sx ++ accVals =
        word.map SmtValue.Char ++ suffixTail →
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_flatten x) =
        Term.Boolean true →
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true →
      (∀ (word' : native_String) (suffixTail' : List SmtValue),
        accVals = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) acc ≠
            Term.Boolean false) →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (__eo_list_concat_rec (__str_flatten x) acc) ≠
        Term.Boolean false
  | x, T, sx, [], acc, accVals, suffixTail, hxTy, hxEval, hAlign,
      hFlatList, hAccList, hAccCompat => by
      exact str_is_compatible_empty_left_ne_false
        (__eo_list_concat_rec (__str_flatten x) acc)
  | x, T, sx, wc :: wcs, acc, accVals, suffixTail, hxTy, hxEval, hAlign,
      hFlatList, hAccList, hAccCompat => by
      have hAccNe : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      cases x with
      | Apply f a =>
          cases f with
          | Apply g head =>
              cases g with
              | UOp op =>
                  by_cases hop : op = UserOp.str_concat
                  · subst op
                    rcases str_concat_args_of_seq_type head a T hxTy with
                      ⟨hHeadTy, hTailTy⟩
                    rcases mkConcat_args_eval_unpack_of_concat_eval M head a sx
                        hxEval with
                      ⟨sHead, sTail, hHeadEval, hTailEval, hUnpack⟩
                    by_cases hHeadString :
                        ∃ str : native_String, head = Term.String str
                    · rcases hHeadString with ⟨str, rfl⟩
                      have hHeadUnpack :
                          native_unpack_seq sHead = str.map SmtValue.Char :=
                        string_eval_unpack_eq M str sHead hHeadEval
                      have hAlignTail :
                          str.map SmtValue.Char ++
                              (native_unpack_seq sTail ++ accVals) =
                            (wc :: wcs).map SmtValue.Char ++ suffixTail := by
                        rw [hUnpack] at hAlign
                        rw [hHeadUnpack] at hAlign
                        simpa [List.append_assoc] using hAlign
                      rw [str_flatten_concat_string_eq str a] at hFlatList ⊢
                      rcases eo_list_concat_args_list_of_result_list_local
                          (RuleProofs.substrWord str 0 str.length)
                          (__str_flatten a) hFlatList with
                        ⟨hWordList, hTailFlatList⟩
                      have hTailAccList :
                          __eo_is_list (Term.UOp UserOp.str_concat)
                              (__eo_list_concat_rec (__str_flatten a) acc) =
                            Term.Boolean true :=
                        eo_list_concat_rec_is_list_true_of_lists
                          (Term.UOp UserOp.str_concat) (__str_flatten a) acc
                          hTailFlatList hAccList
                      have hConcatEq := eo_list_concat_eq_rec_of_lists_local
                        (RuleProofs.substrWord str 0 str.length)
                        (__str_flatten a) hWordList hTailFlatList
                      rw [hConcatEq]
                      rw [eo_list_concat_rec_assoc_local
                        (RuleProofs.substrWord str 0 str.length)
                        (__str_flatten a) acc hWordList hTailFlatList hAccNe]
                      rw [← eo_list_concat_eq_rec_of_lists_local
                        (RuleProofs.substrWord str 0 str.length)
                        (__eo_list_concat_rec (__str_flatten a) acc)
                        hWordList hTailAccList]
                      exact
                        str_is_compatible_substrWord_list_concat_ne_false
                          (wc :: wcs) str
                          (__eo_list_concat_rec (__str_flatten a) acc)
                          (native_unpack_seq sTail ++ accVals) suffixTail
                          hAlignTail
                          (by
                            intro word' suffixTail' hTailAlign
                            exact
                              str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
                                M hM a T sTail word' acc accVals suffixTail'
                                hTailTy hTailEval hTailAlign hTailFlatList
                                hAccList hAccCompat)
                    · by_cases hHeadStuck : head = Term.Stuck
                      · subst head
                        exact False.elim
                          (term_ne_stuck_of_smt_type_seq Term.Stuck T hHeadTy
                            rfl)
                      · have hHeadNe : head ≠ Term.Stuck := hHeadStuck
                        have hIsStr :
                            __eo_is_str head = Term.Boolean false :=
                          eo_is_str_false_of_not_string_ne_stuck head
                            hHeadString hHeadNe
                        by_cases hHeadConcat :
                            ∃ h t : Term, head = mkConcat h t
                        · rcases hHeadConcat with ⟨h, t, rfl⟩
                          rw [__str_flatten.eq_2 h t a] at hFlatList ⊢
                          rcases eo_list_concat_args_list_of_result_list_local
                              (__str_flatten (mkConcat h t)) (__str_flatten a)
                              hFlatList with
                            ⟨hHeadFlatList, hTailFlatList⟩
                          have hTailAccList :
                              __eo_is_list (Term.UOp UserOp.str_concat)
                                  (__eo_list_concat_rec (__str_flatten a) acc) =
                                Term.Boolean true :=
                            eo_list_concat_rec_is_list_true_of_lists
                              (Term.UOp UserOp.str_concat) (__str_flatten a) acc
                              hTailFlatList hAccList
                          have hConcatEq := eo_list_concat_eq_rec_of_lists_local
                            (__str_flatten (mkConcat h t)) (__str_flatten a)
                            hHeadFlatList hTailFlatList
                          rw [hConcatEq]
                          rw [eo_list_concat_rec_assoc_local
                            (__str_flatten (mkConcat h t)) (__str_flatten a) acc
                            hHeadFlatList hTailFlatList hAccNe]
                          have hHeadAlign :
                              native_unpack_seq sHead ++
                                  (native_unpack_seq sTail ++ accVals) =
                                (wc :: wcs).map SmtValue.Char ++ suffixTail := by
                            rw [hUnpack] at hAlign
                            simpa [List.append_assoc] using hAlign
                          exact
                            str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
                              M hM (mkConcat h t) T sHead (wc :: wcs)
                              (__eo_list_concat_rec (__str_flatten a) acc)
                              (native_unpack_seq sTail ++ accVals) suffixTail
                              hHeadTy hHeadEval hHeadAlign hHeadFlatList
                              hTailAccList
                              (by
                                intro word' suffixTail' hTailAlign
                                exact
                                  str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
                                    M hM a T sTail word' acc accVals suffixTail'
                                    hTailTy hTailEval hTailAlign hTailFlatList
                                    hAccList hAccCompat)
                        · have hHeadNotConcat :
                              ∀ h t : Term, head ≠ mkConcat h t := by
                            intro h t hEq
                            exact hHeadConcat ⟨h, t, hEq⟩
                          rw [__str_flatten.eq_3 head a hHeadNotConcat,
                            hIsStr, eo_ite_false] at hFlatList ⊢
                          have hTailFlatNe : __str_flatten a ≠ Term.Stuck := by
                            intro h
                            rw [h] at hFlatList
                            simp [__eo_mk_apply, __eo_is_list] at hFlatList
                          have hApply :
                              __eo_mk_apply
                                  (Term.Apply (Term.UOp UserOp.str_concat) head)
                                  (__str_flatten a) =
                                mkConcat head (__str_flatten a) := by
                            cases hTail : __str_flatten a <;>
                              simp [__eo_mk_apply, mkConcat, hTail] at hTailFlatNe ⊢
                          rw [hApply] at hFlatList ⊢
                          have hTailFlatList :
                              __eo_is_list (Term.UOp UserOp.str_concat)
                                  (__str_flatten a) = Term.Boolean true :=
                            eo_is_list_tail_true_of_cons_self
                              (Term.UOp UserOp.str_concat) head (__str_flatten a)
                              hFlatList
                          have hTailAccNe :
                              __eo_list_concat_rec (__str_flatten a) acc ≠
                                Term.Stuck :=
                            eo_list_concat_rec_ne_stuck_of_list
                              (Term.UOp UserOp.str_concat) (__str_flatten a) acc
                              hTailFlatList hAccNe
                          rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
                            head (__str_flatten a) acc hTailAccNe]
                          exact
                            str_is_compatible_word_mkConcat_non_string_head_ne_false
                              wc wcs head
                              (__eo_list_concat_rec (__str_flatten a) acc)
                              hHeadString
                  · exact
                      str_is_compatible_full_word_flatten_rec_non_concat_ne_false
                        M (Term.Apply
                          (Term.Apply (Term.UOp op) head) a) T sx
                        (wc :: wcs) acc accVals suffixTail hxTy hxEval hAlign
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          simp [mkConcat] at hEq
                          exact hop hEq.1.1)
                        hFlatList hAccCompat
              | _ =>
                  exact
                    str_is_compatible_full_word_flatten_rec_non_concat_ne_false
                      M _ T sx
                      (wc :: wcs) acc accVals suffixTail hxTy hxEval hAlign
                      (by
                        intro h
                        rcases h with ⟨cHead, cTail, hEq⟩
                        cases hEq)
                      hFlatList hAccCompat
          | _ =>
              exact
                str_is_compatible_full_word_flatten_rec_non_concat_ne_false
                  M _ T sx (wc :: wcs) acc accVals suffixTail hxTy hxEval
                  hAlign
                  (by
                    intro h
                    rcases h with ⟨cHead, cTail, hEq⟩
                    cases hEq)
                  hFlatList hAccCompat
      | _ =>
          exact
            str_is_compatible_full_word_flatten_rec_non_concat_ne_false
              M _ T sx (wc :: wcs) acc accVals suffixTail hxTy hxEval hAlign
              (by
                intro h
                rcases h with ⟨cHead, cTail, hEq⟩
                cases hEq)
              hFlatList hAccCompat
termination_by x => sizeOf x

private theorem str_is_compatible_full_word_flatten_ne_false_of_append_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ (x : Term) (T : SmtType) (sx : SmtSeq) (word : native_String)
      (xTail suffixTail : List SmtValue),
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T →
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx →
      native_unpack_seq sx ++ xTail =
        word.map SmtValue.Char ++ suffixTail →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (__str_flatten x) ≠
        Term.Boolean false
  | x, T, sx, [], xTail, suffixTail, hxTy, hxEval, hAlign => by
      exact str_is_compatible_empty_left_ne_false (__str_flatten x)
  | x, T, sx, wc :: wcs, xTail, suffixTail, hxTy, hxEval, hAlign => by
      cases x with
      | Apply f a =>
          cases f with
          | Apply g head =>
              cases g with
              | UOp op =>
                  by_cases hop : op = UserOp.str_concat
                  · subst op
                    rcases str_concat_args_of_seq_type head a T hxTy with
                      ⟨hHeadTy, hTailTy⟩
                    rcases mkConcat_args_eval_unpack_of_concat_eval M head a sx
                        hxEval with
                      ⟨sHead, sTail, hHeadEval, hTailEval, hUnpack⟩
                    by_cases hHeadString :
                        ∃ str : native_String, head = Term.String str
                    · rcases hHeadString with ⟨str, rfl⟩
                      have hHeadUnpack :
                          native_unpack_seq sHead = str.map SmtValue.Char :=
                        string_eval_unpack_eq M str sHead hHeadEval
                      have hAlignTail :
                          str.map SmtValue.Char ++
                              (native_unpack_seq sTail ++ xTail) =
                            (wc :: wcs).map SmtValue.Char ++ suffixTail := by
                        rw [hUnpack] at hAlign
                        rw [hHeadUnpack] at hAlign
                        simpa [List.append_assoc] using hAlign
                      rw [str_flatten_concat_string_eq str a]
                      exact
                        str_is_compatible_substrWord_list_concat_ne_false
                          (wc :: wcs) str (__str_flatten a)
                          (native_unpack_seq sTail ++ xTail) suffixTail
                          hAlignTail
                          (by
                            intro word' suffixTail' hTailAlign
                            exact
                              str_is_compatible_full_word_flatten_ne_false_of_append_eval
                                M hM a T sTail word' xTail suffixTail'
                                hTailTy hTailEval hTailAlign)
                    · by_cases hHeadStuck : head = Term.Stuck
                      · subst head
                        exact False.elim
                          (term_ne_stuck_of_smt_type_seq Term.Stuck T hHeadTy
                            rfl)
                      · by_cases hHeadConcat :
                            ∃ h t : Term, head = mkConcat h t
                        · rcases hHeadConcat with ⟨h, t, rfl⟩
                          have hHeadAlign :
                              native_unpack_seq sHead ++
                                  (native_unpack_seq sTail ++ xTail) =
                                (wc :: wcs).map SmtValue.Char ++ suffixTail := by
                            rw [hUnpack] at hAlign
                            simpa [List.append_assoc] using hAlign
                          by_cases hHeadFlatList :
                              __eo_is_list (Term.UOp UserOp.str_concat)
                                  (__str_flatten (mkConcat h t)) =
                                Term.Boolean true
                          · by_cases hTailFlatList :
                                __eo_is_list (Term.UOp UserOp.str_concat)
                                    (__str_flatten a) = Term.Boolean true
                            · rw [__str_flatten.eq_2 h t a]
                              rw [eo_list_concat_eq_rec_of_lists_local
                                (__str_flatten (mkConcat h t))
                                (__str_flatten a) hHeadFlatList hTailFlatList]
                              exact
                                str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
                                  M hM (mkConcat h t) T sHead (wc :: wcs)
                                  (__str_flatten a)
                                  (native_unpack_seq sTail ++ xTail) suffixTail
                                  hHeadTy hHeadEval hHeadAlign hHeadFlatList
                                  hTailFlatList
                                  (by
                                    intro word' suffixTail' hTailAlign
                                    exact
                                      str_is_compatible_full_word_flatten_ne_false_of_append_eval
                                        M hM a T sTail word' xTail suffixTail'
                                        hTailTy hTailEval hTailAlign)
                            · have hConcatStuck :
                                  __eo_list_concat (Term.UOp UserOp.str_concat)
                                      (__str_flatten (mkConcat h t))
                                      (__str_flatten a) = Term.Stuck := by
                                simp [__eo_list_concat, hTailFlatList,
                                  __eo_requires, native_teq, native_ite,
                                  SmtEval.native_not]
                              rw [__str_flatten.eq_2 h t a, hConcatStuck]
                              change
                                __str_is_compatible
                                    (mkConcat (Term.String [wc])
                                      (RuleProofs.substrWord wcs 0 wcs.length))
                                    Term.Stuck ≠ Term.Boolean false
                              simp [__str_is_compatible]
                          · have hConcatStuck :
                                __eo_list_concat (Term.UOp UserOp.str_concat)
                                    (__str_flatten (mkConcat h t))
                                    (__str_flatten a) = Term.Stuck := by
                              simp [__eo_list_concat, hHeadFlatList,
                                __eo_requires, native_teq, native_ite]
                            rw [__str_flatten.eq_2 h t a, hConcatStuck]
                            change
                              __str_is_compatible
                                  (mkConcat (Term.String [wc])
                                    (RuleProofs.substrWord wcs 0 wcs.length))
                                  Term.Stuck ≠ Term.Boolean false
                            simp [__str_is_compatible]
                        · have hHeadNotConcat :
                              ∀ h t : Term, head ≠ mkConcat h t := by
                            intro h t hEq
                            exact hHeadConcat ⟨h, t, hEq⟩
                          exact
                            str_is_compatible_full_word_flatten_concat_raw_non_string_head_ne_false
                              head a T wc wcs hHeadTy hHeadString hHeadNotConcat
                  · exact
                      str_is_compatible_full_word_flatten_non_concat_ne_false
                        (Term.Apply (Term.Apply (Term.UOp op) head) a) T wc
                        wcs hxTy
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          simp [mkConcat] at hEq
                          exact hop hEq.1.1)
              | _ =>
                  exact
                    str_is_compatible_full_word_flatten_non_concat_ne_false
                      _ T wc wcs hxTy
                      (by
                        intro h
                        rcases h with ⟨cHead, cTail, hEq⟩
                        cases hEq)
          | _ =>
              exact
                str_is_compatible_full_word_flatten_non_concat_ne_false
                  _ T wc wcs hxTy
                  (by
                    intro h
                    rcases h with ⟨cHead, cTail, hEq⟩
                    cases hEq)
      | _ =>
          exact
            str_is_compatible_full_word_flatten_non_concat_ne_false
              _ T wc wcs hxTy
              (by
                intro h
                rcases h with ⟨head, tail, hEq⟩
                cases hEq)

private theorem str_flatten_seq_empty_seq_of_type_eq
    (U : Term)
    (hUType : __eo_typeof U = Term.Type) :
    __str_flatten (__seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
      __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) := by
  by_cases hChar : U = Term.UOp UserOp.Char
  · subst U
    change __str_flatten (Term.String []) = Term.String []
    change __eo_requires (Term.String [])
      (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
      Term.String []
    change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
      Term.String []
    exact eo_requires_self_eq_of_ne_stuck (Term.String []) (Term.String [])
      (by intro h; cases h)
  · have hSeqEmpty :
        __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.UOp1 UserOp1.seq_empty
            (Term.Apply (Term.UOp UserOp.Seq) U) := by
      cases U <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        exact False.elim (hChar rfl)
    rw [hSeqEmpty]
    let empty :=
      Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)
    have hEmptyNe : empty ≠ Term.Stuck := by
      dsimp [empty]
      intro h
      cases h
    have hTypeEmpty :
        __eo_typeof empty = Term.Apply (Term.UOp UserOp.Seq) U := by
      dsimp [empty]
      change
        __eo_typeof_seq_empty
            (__eo_typeof (Term.Apply (Term.UOp UserOp.Seq) U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.UOp UserOp.Seq) U
      change
        __eo_typeof_seq_empty (__eo_typeof_Seq (__eo_typeof U))
            (Term.Apply (Term.UOp UserOp.Seq) U) =
          Term.Apply (Term.UOp UserOp.Seq) U
      rw [hUType]
      rfl
    change __str_flatten empty = empty
    change __eo_requires empty (__seq_empty (__eo_typeof empty)) empty = empty
    rw [hTypeEmpty]
    have hSeqEmpty' :
        __seq_empty (Term.Apply (Term.UOp UserOp.Seq) U) = empty := by
      exact hSeqEmpty
    rw [hSeqEmpty']
    exact eo_requires_self_eq_of_ne_stuck empty empty hEmptyNe

private theorem str_flatten_seq_empty_typeof_eq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __str_flatten (__seq_empty (__eo_typeof x)) =
      __seq_empty (__eo_typeof x) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rcases TranslationProofs.eo_to_smt_type_eq_seq hA with
    ⟨U, hType, hU⟩
  have hSeqWF :
      __smtx_type_wf (SmtType.Seq T) = true :=
    smt_term_seq_type_wf_of_non_none (__eo_to_smt x) hTrans hxTy
  have hSeqComp :
      __smtx_type_wf_component (SmtType.Seq T) = true := by
    simpa [__smtx_type_wf] using hSeqWF
  have hSeqRec :
      __smtx_type_wf_rec (SmtType.Seq T) = true :=
    (smtx_type_wf_component_parts hSeqComp).2
  have hTParts :
      native_inhabited_type T = true ∧
        __smtx_type_wf_rec T = true := by
    simpa [__smtx_type_wf_rec, native_and] using hSeqRec
  have hTRec : __smtx_type_wf_rec T = true :=
    hTParts.2
  have hUType : __eo_typeof U = Term.Type :=
    TranslationProofs.eo_typeof_type_of_smt_type_wf_rec U (by
      rw [hU]
      exact hTRec)
  rw [hType]
  exact str_flatten_seq_empty_seq_of_type_eq U hUType

private theorem str_nary_intro_eq_singleton_of_is_list_false_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean false) :
    __str_nary_intro x = mkConcat x (__seq_empty (__eo_typeof x)) := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  have hTy :
      __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  let empty := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)
  have hEmptyEq : empty = __seq_empty (__eo_typeof x) := by
    simpa [empty] using strConcat_nil_eq_seq_empty_of_type hTy
  have hEmptyNe : empty ≠ Term.Stuck := by
    rw [hEmptyEq]
    exact seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  have hEmptyList :
      __eo_is_list (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    rw [hEmptyEq]
    exact eo_is_list_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
      (seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy)
  have hSeqEmptyList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__seq_empty (__eo_typeof x)) =
        Term.Boolean true := by
    simpa [← hEmptyEq] using hEmptyList
  have hApplyNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty ≠
        Term.Stuck := by
    cases hEmptyCases : empty <;>
      simp [__eo_mk_apply, hEmptyCases] at hEmptyNe ⊢
  have hApplyEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty =
        mkConcat x empty :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNe
  have hApplySeq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
        mkConcat x (__seq_empty (__eo_typeof x)) := by
    simpa [← hEmptyEq] using hApplyEq
  change
    __eo_ite (__eo_is_list (Term.UOp UserOp.str_concat) x) x
        (__eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) empty)
          (Term.Boolean true)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty)) =
      mkConcat x (__seq_empty (__eo_typeof x))
  rw [hList, eo_ite_false]
  rw [hEmptyList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
    (by decide)]
  rw [hApplyEq, hEmptyEq]

private theorem eo_list_rev_str_flatten_intro_non_concat_non_string_eq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__str_nary_intro x)) =
      __str_flatten (__str_nary_intro x) := by
  have hIntroNe :
      __str_nary_intro x ≠ Term.Stuck :=
    str_nary_intro_ne_stuck_of_smt_type_seq x T hxTy
  have hxNe : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntroNe with hIntroEq | ⟨hIntroEq, hEmptyNil⟩
  · rw [hIntroEq, str_flatten_eq_default_of_not_str_concat x hNotConcat]
    by_cases hReq :
        __eo_requires x (__seq_empty (__eo_typeof x)) x = Term.Stuck
    · rw [hReq]
      simp [__eo_list_rev, __eo_is_list, __eo_requires, native_teq,
        native_ite]
    · have hReqEq :
          __eo_requires x (__seq_empty (__eo_typeof x)) x = x :=
        RuleProofs.eo_requires_result_eq_of_ne_stuck x
          (__seq_empty (__eo_typeof x)) x hReq
      have hEmptyEq : x = __seq_empty (__eo_typeof x) :=
        RuleProofs.eo_requires_eq_of_ne_stuck x
          (__seq_empty (__eo_typeof x)) x hReq
      have hEmptyNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat)
              (__seq_empty (__eo_typeof x)) =
            Term.Boolean true :=
        eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy
      rw [hReqEq, hEmptyEq]
      exact eo_list_rev_str_concat_nil_eq_of_nil_true
        (__seq_empty (__eo_typeof x)) hEmptyNil
  · rw [hIntroEq]
    have hIsStr : __eo_is_str x = Term.Boolean false :=
      eo_is_str_false_of_not_string_ne_stuck x hxNotString hxNe
    have hFlatEmpty :
        __str_flatten (__seq_empty (__eo_typeof x)) =
          __seq_empty (__eo_typeof x) :=
      str_flatten_seq_empty_typeof_eq x T hxTy
    have hEmptyNe :
        __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
      term_ne_stuck_of_eo_is_list_nil_true (Term.UOp UserOp.str_concat)
        (__seq_empty (__eo_typeof x)) hEmptyNil
    have hApply :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)) =
          mkConcat x (__seq_empty (__eo_typeof x)) := by
      cases hEmpty : __seq_empty (__eo_typeof x) <;>
        simp [__eo_mk_apply, hEmpty] at hEmptyNe ⊢
    have hEmptyList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true :=
      eo_is_list_str_concat_nil_true_of_nil_true
        (__seq_empty (__eo_typeof x)) hEmptyNil
    have hConsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (mkConcat x (__seq_empty (__eo_typeof x))) =
          Term.Boolean true :=
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.str_concat) x (__seq_empty (__eo_typeof x))
        (by decide) hEmptyList
    have hRevCons :
        __eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck :=
      eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
        (mkConcat x (__seq_empty (__eo_typeof x))) hConsList
    have hXNotConcat : ∀ h t : Term, x ≠ mkConcat h t := by
      intro h t hEq
      exact hNotConcat ⟨h, t, hEq⟩
    rw [__str_flatten.eq_3 x (__seq_empty (__eo_typeof x)) hXNotConcat,
      hIsStr, eo_ite_false, hFlatEmpty, hApply]
    exact eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck x
      (__seq_empty (__eo_typeof x)) hEmptyNil hRevCons

private theorem str_is_compatible_rev_word_flatten_intro_non_concat_non_string_ne_false
    (x : Term) (T : SmtType) (wc : native_Char) (wcs : native_String)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hxNotString : ¬ ∃ s : native_String, x = Term.String s) :
    __str_is_compatible
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord (wc :: wcs) 0 ((wc :: wcs).length)))
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro x))) ≠
      Term.Boolean false := by
  rw [eo_list_rev_substrWord_local (wc :: wcs)]
  rw [eo_list_rev_str_flatten_intro_non_concat_non_string_eq x T hxTy
    hNotConcat hxNotString]
  cases hRevWord : (wc :: wcs).reverse with
  | nil =>
      have hLen := congrArg List.length hRevWord
      simp at hLen
  | cons rc rcs =>
      exact
        str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
          x T rc rcs hxTy hNotConcat hxNotString

private theorem str_is_compatible_rev_rec_flatten_non_concat_ne_false_of_append_eval
    (M : SmtModel) (x : Term) (T : SmtType) (sx : SmtSeq)
    (word : native_String) (acc : Term)
    (accVals suffixTail : List SmtValue)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hAlign :
      (native_unpack_seq sx).reverse ++ accVals =
        word.map SmtValue.Char ++ suffixTail)
    (hAccCompat :
      ∀ (word' : native_String) (suffixTail' : List SmtValue),
        accVals = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) acc ≠
            Term.Boolean false)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_is_compatible
        (RuleProofs.substrWord word 0 word.length)
        (__eo_list_rev_rec (__str_flatten x) acc) ≠
      Term.Boolean false := by
  rw [str_flatten_eq_default_of_not_str_concat x hNotConcat]
  by_cases hReq :
      __eo_requires x (__seq_empty (__eo_typeof x)) x = Term.Stuck
  · rw [hReq]
    have hRight :
        __eo_list_rev_rec Term.Stuck acc = Term.Stuck := by
      rfl
    rw [hRight]
    cases hLeft : RuleProofs.substrWord word 0 word.length <;>
      simp [__str_is_compatible]
  · have hReqEq :
        __eo_requires x (__seq_empty (__eo_typeof x)) x = x :=
      RuleProofs.eo_requires_result_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    have hEmptyEq : x = __seq_empty (__eo_typeof x) :=
      RuleProofs.eo_requires_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    rw [hReqEq, hEmptyEq]
    have hEmptyEval := eval_seq_empty_typeof M x T hxTy
    rw [hEmptyEq] at hxEval
    rw [hEmptyEval] at hxEval
    injection hxEval with hsx
    subst sx
    have hAccAlign :
        accVals = word.map SmtValue.Char ++ suffixTail := by
      simpa [native_unpack_seq] using hAlign
    have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy
    rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true
      (__seq_empty (__eo_typeof x)) acc hNil]
    exact hAccCompat word suffixTail hAccAlign

private theorem str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
    (M : SmtModel) :
    ∀ (x : Term) (T : SmtType) (sx : SmtSeq) (word : native_String)
      (acc : Term) (accVals suffixTail : List SmtValue),
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T →
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx →
      (native_unpack_seq sx).reverse ++ accVals =
        word.map SmtValue.Char ++ suffixTail →
      (∀ (word' : native_String) (suffixTail' : List SmtValue),
        accVals = word'.map SmtValue.Char ++ suffixTail' →
          __str_is_compatible
              (RuleProofs.substrWord word' 0 word'.length) acc ≠
            Term.Boolean false) →
      __str_is_compatible
          (RuleProofs.substrWord word 0 word.length)
          (__eo_list_rev_rec (__str_flatten x) acc) ≠
        Term.Boolean false
  | x, T, sx, [], acc, accVals, suffixTail, hxTy, hxEval, hAlign,
      hAccCompat => by
      exact str_is_compatible_empty_left_ne_false
        (__eo_list_rev_rec (__str_flatten x) acc)
  | x, T, sx, wc :: wcs, acc, accVals, suffixTail, hxTy, hxEval, hAlign,
      hAccCompat => by
      by_cases hAccNe : acc ≠ Term.Stuck
      · cases x with
        | String str =>
            cases str with
            | nil =>
                have hStr :
                    native_unpack_seq sx = [] :=
                  string_eval_unpack_eq M [] sx hxEval
                have hAccAlign :
                    accVals =
                      (wc :: wcs).map SmtValue.Char ++ suffixTail := by
                  simpa [hStr] using hAlign
                change
                  __str_is_compatible
                      (RuleProofs.substrWord (wc :: wcs) 0
                        (wc :: wcs).length)
                      (__eo_list_rev_rec (Term.String []) acc) ≠
                    Term.Boolean false
                have hNil :
                    __eo_is_list_nil (Term.UOp UserOp.str_concat)
                        (Term.String []) =
                      Term.Boolean true := by
                  simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                    __eo_eq]
                  change decide (Term.String [] = Term.String []) = true
                  simp
                rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true
                  (Term.String []) acc hNil]
                exact hAccCompat (wc :: wcs) suffixTail hAccAlign
            | cons c cs =>
                have hFlat :
                    __str_flatten (Term.String (c :: cs)) = Term.Stuck := by
                  change
                    __eo_requires (Term.String (c :: cs)) (Term.String [])
                        (Term.String (c :: cs)) =
                      Term.Stuck
                  simp [__eo_requires, native_teq, native_ite]
                rw [hFlat]
                change
                  __str_is_compatible
                      (RuleProofs.substrWord (wc :: wcs) 0
                        (wc :: wcs).length)
                      Term.Stuck ≠
                    Term.Boolean false
                cases hLeft :
                    RuleProofs.substrWord (wc :: wcs) 0
                      (wc :: wcs).length <;>
                  simp [__str_is_compatible]
        | Stuck =>
            exact False.elim
              (term_ne_stuck_of_smt_type_seq Term.Stuck T hxTy rfl)
        | Apply f a =>
            cases f with
            | Apply g head =>
                cases g with
                | UOp op =>
                    by_cases hop : op = UserOp.str_concat
                    · subst op
                      rcases str_concat_args_of_seq_type head a T hxTy with
                        ⟨hHeadTy, hTailTy⟩
                      rcases mkConcat_args_eval_unpack_of_concat_eval M head a
                          sx hxEval with
                        ⟨sHead, sTail, hHeadEval, hTailEval, hUnpack⟩
                      by_cases hHeadString :
                          ∃ str : native_String, head = Term.String str
                      · rcases hHeadString with ⟨str, rfl⟩
                        have hHeadUnpack :
                            native_unpack_seq sHead =
                              str.map SmtValue.Char :=
                          string_eval_unpack_eq M str sHead hHeadEval
                        have hAlignTail :
                            (native_unpack_seq sTail).reverse ++
                                (str.reverse.map SmtValue.Char ++ accVals) =
                              (wc :: wcs).map SmtValue.Char ++
                                suffixTail := by
                          rw [hUnpack] at hAlign
                          rw [hHeadUnpack] at hAlign
                          simpa [List.reverse_append, List.map_reverse,
                            List.append_assoc] using hAlign
                        rw [str_flatten_concat_string_eq str a]
                        by_cases hTailList :
                            __eo_is_list (Term.UOp UserOp.str_concat)
                                (__str_flatten a) =
                              Term.Boolean true
                        · rw [eo_list_concat_substrWord_eq_rec_of_tail_list
                            str (__str_flatten a) hTailList]
                          rw [eo_list_rev_rec_list_concat_rec_substrWord_eq
                            str (__str_flatten a) acc hTailList hAccNe]
                          exact
                            str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                              M a T sTail (wc :: wcs)
                              (__eo_list_rev_rec
                                (RuleProofs.substrWord str 0 str.length) acc)
                              (str.reverse.map SmtValue.Char ++ accVals)
                              suffixTail hTailTy hTailEval hAlignTail
                              (by
                                intro word' suffixTail' hAccAlign
                                exact
                                  str_is_compatible_substrWord_rev_rec_substrWord_acc_ne_false
                                    word' str acc accVals suffixTail'
                                    hAccAlign hAccCompat)
                        · rw [eo_list_concat_substrWord_eq_stuck_of_tail_not_list
                            str (__str_flatten a) hTailList]
                          change
                            __str_is_compatible
                                (RuleProofs.substrWord (wc :: wcs) 0
                                  (wc :: wcs).length)
                                Term.Stuck ≠
                              Term.Boolean false
                          cases hLeft :
                              RuleProofs.substrWord (wc :: wcs) 0
                                (wc :: wcs).length <;>
                            simp [__str_is_compatible]
                      · by_cases hHeadStuck : head = Term.Stuck
                        · subst head
                          exact False.elim
                            (term_ne_stuck_of_smt_type_seq Term.Stuck T
                              hHeadTy rfl)
                        · have hHeadNe : head ≠ Term.Stuck := hHeadStuck
                          have hIsStr :
                              __eo_is_str head = Term.Boolean false :=
                            eo_is_str_false_of_not_string_ne_stuck head
                              hHeadString hHeadNe
                          have hAlignTail :
                              (native_unpack_seq sTail).reverse ++
                                  ((native_unpack_seq sHead).reverse ++
                                    accVals) =
                                (wc :: wcs).map SmtValue.Char ++
                                  suffixTail := by
                            rw [hUnpack] at hAlign
                            simpa [List.reverse_append, List.append_assoc]
                              using hAlign
                          by_cases hHeadConcat :
                              ∃ h t : Term, head = mkConcat h t
                          · rcases hHeadConcat with ⟨h, t, rfl⟩
                            by_cases hHeadFlatList :
                                __eo_is_list (Term.UOp UserOp.str_concat)
                                    (__str_flatten (mkConcat h t)) =
                                  Term.Boolean true
                            · by_cases hTailFlatList :
                                  __eo_is_list (Term.UOp UserOp.str_concat)
                                      (__str_flatten a) = Term.Boolean true
                              · rw [__str_flatten.eq_2 h t a]
                                rw [eo_list_concat_eq_rec_of_lists_local
                                  (__str_flatten (mkConcat h t))
                                  (__str_flatten a) hHeadFlatList
                                  hTailFlatList]
                                rw [eo_list_rev_rec_concat_rec_local
                                  (__str_flatten (mkConcat h t))
                                  (__str_flatten a) acc hHeadFlatList
                                  hTailFlatList hAccNe]
                                exact
                                  str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                                    M a T sTail (wc :: wcs)
                                    (__eo_list_rev_rec
                                      (__str_flatten (mkConcat h t)) acc)
                                    ((native_unpack_seq sHead).reverse ++
                                      accVals)
                                    suffixTail hTailTy hTailEval hAlignTail
                                    (by
                                      intro word' suffixTail' hHeadAlign
                                      exact
                                        str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                                          M (mkConcat h t) T sHead word' acc
                                          accVals suffixTail' hHeadTy hHeadEval
                                          hHeadAlign hAccCompat)
                              · have hConcatStuck :
                                    __eo_list_concat
                                        (Term.UOp UserOp.str_concat)
                                        (__str_flatten (mkConcat h t))
                                        (__str_flatten a) = Term.Stuck := by
                                  simp [__eo_list_concat, hTailFlatList,
                                    __eo_requires, native_teq, native_ite]
                                rw [__str_flatten.eq_2 h t a, hConcatStuck]
                                change
                                  __str_is_compatible
                                      (RuleProofs.substrWord (wc :: wcs) 0
                                        (wc :: wcs).length)
                                      Term.Stuck ≠ Term.Boolean false
                                cases hLeft :
                                    RuleProofs.substrWord (wc :: wcs) 0
                                      (wc :: wcs).length <;>
                                  simp [__str_is_compatible]
                            · have hConcatStuck :
                                  __eo_list_concat (Term.UOp UserOp.str_concat)
                                      (__str_flatten (mkConcat h t))
                                      (__str_flatten a) = Term.Stuck := by
                                simp [__eo_list_concat, hHeadFlatList,
                                  __eo_requires, native_teq, native_ite]
                              rw [__str_flatten.eq_2 h t a, hConcatStuck]
                              change
                                __str_is_compatible
                                    (RuleProofs.substrWord (wc :: wcs) 0
                                      (wc :: wcs).length)
                                    Term.Stuck ≠ Term.Boolean false
                              cases hLeft :
                                  RuleProofs.substrWord (wc :: wcs) 0
                                    (wc :: wcs).length <;>
                                simp [__str_is_compatible]
                          · have hHeadNotConcat :
                                ∀ h t : Term, head ≠ mkConcat h t := by
                              intro h t hEq
                              exact hHeadConcat ⟨h, t, hEq⟩
                            rw [__str_flatten.eq_3 head a hHeadNotConcat,
                              hIsStr, eo_ite_false]
                            by_cases hTailStuck :
                                __str_flatten a = Term.Stuck
                            · rw [hTailStuck]
                              simp [__eo_mk_apply]
                              change
                                __str_is_compatible
                                    (RuleProofs.substrWord (wc :: wcs) 0
                                      (wc :: wcs).length)
                                    Term.Stuck ≠
                                  Term.Boolean false
                              cases hLeft :
                                  RuleProofs.substrWord (wc :: wcs) 0
                                    (wc :: wcs).length <;>
                                simp [__str_is_compatible]
                            · have hApply :
                                __eo_mk_apply
                                    (Term.Apply
                                      (Term.UOp UserOp.str_concat) head)
                                    (__str_flatten a) =
                                  mkConcat head (__str_flatten a) := by
                                cases hTail : __str_flatten a <;>
                                  simp [hTail] at hTailStuck
                                all_goals
                                  simp [__eo_mk_apply, mkConcat]
                              rw [hApply]
                              rw [eo_list_rev_rec_cons
                                (Term.UOp UserOp.str_concat) head
                                (__str_flatten a) acc hAccNe]
                              exact
                                str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                                  M a T sTail (wc :: wcs)
                                  (mkConcat head acc)
                                  ((native_unpack_seq sHead).reverse ++
                                    accVals)
                                  suffixTail hTailTy hTailEval hAlignTail
                                  (by
                                    intro word' suffixTail' hAccAlign
                                    cases word' with
                                    | nil =>
                                        exact
                                          str_is_compatible_empty_left_ne_false
                                            (mkConcat head acc)
                                    | cons dc dcs =>
                                        exact
                                          str_is_compatible_word_mkConcat_non_string_head_ne_false
                                            dc dcs head acc hHeadString)
                    · exact
                        str_is_compatible_rev_rec_flatten_non_concat_ne_false_of_append_eval
                          M (Term.Apply (Term.Apply (Term.UOp op) head) a)
                          T sx (wc :: wcs) acc accVals suffixTail hxTy hxEval
                          hAlign hAccCompat
                          (by
                            intro h
                            rcases h with ⟨cHead, cTail, hEq⟩
                            simp [mkConcat] at hEq
                            exact hop hEq.1.1)
                | _ =>
                    exact
                      str_is_compatible_rev_rec_flatten_non_concat_ne_false_of_append_eval
                        M _ T sx
                        (wc :: wcs) acc accVals suffixTail hxTy hxEval
                        hAlign hAccCompat
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          cases hEq)
            | _ =>
                exact
                  str_is_compatible_rev_rec_flatten_non_concat_ne_false_of_append_eval
                    M _ T sx (wc :: wcs) acc accVals
                    suffixTail hxTy hxEval hAlign hAccCompat
                    (by
                      intro h
                      rcases h with ⟨cHead, cTail, hEq⟩
                      cases hEq)
        | _ =>
            exact
              str_is_compatible_rev_rec_flatten_non_concat_ne_false_of_append_eval
                M _ T sx (wc :: wcs) acc accVals suffixTail hxTy hxEval
                hAlign hAccCompat
                (by
                  intro h
                  rcases h with ⟨cHead, cTail, hEq⟩
                  cases hEq)
      · have hAcc : acc = Term.Stuck := by
          by_cases h : acc = Term.Stuck
          · exact h
          · exact False.elim (hAccNe h)
        rw [hAcc]
        have hRight :
            __eo_list_rev_rec (__str_flatten x) Term.Stuck = Term.Stuck := by
          cases hFlat : __str_flatten x <;> rfl
        rw [hRight]
        cases hLeft :
            RuleProofs.substrWord (wc :: wcs) 0 (wc :: wcs).length <;>
          simp [__str_is_compatible]

private theorem str_flatten_get_nil_empty_non_concat_of_seq_if_list
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_flatten x) =
        Term.Boolean true) :
    __str_is_empty
        (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (__str_flatten x)) =
      Term.Boolean true := by
  rw [str_flatten_eq_default_of_not_str_concat x hNotConcat] at hList ⊢
  by_cases hReq :
      __eo_requires x (__seq_empty (__eo_typeof x)) x = Term.Stuck
  · rw [hReq] at hList
    simp [__eo_is_list] at hList
  · have hReqEq :
        __eo_requires x (__seq_empty (__eo_typeof x)) x = x :=
      RuleProofs.eo_requires_result_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    have hEmptyEq : x = __seq_empty (__eo_typeof x) :=
      RuleProofs.eo_requires_eq_of_ne_stuck x
        (__seq_empty (__eo_typeof x)) x hReq
    rw [hReqEq, hEmptyEq]
    have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy
    rw [eo_get_nil_rec_str_concat_eq_of_nil_true
      (__seq_empty (__eo_typeof x)) hNil]
    exact str_is_empty_seq_empty_typeof_of_seq x T hxTy

private theorem str_flatten_get_nil_empty_of_seq_if_list :
    ∀ (x : Term) (T : SmtType),
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T →
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_flatten x) =
        Term.Boolean true →
      __str_is_empty
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (__str_flatten x)) =
        Term.Boolean true
  | x, T, hxTy, hList => by
      cases x with
      | String str =>
          cases str with
          | nil =>
              change
                __str_is_empty
                    (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
                      (Term.String [])) =
                  Term.Boolean true
              have hNil :
                  __eo_is_list_nil (Term.UOp UserOp.str_concat)
                      (Term.String []) =
                    Term.Boolean true := by
                simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq]
                change decide (Term.String [] = Term.String []) = true
                simp
              rw [eo_get_nil_rec_str_concat_eq_of_nil_true
                (Term.String []) hNil]
              simp [__str_is_empty]
          | cons c cs =>
              change
                __eo_is_list (Term.UOp UserOp.str_concat)
                    (__eo_requires (Term.String (c :: cs)) (Term.String [])
                      (Term.String (c :: cs))) =
                  Term.Boolean true at hList
              simp [__eo_requires, native_teq, native_ite, __eo_is_list] at hList
      | Stuck =>
          exact False.elim
            (term_ne_stuck_of_smt_type_seq Term.Stuck T hxTy rfl)
      | Apply f a =>
          cases f with
          | Apply g head =>
              cases g with
              | UOp op =>
                  by_cases hop : op = UserOp.str_concat
                  · subst op
                    rcases str_concat_args_of_seq_type head a T hxTy with
                      ⟨hHeadTy, hTailTy⟩
                    by_cases hHeadString :
                        ∃ str : native_String, head = Term.String str
                    · rcases hHeadString with ⟨str, rfl⟩
                      rw [str_flatten_concat_string_eq str a] at hList ⊢
                      by_cases hTailList :
                          __eo_is_list (Term.UOp UserOp.str_concat)
                              (__str_flatten a) =
                            Term.Boolean true
                      · rw [eo_list_concat_substrWord_eq_rec_of_tail_list
                          str (__str_flatten a) hTailList] at hList ⊢
                        rw [eo_get_nil_rec_list_concat_rec_substrWord_eq
                          str (__str_flatten a) hTailList]
                        exact
                          str_flatten_get_nil_empty_of_seq_if_list a T
                            hTailTy hTailList
                      · rw [eo_list_concat_substrWord_eq_stuck_of_tail_not_list
                          str (__str_flatten a) hTailList] at hList
                        simp [__eo_is_list] at hList
                    · by_cases hHeadStuck : head = Term.Stuck
                      · subst head
                        exact False.elim
                          (term_ne_stuck_of_smt_type_seq Term.Stuck T
                            hHeadTy rfl)
                      · have hHeadNe : head ≠ Term.Stuck := hHeadStuck
                        have hIsStr :
                            __eo_is_str head = Term.Boolean false :=
                          eo_is_str_false_of_not_string_ne_stuck head
                            hHeadString hHeadNe
                        by_cases hHeadConcat :
                            ∃ h t : Term, head = mkConcat h t
                        · rcases hHeadConcat with ⟨h, t, rfl⟩
                          rw [__str_flatten.eq_2 h t a] at hList ⊢
                          obtain ⟨hHeadFlatList, hTailFlatList⟩ :=
                            eo_list_concat_args_list_of_result_list_local
                              (__str_flatten (mkConcat h t))
                              (__str_flatten a) hList
                          rw [eo_list_concat_eq_rec_of_lists_local
                            (__str_flatten (mkConcat h t)) (__str_flatten a)
                            hHeadFlatList hTailFlatList]
                          rw [eo_get_nil_rec_concat_rec_local
                            (__str_flatten (mkConcat h t)) (__str_flatten a)
                            hHeadFlatList hTailFlatList]
                          exact
                            str_flatten_get_nil_empty_of_seq_if_list a T
                              hTailTy hTailFlatList
                        · have hHeadNotConcat :
                              ∀ h t : Term, head ≠ mkConcat h t := by
                            intro h t hEq
                            exact hHeadConcat ⟨h, t, hEq⟩
                          rw [__str_flatten.eq_3 head a hHeadNotConcat,
                            hIsStr, eo_ite_false] at hList ⊢
                          by_cases hTailStuck :
                              __str_flatten a = Term.Stuck
                          · rw [hTailStuck] at hList
                            simp [__eo_mk_apply, __eo_is_list] at hList
                          · have hApply :
                                __eo_mk_apply
                                    (Term.Apply
                                      (Term.UOp UserOp.str_concat) head)
                                    (__str_flatten a) =
                                  mkConcat head (__str_flatten a) := by
                              cases hTail : __str_flatten a <;>
                                simp [__eo_mk_apply, mkConcat, hTail] at hTailStuck ⊢
                            rw [hApply] at hList ⊢
                            have hTailList :
                                __eo_is_list (Term.UOp UserOp.str_concat)
                                    (__str_flatten a) =
                                  Term.Boolean true :=
                              eo_is_list_tail_true_of_cons_self
                                (Term.UOp UserOp.str_concat) head
                                (__str_flatten a) hList
                            rw [eo_get_nil_rec_cons_self_eq_of_tail_list
                              (Term.UOp UserOp.str_concat) head
                              (__str_flatten a) (by decide) hTailList]
                            exact
                              str_flatten_get_nil_empty_of_seq_if_list a T
                                hTailTy hTailList
                  · exact
                      str_flatten_get_nil_empty_non_concat_of_seq_if_list
                        (Term.Apply (Term.Apply (Term.UOp op) head) a) T
                        hxTy
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          simp [mkConcat] at hEq
                          exact hop hEq.1.1)
                        hList
              | _ =>
                  exact
                    str_flatten_get_nil_empty_non_concat_of_seq_if_list
                      _ T hxTy
                      (by
                        intro h
                        rcases h with ⟨cHead, cTail, hEq⟩
                        cases hEq)
                      hList
          | _ =>
              exact
                str_flatten_get_nil_empty_non_concat_of_seq_if_list
                  _ T hxTy
                  (by
                    intro h
                    rcases h with ⟨cHead, cTail, hEq⟩
                    cases hEq)
                  hList
      | _ =>
          exact
            str_flatten_get_nil_empty_non_concat_of_seq_if_list
              _ T hxTy
              (by
                intro h
                rcases h with ⟨cHead, cTail, hEq⟩
                cases hEq)
              hList

private theorem str_is_compatible_full_word_flatten_intro_ne_false_of_append_eval
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (T : SmtType) (sx : SmtSeq) (word : native_String)
    (xTail suffixTail : List SmtValue)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hAlign :
      native_unpack_seq sx ++ xTail =
        word.map SmtValue.Char ++ suffixTail) :
    __str_is_compatible
        (RuleProofs.substrWord word 0 word.length)
        (__str_flatten (__str_nary_intro x)) ≠
      Term.Boolean false := by
  cases word with
  | nil =>
      exact str_is_compatible_empty_left_ne_false (__str_flatten (__str_nary_intro x))
  | cons wc wcs =>
      cases x with
      | String str =>
          have hStr :
              native_unpack_seq sx = str.map SmtValue.Char :=
            string_eval_unpack_eq M str sx hxEval
          have hAlign' :
              str.map SmtValue.Char ++ xTail =
                (wc :: wcs).map SmtValue.Char ++ suffixTail := by
            simpa [hStr] using hAlign
          cases str with
          | nil =>
              rw [RuleProofs.str_flatten_nary_intro_empty]
              exact substrWord_compatible_ne_false_of_append_eq (wc :: wcs) [] xTail suffixTail hAlign'
          | cons c cs =>
              rw [RuleProofs.str_flatten_nary_intro_cons c cs]
              simpa using
                substrWord_compatible_ne_false_of_append_eq (wc :: wcs) (c :: cs)
                  xTail suffixTail hAlign'
      | Stuck =>
          exact False.elim
            (term_ne_stuck_of_smt_type_seq Term.Stuck T hxTy rfl)
      | Apply f a =>
          cases f with
          | Apply g head =>
              cases g with
              | UOp op =>
                  by_cases hop : op = UserOp.str_concat
                  · subst op
                    let raw := mkConcat head a
                    have hRawNe : raw ≠ Term.Stuck :=
                      term_ne_stuck_of_smt_type_seq raw T (by
                        simpa [raw] using hxTy)
                    rcases eo_is_list_boolean_of_ne_stuck
                        (Term.UOp UserOp.str_concat) raw (by decide) hRawNe with
                      ⟨isList, hRawList⟩
                    cases isList
                    · have hIntroEq :
                          __str_nary_intro raw =
                            mkConcat raw (__seq_empty (__eo_typeof raw)) :=
                        str_nary_intro_eq_singleton_of_is_list_false_seq
                          raw T (by simpa [raw] using hxTy)
                          (by simpa using hRawList)
                      have hFlatEmpty :
                          __str_flatten (__seq_empty (__eo_typeof raw)) =
                            __seq_empty (__eo_typeof raw) :=
                        str_flatten_seq_empty_typeof_eq raw T
                          (by simpa [raw] using hxTy)
                      have hEmptyList :
                          __eo_is_list (Term.UOp UserOp.str_concat)
                              (__seq_empty (__eo_typeof raw)) =
                            Term.Boolean true :=
                        eo_is_list_str_concat_seq_empty_of_ne_stuck
                          (__eo_typeof raw)
                          (seq_empty_typeof_ne_stuck_of_smt_type_seq raw T
                            (by simpa [raw] using hxTy))
                      by_cases hRawFlatList :
                          __eo_is_list (Term.UOp UserOp.str_concat)
                              (__str_flatten raw) = Term.Boolean true
                      · rw [hIntroEq]
                        change
                          __str_is_compatible
                              (RuleProofs.substrWord (wc :: wcs) 0
                                (wc :: wcs).length)
                              (__eo_list_concat (Term.UOp UserOp.str_concat)
                                (__str_flatten raw)
                                (__str_flatten
                                  (__seq_empty (__eo_typeof raw)))) ≠
                            Term.Boolean false
                        rw [hFlatEmpty]
                        rw [eo_list_concat_eq_rec_of_lists_local
                          (__str_flatten raw) (__seq_empty (__eo_typeof raw))
                          hRawFlatList hEmptyList]
                        exact
                          str_is_compatible_full_word_flatten_rec_ne_false_of_append_eval
                            M hM raw T sx (wc :: wcs)
                            (__seq_empty (__eo_typeof raw)) xTail suffixTail
                            (by simpa [raw] using hxTy)
                            (by simpa [raw] using hxEval) hAlign hRawFlatList
                            hEmptyList
                            (by
                              intro word' suffixTail' hTailAlign
                              exact
                                str_is_compatible_seq_empty_typeof_right_ne_false
                                  (RuleProofs.substrWord word' 0 word'.length)
                                  raw T (by simpa [raw] using hxTy))
                      · have hConcatStuck :
                            __eo_list_concat (Term.UOp UserOp.str_concat)
                                (__str_flatten raw)
                                (__str_flatten
                                  (__seq_empty (__eo_typeof raw))) =
                              Term.Stuck := by
                          simp [__eo_list_concat, hRawFlatList,
                            __eo_requires, native_teq, native_ite]
                        rw [hIntroEq]
                        change
                          __str_is_compatible
                              (RuleProofs.substrWord (wc :: wcs) 0
                                (wc :: wcs).length)
                              (__eo_list_concat (Term.UOp UserOp.str_concat)
                                (__str_flatten raw)
                                (__str_flatten
                                  (__seq_empty (__eo_typeof raw)))) ≠
                            Term.Boolean false
                        rw [hConcatStuck]
                        change
                          __str_is_compatible
                              (mkConcat (Term.String [wc])
                                (RuleProofs.substrWord wcs 0 wcs.length))
                              Term.Stuck ≠ Term.Boolean false
                        simp [__str_is_compatible]
                    · rw [str_nary_intro_eq_self_of_is_list raw
                          (by simpa using hRawList)]
                      exact
                        str_is_compatible_full_word_flatten_ne_false_of_append_eval
                          M hM raw T sx (wc :: wcs) xTail suffixTail
                          (by simpa [raw] using hxTy)
                          (by simpa [raw] using hxEval) hAlign
                  · exact
                      str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
                        (Term.Apply (Term.Apply (Term.UOp op) head) a) T wc
                        wcs hxTy
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          simp [mkConcat] at hEq
                          exact hop hEq.1.1)
                        (by
                          intro h
                          rcases h with ⟨s, hEq⟩
                          cases hEq)
              | _ =>
                  exact
                    str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
                      _ T wc wcs hxTy
                      (by
                        intro h
                        rcases h with ⟨cHead, cTail, hEq⟩
                        cases hEq)
                      (by
                        intro h
                        rcases h with ⟨s, hEq⟩
                        cases hEq)
          | _ =>
              exact
                str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
                  _ T wc wcs hxTy
                  (by
                    intro h
                    rcases h with ⟨cHead, cTail, hEq⟩
                    cases hEq)
                  (by
                    intro h
                    rcases h with ⟨s, hEq⟩
                    cases hEq)
      | _ =>
          exact
            str_is_compatible_full_word_flatten_intro_non_concat_non_string_ne_false
              _ T wc wcs hxTy
              (by
                intro h
                rcases h with ⟨head, tail, hEq⟩
                cases hEq)
              (by
                intro h
                rcases h with ⟨s, hEq⟩
                cases hEq)

private theorem str_is_compatible_rev_word_flatten_intro_ne_false_of_append_eval
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (T : SmtType) (sx : SmtSeq) (word : native_String)
    (xPrefix prefixTail : List SmtValue)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hAlign :
      xPrefix ++ native_unpack_seq sx =
        prefixTail ++ word.map SmtValue.Char) :
    __str_is_compatible
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (RuleProofs.substrWord word 0 word.length))
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro x))) ≠
      Term.Boolean false := by
  cases word with
  | nil =>
      rw [eo_list_rev_substrWord_local []]
      exact str_is_compatible_empty_left_ne_false (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__str_nary_intro x)))
  | cons wc wcs =>
      cases x with
      | String str =>
          have hStr :
              native_unpack_seq sx = str.map SmtValue.Char :=
            string_eval_unpack_eq M str sx hxEval
          have hAlign' :
              xPrefix ++ str.map SmtValue.Char =
                prefixTail ++ (wc :: wcs).map SmtValue.Char := by
            simpa [hStr] using hAlign
          have hAlignRev :
              str.reverse.map SmtValue.Char ++ xPrefix.reverse =
                (wc :: wcs).reverse.map SmtValue.Char ++
                  prefixTail.reverse := by
            have hRev := congrArg List.reverse hAlign'
            simpa [List.reverse_append, List.map_reverse] using hRev
          rw [eo_list_rev_substrWord_local (wc :: wcs)]
          cases str with
          | nil =>
              rw [RuleProofs.str_flatten_nary_intro_empty]
              have hRevEmpty :
                  __eo_list_rev (Term.UOp UserOp.str_concat)
                      (Term.String []) =
                    Term.String [] :=
                eo_list_rev_str_concat_nil_eq_of_nil_true (Term.String [])
                  (by
                    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                      __eo_eq]
                    change decide (Term.String [] = Term.String []) = true
                    simp)
              rw [hRevEmpty]
              exact str_is_compatible_empty_right_ne_false
                (RuleProofs.substrWord (wc :: wcs).reverse 0
                  (wc :: wcs).reverse.length)
          | cons c cs =>
              rw [RuleProofs.str_flatten_nary_intro_cons c cs]
              rw [eo_list_rev_substrWord_local (c :: cs)]
              simpa using
                substrWord_compatible_ne_false_of_append_eq
                  (wc :: wcs).reverse (c :: cs).reverse
                  xPrefix.reverse prefixTail.reverse hAlignRev
      | Stuck =>
          exact False.elim
            (term_ne_stuck_of_smt_type_seq Term.Stuck T hxTy rfl)
      | Apply f a =>
          cases f with
          | Apply g head =>
              cases g with
              | UOp op =>
                  by_cases hop : op = UserOp.str_concat
                  · subst op
                    rw [eo_list_rev_substrWord_local (wc :: wcs)]
                    have hRawNotString :
                        ¬ ∃ s : native_String,
                          mkConcat head a = Term.String s := by
                      intro h
                      rcases h with ⟨s, hEq⟩
                      cases hEq
                    have hRawNe : mkConcat head a ≠ Term.Stuck :=
                      term_ne_stuck_of_smt_type_seq (mkConcat head a) T hxTy
                    rcases eo_is_list_boolean_of_ne_stuck
                        (Term.UOp UserOp.str_concat) (mkConcat head a)
                        (by decide) hRawNe with
                      ⟨isList, hRawList⟩
                    cases isList
                    · have hIntroEq :
                          __str_nary_intro (mkConcat head a) =
                            mkConcat (mkConcat head a)
                              (__seq_empty (__eo_typeof (mkConcat head a))) :=
                        str_nary_intro_eq_singleton_of_is_list_false_seq
                          (mkConcat head a) T hxTy (by simpa using hRawList)
                      let empty := __seq_empty (__eo_typeof (mkConcat head a))
                      have hEmptyNil :
                          __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
                            Term.Boolean true := by
                        simpa [empty] using
                          eo_is_list_nil_str_concat_seq_empty_typeof_of_seq
                            (mkConcat head a) T hxTy
                      have hEmptyList :
                          __eo_is_list (Term.UOp UserOp.str_concat) empty =
                            Term.Boolean true :=
                        eo_is_list_str_concat_nil_true_of_nil_true empty
                          hEmptyNil
                      have hEmptyNe : empty ≠ Term.Stuck := by
                        simpa [empty] using
                          seq_empty_typeof_ne_stuck_of_smt_type_seq
                            (mkConcat head a) T hxTy
                      have hFlatEmpty : __str_flatten empty = empty := by
                        simpa [empty] using
                          str_flatten_seq_empty_typeof_eq
                            (mkConcat head a) T hxTy
                      rw [hIntroEq, __str_flatten.eq_2 head a empty,
                        hFlatEmpty]
                      have hAlignRev :
                          (native_unpack_seq sx).reverse ++ xPrefix.reverse =
                            (wc :: wcs).reverse.map SmtValue.Char ++
                              prefixTail.reverse := by
                        have hRev := congrArg List.reverse hAlign
                        simpa [List.reverse_append, List.map_reverse]
                          using hRev
                      by_cases hFlatList :
                          __eo_is_list (Term.UOp UserOp.str_concat)
                              (__str_flatten (mkConcat head a)) =
                            Term.Boolean true
                      · rw [eo_list_concat_eq_rec_of_lists_local
                          (__str_flatten (mkConcat head a)) empty hFlatList
                          hEmptyList]
                        have hConcatList :
                            __eo_is_list (Term.UOp UserOp.str_concat)
                                (__eo_list_concat_rec
                                  (__str_flatten (mkConcat head a)) empty) =
                              Term.Boolean true :=
                          eo_list_concat_rec_is_list_true_of_lists
                            (Term.UOp UserOp.str_concat)
                            (__str_flatten (mkConcat head a)) empty hFlatList
                            hEmptyList
                        have hRevNe :
                            __eo_list_rev (Term.UOp UserOp.str_concat)
                                (__eo_list_concat_rec
                                  (__str_flatten (mkConcat head a)) empty) ≠
                              Term.Stuck :=
                          eo_list_rev_ne_stuck_of_is_list_true
                            (Term.UOp UserOp.str_concat)
                            (__eo_list_concat_rec
                              (__str_flatten (mkConcat head a)) empty)
                            hConcatList
                        rw [eo_list_rev_eq_rec_of_ne_stuck
                          (Term.UOp UserOp.str_concat)
                          (__eo_list_concat_rec
                            (__str_flatten (mkConcat head a)) empty) hRevNe]
                        rw [eo_get_nil_rec_concat_rec_local
                          (__str_flatten (mkConcat head a)) empty hFlatList
                          hEmptyList]
                        rw [eo_get_nil_rec_str_concat_eq_of_nil_true empty
                          hEmptyNil]
                        rw [eo_list_rev_rec_concat_rec_local
                          (__str_flatten (mkConcat head a)) empty empty
                          hFlatList hEmptyList hEmptyNe]
                        rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true
                          empty
                          (__eo_list_rev_rec
                            (__str_flatten (mkConcat head a)) empty)
                          hEmptyNil]
                        exact
                          str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                            M (mkConcat head a) T sx (wc :: wcs).reverse
                            empty xPrefix.reverse prefixTail.reverse hxTy hxEval
                            hAlignRev
                            (by
                              intro word' suffixTail' hAccAlign
                              exact
                                str_is_compatible_str_is_empty_right_ne_false
                                  (RuleProofs.substrWord word' 0 word'.length)
                                  empty
                                  (by
                                    simpa [empty] using
                                      str_is_empty_seq_empty_typeof_of_seq
                                        (mkConcat head a) T hxTy))
                      · have hConcatStuck :
                            __eo_list_concat (Term.UOp UserOp.str_concat)
                                (__str_flatten (mkConcat head a)) empty =
                              Term.Stuck := by
                          simp [__eo_list_concat, hFlatList, __eo_requires,
                            native_teq, native_ite]
                        rw [hConcatStuck]
                        have hRevStuck :
                            __eo_list_rev (Term.UOp UserOp.str_concat)
                                Term.Stuck = Term.Stuck := by
                          simp [__eo_list_rev, __eo_is_list, __eo_requires,
                            native_teq, native_ite]
                        rw [hRevStuck]
                        cases hLeft :
                            RuleProofs.substrWord (wc :: wcs).reverse 0
                              (wc :: wcs).reverse.length <;>
                          simp [__str_is_compatible]
                    · rw [str_nary_intro_eq_self_of_is_list (mkConcat head a)
                        (by simpa using hRawList)]
                      by_cases hRevStuck :
                          __eo_list_rev (Term.UOp UserOp.str_concat)
                              (__str_flatten (mkConcat head a)) =
                            Term.Stuck
                      · rw [hRevStuck]
                        cases hLeft :
                            RuleProofs.substrWord (wc :: wcs).reverse 0
                              (wc :: wcs).reverse.length <;>
                          simp [__str_is_compatible]
                      · have hFlatList :
                            __eo_is_list (Term.UOp UserOp.str_concat)
                                (__str_flatten (mkConcat head a)) =
                              Term.Boolean true :=
                          eo_list_rev_is_list_true_of_ne_stuck
                            (Term.UOp UserOp.str_concat)
                            (__str_flatten (mkConcat head a)) hRevStuck
                        have hNilEmpty :
                            __str_is_empty
                                (__eo_get_nil_rec
                                  (Term.UOp UserOp.str_concat)
                                  (__str_flatten (mkConcat head a))) =
                              Term.Boolean true :=
                          str_flatten_get_nil_empty_of_seq_if_list
                            (mkConcat head a) T hxTy hFlatList
                        rw [eo_list_rev_eq_rec_of_ne_stuck
                          (Term.UOp UserOp.str_concat)
                          (__str_flatten (mkConcat head a)) hRevStuck]
                        have hAlignRev :
                            (native_unpack_seq sx).reverse ++
                                xPrefix.reverse =
                              (wc :: wcs).reverse.map SmtValue.Char ++
                                prefixTail.reverse := by
                          have hRev := congrArg List.reverse hAlign
                          simpa [List.reverse_append, List.map_reverse]
                            using hRev
                        exact
                          str_is_compatible_rev_rec_flatten_ne_false_of_append_eval
                            M (mkConcat head a) T sx (wc :: wcs).reverse
                            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
                              (__str_flatten (mkConcat head a)))
                            xPrefix.reverse prefixTail.reverse hxTy hxEval
                            hAlignRev
                            (by
                              intro word' suffixTail' hAccAlign
                              exact
                                str_is_compatible_str_is_empty_right_ne_false
                                  (RuleProofs.substrWord word' 0
                                    word'.length)
                                  (__eo_get_nil_rec
                                    (Term.UOp UserOp.str_concat)
                                    (__str_flatten (mkConcat head a)))
                                  hNilEmpty)
                  · exact
                      str_is_compatible_rev_word_flatten_intro_non_concat_non_string_ne_false
                        (Term.Apply (Term.Apply (Term.UOp op) head) a) T wc
                        wcs hxTy
                        (by
                          intro h
                          rcases h with ⟨cHead, cTail, hEq⟩
                          simp [mkConcat] at hEq
                          exact hop hEq.1.1)
                        (by
                          intro h
                          rcases h with ⟨s, hEq⟩
                          cases hEq)
              | _ =>
                  exact
                    str_is_compatible_rev_word_flatten_intro_non_concat_non_string_ne_false
                      _ T wc wcs hxTy
                      (by
                        intro h
                        rcases h with ⟨cHead, cTail, hEq⟩
                        cases hEq)
                      (by
                        intro h
                        rcases h with ⟨s, hEq⟩
                        cases hEq)
          | _ =>
              exact
                str_is_compatible_rev_word_flatten_intro_non_concat_non_string_ne_false
                  _ T wc wcs hxTy
                  (by
                    intro h
                    rcases h with ⟨cHead, cTail, hEq⟩
                    cases hEq)
                  (by
                    intro h
                    rcases h with ⟨s, hEq⟩
                    cases hEq)
      | _ =>
          exact
            str_is_compatible_rev_word_flatten_intro_non_concat_non_string_ne_false
              _ T wc wcs hxTy
              (by
                intro h
                rcases h with ⟨head, tail, hEq⟩
                cases hEq)
              (by
                intro h
                rcases h with ⟨s, hEq⟩
                cases hEq)

private theorem mkConcat_eval_unpack_eq
    (M : SmtModel) (x y : Term) (sxy sx sy : SmtSeq)
    (hxyEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
        SmtValue.Seq sxy)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    native_unpack_seq sxy =
      native_unpack_seq sx ++ native_unpack_seq sy := by
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hyEval] at hxyEval
  simp [__smtx_model_eval_str_concat, native_seq_concat] at hxyEval
  rw [← hxyEval]
  simp [_root_.native_unpack_pack_seq]

private theorem str_flatten_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_flatten x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_flatten] at h

private theorem cprop_flat_second_false_tail_head_of_ne_stuck
    (t tc tTail : Term)
    (hIntroT : __str_nary_intro t = mkConcat tc tTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hFlatNe : concatCPropFlatSecond (Term.Boolean false) t ≠ Term.Stuck) :
    ∃ x xTail,
      tTail = mkConcat x xTail ∧
        __eo_is_list (Term.UOp UserOp.str_concat) xTail = Term.Boolean true ∧
        concatCPropFlatSecond (Term.Boolean false) t =
          __str_flatten (__str_nary_intro x) := by
  have hSecondEq :
      concatCPropSecond (Term.Boolean false) t =
        __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) := by
    simpa [concatCPropSecond, concatCPropNormalize, concatSplitNormalize,
      eo_ite_false, hIntroT] using
      eo_list_nth_one_str_concat_cons_eq_tail_zero tc tTail hTTailList
  have hIntroSecondNe :
      __str_nary_intro (concatCPropSecond (Term.Boolean false) t) ≠
        Term.Stuck :=
    str_flatten_arg_ne_stuck_of_ne_stuck
      (__str_nary_intro (concatCPropSecond (Term.Boolean false) t))
      hFlatNe
  have hSecondNe :
      concatCPropSecond (Term.Boolean false) t ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (concatCPropSecond (Term.Boolean false) t) hIntroSecondNe
  have hNthNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) ≠ Term.Stuck := by
    rwa [hSecondEq] at hSecondNe
  let x :=
    __eo_list_nth (Term.UOp UserOp.str_concat) tTail (Term.Numeral 0)
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) tTail x rfl (by simpa [x] using hNthNe)
    with ⟨xTail, hTailEq, hXTailList⟩
  refine ⟨x, xTail, hTailEq, hXTailList, ?_⟩
  simp [concatCPropFlatSecond, hSecondEq, x]

private theorem cprop_flat_second_true_tail_head_of_rev_ne_stuck
    (t tc tTail : Term)
    (hRevIntroT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hRevFlatNe :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropFlatSecond (Term.Boolean true) t) ≠ Term.Stuck) :
    ∃ x xTail,
      tTail = mkConcat x xTail ∧
        __eo_is_list (Term.UOp UserOp.str_concat) xTail = Term.Boolean true ∧
        concatCPropFlatSecond (Term.Boolean true) t =
          __str_flatten (__str_nary_intro x) := by
  have hFlatNe : concatCPropFlatSecond (Term.Boolean true) t ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (concatCPropFlatSecond (Term.Boolean true) t) hRevFlatNe
  have hSecondEq :
      concatCPropSecond (Term.Boolean true) t =
        __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) := by
    simpa [concatCPropSecond, concatCPropNormalize, concatSplitNormalize,
      eo_ite_true, hRevIntroT] using
      eo_list_nth_one_str_concat_cons_eq_tail_zero tc tTail hTTailList
  have hIntroSecondNe :
      __str_nary_intro (concatCPropSecond (Term.Boolean true) t) ≠
        Term.Stuck :=
    str_flatten_arg_ne_stuck_of_ne_stuck
      (__str_nary_intro (concatCPropSecond (Term.Boolean true) t))
      hFlatNe
  have hSecondNe :
      concatCPropSecond (Term.Boolean true) t ≠ Term.Stuck :=
    str_nary_intro_arg_ne_stuck_of_ne_stuck
      (concatCPropSecond (Term.Boolean true) t) hIntroSecondNe
  have hNthNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) tTail
          (Term.Numeral 0) ≠ Term.Stuck := by
    rwa [hSecondEq] at hSecondNe
  let x :=
    __eo_list_nth (Term.UOp UserOp.str_concat) tTail (Term.Numeral 0)
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) tTail x rfl (by simpa [x] using hNthNe)
    with ⟨xTail, hTailEq, hXTailList⟩
  refine ⟨x, xTail, hTailEq, hXTailList, ?_⟩
  simp [concatCPropFlatSecond, hSecondEq, x]

private theorem eo_prog_concat_cprop_eq_of_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
      concatCPropFormula rev t s tc ∧
      concatCPropHead rev t = tc := by
  have hProgBody :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
        concatCPropBody rev t s tc := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals rfl
  have hBodyNe : concatCPropBody rev t s tc ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadT : concatCPropHead rev t = tc :=
    eo_requires_eq_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  have hFormulaEq :
      concatCPropBody rev t s tc = concatCPropFormula rev t s tc :=
    eo_requires_eq_result_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  exact ⟨by rw [hProgBody, hFormulaEq], hHeadT⟩

private theorem eo_prog_concat_cprop_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s tc,
      x1 = mkEq t s ∧ x2 = mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)) := by
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
                                              | Apply lenOp tc =>
                                                  cases lenOp with
                                                  | UOp lenU =>
                                                      cases lenU with
                                                      | str_len =>
                                                          cases zero with
                                                          | Numeral z =>
                                                              by_cases hz : z = 0
                                                              · subst z
                                                                exact
                                                                  ⟨t, rhs1, tc,
                                                                    rfl, rfl⟩
                                                              · cases rev <;>
                                                                  simp [__eo_prog_concat_cprop, hz]
                                                                    at hProg
                                                          | _ =>
                                                              cases rev <;>
                                                                simp [__eo_prog_concat_cprop]
                                                                  at hProg
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_cprop]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_cprop]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_cprop]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_cprop] at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_cprop] at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_cprop] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_cprop] at hProg
                          | _ =>
                              cases rev <;>
                                simp [__eo_prog_concat_cprop] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_cprop] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_cprop] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_cprop] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_cprop] at hProg

private theorem concatCProp_rev_cases_of_prog_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htcNe : tc ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck rev t s tc hProg with
    ⟨_, hHeadT⟩
  have hHeadNe : concatCPropHead rev t ≠ Term.Stuck := by
    rw [hHeadT]
    exact htcNe
  have hNormNe : concatCPropNormalize rev t ≠ Term.Stuck :=
    concatSplitNormalize_ne_stuck_of_head_ne_stuck rev t hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (__str_nary_intro t) ≠ Term.Stuck := by
    simpa [concatCPropNormalize, concatSplitNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
    (__str_nary_intro t) hIteNe

private theorem cprop_formula_false_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropFormula (Term.Boolean false) t s tc ≠ Term.Stuck := by
  rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
    (Term.Boolean false) t s tc hProg).1]
  exact hProg

private theorem cprop_formula_true_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropFormula (Term.Boolean true) t s tc ≠ Term.Stuck := by
  rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
    (Term.Boolean true) t s tc hProg).1]
  exact hProg

private theorem cprop_prefix_false_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck := by
  have hFormulaNe := cprop_formula_false_ne_of_prog t s tc hProg
  have hRhsNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropPrefix (Term.Boolean false) t s))
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropSuffix (Term.Boolean false) t s tc))
            (__eo_nil (Term.UOp UserOp.str_concat)
              (__eo_typeof (concatCPropPrefix (Term.Boolean false) t s)))) ≠
        Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by
        simpa [concatCPropFormula, eo_ite_false] using hFormulaNe)
  have hFunNe :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
  exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFunNe

private theorem cprop_reverse_end_true_ne_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck := by
  have hFormulaNe := cprop_formula_true_ne_of_prog t s tc hProg
  have hRhsNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropReverseSuffix (Term.Boolean true) t s tc))
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropReverseEnd (Term.Boolean true) t s))
            (__eo_nil (Term.UOp UserOp.str_concat)
              (__eo_typeof
                (concatCPropReverseSuffix (Term.Boolean true) t s tc)))) ≠
        Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by
        simpa [concatCPropFormula, eo_ite_true] using hFormulaNe)
  have hInnerNe :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsNe
  have hInnerFunNe :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInnerNe
  exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe

private theorem cprop_context_false_head_type
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof
            (__eo_to_smt (concatCPropHead (Term.Boolean false) s)) =
          SmtType.Seq T := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean false) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hPrefixNe :
      concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck :=
    cprop_prefix_false_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hPrefixNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
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
  rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
      hIntroT htcTy hTNN with
    ⟨htTy, _htTailTy⟩
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
  exact ⟨T, htcTy, by simpa [sc] using hscTy⟩

private theorem cprop_overlap_len_false_int_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof (__eo_to_smt (concatCPropOverlapLen (Term.Boolean false) t s)) =
      SmtType.Int := by
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hKNe :
      concatCPropOverlapLen (Term.Boolean false) t s ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hPrefixNe
  exact smt_typeof_eo_add_one_of_ne_stuck
    (__str_overlap_rec (concatCPropSHeadTailWord (Term.Boolean false) s)
      (concatCPropFlatSecond (Term.Boolean false) t))
    (by simpa [concatCPropOverlapLen, eo_ite_false] using hKNe)

private theorem cprop_prefix_false_seq_type
    (t s tc : Term) (T : SmtType)
    (hscTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropHead (Term.Boolean false) s)) =
        SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
      SmtType.Seq T := by
  let sc := concatCPropHead (Term.Boolean false) s
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hOuterFun :
      __eo_mk_apply
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0)) k ≠ Term.Stuck := by
    simpa [concatCPropPrefix, sc, k] using hPrefixNe
  have hKNe : k ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hOuterFun
  have hMidFunNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
        (Term.Numeral 0) ≠ Term.Stuck :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
  have hInnerFunNe :
      __eo_mk_apply (Term.UOp UserOp.str_substr) sc ≠ Term.Stuck :=
    cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hMidFunNe
  have hscNe : sc ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe
  have hKTy :
      __smtx_typeof (__eo_to_smt k) = SmtType.Int := by
    simpa [k] using cprop_overlap_len_false_int_of_prog t s tc hProg
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_2]
  have hPrefixEq :
      concatCPropPrefix (Term.Boolean false) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0)) k := by
    simp [concatCPropPrefix, sc, k, __eo_mk_apply]
  rw [hPrefixEq]
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
          (__eo_to_smt k)) =
      SmtType.Seq T
  exact smtx_typeof_str_substr_seq (__eo_to_smt sc) (SmtTerm.Numeral 0)
    (__eo_to_smt k) T (by simpa [sc] using hscTy) hZeroTy hKTy

private theorem cprop_suffix_false_seq_type
    (t s tc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hPrefixTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatCPropSuffix (Term.Boolean false) t s tc)) =
      SmtType.Seq T := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  have hpfxNe : pfx ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck pfx T (by simpa [pfx] using hPrefixTy)
  have hLenPfxEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx =
        Term.Apply (Term.UOp UserOp.str_len) pfx :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) pfx (by simp) hpfxNe
  have hLenPfxNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx ≠ Term.Stuck := by
    rw [hLenPfxEq]
    simp
  have hSubMidEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) tc)
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hSubMidNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) ≠ Term.Stuck := by
    rw [hSubMidEq]
    simp
  have hNegLenEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hNegLenNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) ≠ Term.Stuck := by
    rw [hNegLenEq]
    simp
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Apply (Term.UOp UserOp.str_len) pfx))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) pfx)) := by
    rw [hSubMidEq, hNegLenEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Apply (Term.UOp UserOp.str_len) pfx))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) pfx)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropSuffix (Term.Boolean false) t s tc =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Apply (Term.UOp UserOp.str_len) pfx))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) pfx))) := by
    dsimp [concatCPropSuffix, pfx]
    rw [hOuterEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp._at_purify)
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx)))
      (by simp) (by simp)
  have hLenTcTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt tc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt tc) T htcTy
  have hLenPfxTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt pfx)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt pfx) T (by simpa [pfx] using hPrefixTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt pfx))) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt tc))
      (SmtTerm.str_len (__eo_to_smt pfx)) hLenTcTy hLenPfxTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx)))) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tc)
      (SmtTerm.str_len (__eo_to_smt pfx))
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
        (SmtTerm.str_len (__eo_to_smt pfx))) T htcTy hLenPfxTy hNegTy
  rw [hSuffixEq]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx))))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using hSubTy

private theorem cprop_context_false
    (M : SmtModel) (hM : model_wf M)
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tTail sTail,
      sc = concatCPropHead (Term.Boolean false) s ∧
      __str_nary_intro t = mkConcat tc tTail ∧
      __str_nary_intro s = mkConcat sc sTail ∧
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean false) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hFormulaNe : concatCPropFormula (Term.Boolean false) t s tc ≠ Term.Stuck := by
    rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean false) t s tc hProg).1]
    exact hProg
  have hPrefixNe :
      concatCPropPrefix (Term.Boolean false) t s ≠ Term.Stuck := by
    have hRhsNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropPrefix (Term.Boolean false) t s))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat)
                (concatCPropSuffix (Term.Boolean false) t s tc))
              (__eo_nil (Term.UOp UserOp.str_concat)
                (__eo_typeof (concatCPropPrefix (Term.Boolean false) t s)))) ≠
          Term.Stuck :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
        (by
          simpa [concatCPropFormula, eo_ite_false] using hFormulaNe)
    have hFunNe :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFunNe
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hPrefixNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_false] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_false]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) tc
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) sc
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_cons_seq_types_of_head_seq t tc tTail T
      hIntroT htcTy hTNN with
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
    exact smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
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
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true := by
    simpa [hIntroT, hIntroS] using hIntroEq
  exact ⟨T, sc, tTail, sTail, rfl, hIntroT, hIntroS, hTTailList,
    hSTailList, htcTy, hscTy, htTailTy, hsTailTy, hConcatEq⟩

private theorem eo_interprets_rev_cons_snoc_prefix_of_seq_with_cons_eq
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
            (mkConcat pref head)) true ∧
        (∀ a aTail, tail = mkConcat a aTail ->
          pref =
            __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail)) := by
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
    refine ⟨pref, hPrefixTy, hSnoc, ?_⟩
    intro b bTail _hEq
    rfl
  · have hNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) tail =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_of_list_true_not_concat tail hTailList
        hTailConcat
    refine ⟨tail, hTailTy,
      eo_interprets_rev_cons_snoc_of_list_nil_raw M hM head tail T
        hHeadTy hNil hTailTy hRevCons, ?_⟩
    intro a aTail hEq
    exact False.elim (hTailConcat ⟨a, aTail, hEq⟩)

private theorem cprop_context_true
    (M : SmtModel) (hM : model_wf M)
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq t s) true) :
    ∃ T sc tPrefix sPrefix tTail sTail,
      sc = concatCPropHead (Term.Boolean true) s ∧
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail ∧
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat sc sTail ∧
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T ∧
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true ∧
      (∀ a aTail, tTail = mkConcat a aTail ->
        tPrefix =
          __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) tTail)) ∧
      (∀ a aTail, sTail = mkConcat a aTail ->
        sPrefix =
          __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) sTail)) := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean true) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hFormulaNe : concatCPropFormula (Term.Boolean true) t s tc ≠ Term.Stuck := by
    rw [← (eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg).1]
    exact hProg
  have hReverseEndNe :
      concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck := by
    have hRhsNe :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat)
              (concatCPropReverseSuffix (Term.Boolean true) t s tc))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat)
                (concatCPropReverseEnd (Term.Boolean true) t s))
              (__eo_nil (Term.UOp UserOp.str_concat)
                (__eo_typeof
                  (concatCPropReverseSuffix (Term.Boolean true) t s tc)))) ≠
          Term.Stuck :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
        (by
          simpa [concatCPropFormula, eo_ite_true] using hFormulaNe)
    have hInnerNe :=
      cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhsNe
    have hInnerFunNe :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInnerNe
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerFunNe
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hReverseEndNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      tc hNthTEq hNthTNe with
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
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
      hRevIntroT htcTy hTNN with
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
              (mkConcat tc tTail)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true := by
    simpa [hRevIntroT, hRevIntroS] using hDoubleEq
  have hConsTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat tc tTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      tc tTail (by decide) hTTailList
  have hConsSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat sc sTail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      sc sTail (by decide) hSTailList
  have hConsTTy :
      __smtx_typeof (__eo_to_smt (mkConcat tc tTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq tc tTail T htcTy htTailTy
  have hConsSTy :
      __smtx_typeof (__eo_to_smt (mkConcat sc sTail)) = SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc sTail T hscTy hsTailTy
  have hRevConsT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat tc tTail) hConsTList
  have hRevConsS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail) ≠
        Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat sc sTail) hConsSList
  have hElimConsT :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat tc tTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq tc tTail T
      hConsTTy hRevConsT
  have hElimConsS :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat sc sTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq sc sTail T
      hConsSTy hRevConsS
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq_with_cons_eq M hM tc tTail T
      htcTy hTTailList htTailTy hRevConsT hElimConsT with
    ⟨tPrefix, htPrefixTy, hSnocT, hTPrefixConsEq⟩
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq_with_cons_eq M hM sc sTail T
      hscTy hSTailList hsTailTy hRevConsS hElimConsS with
    ⟨sPrefix, hsPrefixTy, hSnocS, hSPrefixConsEq⟩
  have hSnocTSymm :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat tc tTail)))) true :=
    eo_interprets_eq_symm_local M
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (mkConcat tPrefix tc) hSnocT
  have hLeftToRight :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc)
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat sc sTail)))) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat tc tTail)))
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      hSnocTSymm hRevConcatEq
  have hSnocEq :
      eo_interprets M
        (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true :=
    RuleProofs.eo_interprets_eq_trans M (mkConcat tPrefix tc)
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat sc sTail)))
      (mkConcat sPrefix sc) hLeftToRight hSnocS
  exact ⟨T, sc, tPrefix, sPrefix, tTail, sTail, rfl, hRevIntroT,
    hRevIntroS, hTTailList, hSTailList, htTailTy, hsTailTy, htcTy,
    hscTy, htPrefixTy, hsPrefixTy, hSnocEq, hTPrefixConsEq,
    hSPrefixConsEq⟩

private theorem cprop_context_true_head_type
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T ∧
        __smtx_typeof
            (__eo_to_smt (concatCPropHead (Term.Boolean true) s)) =
          SmtType.Seq T := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck
      (Term.Boolean true) t s tc hProg with
    ⟨_, hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  let sc := concatCPropHead (Term.Boolean true) s
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by unfold RuleProofs.eo_has_smt_translation; rw [htcTy]; exact seq_ne_none T)
  have hReverseEndNe :
      concatCPropReverseEnd (Term.Boolean true) t s ≠ Term.Stuck :=
    cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck := by
    have hOuterFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hReverseEndNe
    have hMidFun :=
      cprop_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hOuterFun
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hMidFun
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) = tc := by
    simpa [concatCPropHead, concatCPropNormalize, concatSplitHead,
      concatSplitNormalize, eo_ite_true] using hHeadT
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) = sc := by
    simp [sc, concatCPropHead, concatSplitHead,
      concatSplitNormalize, eo_ite_true]
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact htcNe
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hscNe
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      tc hNthTEq hNthTNe with
    ⟨tTail, hRevIntroT, _hTTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      sc hNthSEq hNthSNe with
    ⟨sTail, hRevIntroS, _hSTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      t s hPremBool with
    ⟨hTSSameTy, hTNN⟩
  have hSNN : __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
    rw [← hTSSameTy]
    exact hTNN
  rcases str_nary_intro_rev_cons_seq_types_of_head_seq t tc tTail T
      hRevIntroT htcTy hTNN with
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
  exact ⟨T, htcTy, by simpa [sc] using hscTy⟩

private theorem cprop_overlap_len_true_int_of_prog
    (t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof (__eo_to_smt (concatCPropOverlapLen (Term.Boolean true) t s)) =
      SmtType.Int := by
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hKNe :
      concatCPropOverlapLen (Term.Boolean true) t s ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEndNe
  exact smt_typeof_eo_add_one_of_ne_stuck
    (__str_overlap_rec
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (concatCPropSHeadTailWord (Term.Boolean true) s))
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (concatCPropFlatSecond (Term.Boolean true) t)))
    (by simpa [concatCPropOverlapLen, eo_ite_true] using hKNe)

private theorem cprop_reverse_end_true_seq_type
    (t s tc : Term) (T : SmtType)
    (hscTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropHead (Term.Boolean true) s)) =
        SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
      SmtType.Seq T := by
  let sc := concatCPropHead (Term.Boolean true) s
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T (by simpa [sc] using hscTy)
  have hKNe : k ≠ Term.Stuck :=
    cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEndNe
  have hKTy : __smtx_typeof (__eo_to_smt k) = SmtType.Int := by
    simpa [k] using cprop_overlap_len_true_int_of_prog t s tc hProg
  have hLenScEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) sc =
        Term.Apply (Term.UOp UserOp.str_len) sc :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) sc (by simp) hscNe
  have hLenScNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) sc ≠ Term.Stuck := by
    rw [hLenScEq]
    simp
  have hSubFunEq :
      __eo_mk_apply (Term.UOp UserOp.str_substr) sc =
        Term.Apply (Term.UOp UserOp.str_substr) sc :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_substr) sc (by simp) hscNe
  have hNegFunEq :
      __eo_mk_apply (Term.UOp UserOp.neg)
          (__eo_mk_apply (Term.UOp UserOp.str_len) sc) =
        Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) sc) := by
    rw [hLenScEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) sc)
      (by simp) (by simp)
  have hNegEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) sc)) k := by
    rw [hNegFunEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) sc)) k
      (by simp) hKNe
  have hNegNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k ≠
        Term.Stuck := by
    rw [hNegEq]
    simp
  have hSubMidEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.neg)
              (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_substr) sc)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) sc)) k) := by
    rw [hSubFunEq, hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) sc)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) sc)) k)
      (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_substr) sc)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.neg)
                (__eo_mk_apply (Term.UOp UserOp.str_len) sc)) k)) k =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k := by
    rw [hSubMidEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.str_substr) sc)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k
      (by simp) hKNe
  have hEndEq :
      concatCPropReverseEnd (Term.Boolean true) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc)) k)) k := by
    dsimp [concatCPropReverseEnd, sc, k]
    rw [hOuterEq]
  have hLenScTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt sc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt sc) T (by simpa [sc] using hscTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k)) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k)
      hLenScTy hKTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt sc)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
            (__eo_to_smt k)) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt sc)
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
      (__eo_to_smt k) T (by simpa [sc] using hscTy) hNegTy hKTy
  rw [hEndEq]
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt sc)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc)) (__eo_to_smt k))
          (__eo_to_smt k)) =
      SmtType.Seq T
  exact hSubTy

private theorem cprop_reverse_suffix_true_seq_type
    (t s tc : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hEndTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (concatCPropReverseSuffix (Term.Boolean true) t s tc)) =
      SmtType.Seq T := by
  let endPart := concatCPropReverseEnd (Term.Boolean true) t s
  have hEndNe : endPart ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck endPart T (by simpa [endPart] using hEndTy)
  have hLenEndEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart =
        Term.Apply (Term.UOp UserOp.str_len) endPart :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) endPart (by simp) hEndNe
  have hLenEndNe :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart ≠ Term.Stuck := by
    rw [hLenEndEq]
    simp
  have hNegEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart) := by
    rw [hLenEndEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) endPart) (by simp) (by simp)
  have hNegNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) ≠
        Term.Stuck := by
    rw [hNegEq]
    simp
  have hOuterEq :
      __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) endPart)) := by
    rw [hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) endPart)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropReverseSuffix (Term.Boolean true) t s tc =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart))) := by
    change
      __eo_mk_apply (Term.UOp UserOp._at_purify)
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart))) =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart)))
    rw [hOuterEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp._at_purify)
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Numeral 0))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart)))
      (by simp) (by simp)
  have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_2]
  have hLenTcTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt tc)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt tc) T htcTy
  have hLenEndTy :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt endPart)) = SmtType.Int :=
    smtx_typeof_str_len_seq (__eo_to_smt endPart) T
      (by simpa [endPart] using hEndTy)
  have hNegTy :
      __smtx_typeof
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
            (SmtTerm.str_len (__eo_to_smt endPart))) =
        SmtType.Int :=
    smtx_typeof_neg_int (SmtTerm.str_len (__eo_to_smt tc))
      (SmtTerm.str_len (__eo_to_smt endPart)) hLenTcTy hLenEndTy
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart)))) =
        SmtType.Seq T :=
    smtx_typeof_str_substr_seq (__eo_to_smt tc) (SmtTerm.Numeral 0)
      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
        (SmtTerm.str_len (__eo_to_smt endPart))) T htcTy hZeroTy hNegTy
  rw [hSuffixEq]
  change
    __smtx_typeof
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart))))) =
      SmtType.Seq T
  simpa [__smtx_typeof] using hSubTy

private theorem cprop_suffix_false_eval_of_prefix_eval
    (M : SmtModel) (hM : model_wf M)
    (t s tc : Term) (T : SmtType) (st spfx : SmtSeq)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hPrefixTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtType.Seq T)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hPrefixEval :
      __smtx_model_eval M
          (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
        SmtValue.Seq spfx)
    (hle : (native_unpack_seq spfx).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropSuffix (Term.Boolean false) t s tc)) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).drop (native_unpack_seq spfx).length)) := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  have hpfxNe : pfx ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck pfx T (by simpa [pfx] using hPrefixTy)
  have hLenPfxEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) pfx =
        Term.Apply (Term.UOp UserOp.str_len) pfx :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) pfx (by simp) hpfxNe
  have hSubMidEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.str_substr) tc)
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hNegLenEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) pfx) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx) := by
    rw [hLenPfxEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) pfx) (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Apply (Term.UOp UserOp.str_len) pfx))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) pfx)) := by
    rw [hSubMidEq, hNegLenEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Apply (Term.UOp UserOp.str_len) pfx))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) pfx)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropSuffix (Term.Boolean false) t s tc =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Apply (Term.UOp UserOp.str_len) pfx))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) pfx))) := by
    dsimp [concatCPropSuffix, pfx]
    rw [hOuterEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp._at_purify)
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Apply (Term.UOp UserOp.str_len) pfx))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) pfx)))
      (by simp) (by simp)
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hSub :
      native_seq_extract (native_unpack_seq st)
          (Int.ofNat (native_unpack_seq spfx).length)
          (Int.ofNat
            ((native_unpack_seq st).length - (native_unpack_seq spfx).length)) =
        (native_unpack_seq st).drop (native_unpack_seq spfx).length :=
    native_seq_extract_to_end_nat (native_unpack_seq st)
      (native_unpack_seq spfx).length hle
  have hDiff :
      Int.ofNat
          ((native_unpack_seq st).length - (native_unpack_seq spfx).length) =
        Int.ofNat (native_unpack_seq st).length -
          Int.ofNat (native_unpack_seq spfx).length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq st)
          (Int.ofNat (native_unpack_seq spfx).length)
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq spfx).length) =
        (native_unpack_seq st).drop (native_unpack_seq spfx).length := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [Int.sub_eq_add_neg] using hSub'
  rw [hSuffixEq]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc)
            (SmtTerm.str_len (__eo_to_smt pfx))
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt pfx))))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).drop (native_unpack_seq spfx).length))
  simp [pfx, htcEval, hPrefixEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
    __smtx_model_eval__at_purify, __smtx_model_eval__,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

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

private theorem cprop_prefix_false_eval_of_overlap
    (M : SmtModel) (hM : model_wf M)
    (t s sc : Term) (T : SmtType) (ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat n)) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropPrefix (Term.Boolean false) t s)) =
      SmtValue.Seq
        (native_pack_seq T ((native_unpack_seq ss).take n)) := by
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T hscTy
  have hPrefixEq :
      concatCPropPrefix (Term.Boolean false) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Numeral 0))
          (Term.Numeral (Int.ofNat n)) := by
    dsimp [concatCPropPrefix, k]
    rw [← hScEq, hOverlap]
    simp [__eo_mk_apply]
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have hSub :
      native_seq_extract (native_unpack_seq ss) 0 (Int.ofNat n) =
        (native_unpack_seq ss).take n :=
    native_seq_extract_zero_nat_any (native_unpack_seq ss) n
  rw [hPrefixEq]
  change
    __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt sc) (SmtTerm.Numeral 0)
          (SmtTerm.Numeral (Int.ofNat n))) =
      SmtValue.Seq (native_pack_seq T ((native_unpack_seq ss).take n))
  simp [hscEval, __smtx_model_eval, __smtx_model_eval_str_substr,
    hElem]
  exact congrArg (native_pack_seq T) hSub

private theorem native_seq_extract_suffix_nat_suffix
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
    have hltInt : (Int.ofNat xs.length : Int) < Int.ofNat n :=
      Int.ofNat_lt.mpr hlt
    have hStartNeg :
        Int.ofNat xs.length + -Int.ofNat n < 0 := by
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

private theorem native_seq_extract_length_le_nat_arg
    (xs : List SmtValue) (i : native_Int) (n : Nat) :
    (native_seq_extract xs i (Int.ofNat n)).length <= n := by
  have hInt :
      Int.ofNat (native_seq_extract xs i (Int.ofNat n)).length <=
        Int.ofNat n := by
    simp only [native_seq_extract]
    split
    · simp
    · rename_i h
      have hProp :
          ¬ ((i < 0 ∨ Int.ofNat n <= 0) ∨
              Int.ofNat xs.length <= i) := by
        simpa [Bool.or_eq_true, decide_eq_true_eq] using h
      have hiNonneg : 0 <= i := by
        have hiNot : ¬ i < 0 := by
          intro hi
          exact hProp (Or.inl (Or.inl hi))
        exact Int.le_of_not_gt hiNot
      have hiLt : i < Int.ofNat xs.length := by
        have hiNot : ¬ Int.ofNat xs.length <= i := by
          intro hle
          exact hProp (Or.inr hle)
        exact Int.lt_of_not_ge hiNot
      have hTake :
          ((xs.drop (Int.toNat i)).take
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i)))).length <=
            Int.toNat (min (Int.ofNat n) (Int.ofNat xs.length - i)) :=
        List.length_take_le _ _
      have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by
        omega
      have hMinNonneg :
          0 <= min (Int.ofNat n) (Int.ofNat xs.length - i) := by
        exact (Int.le_min).2 ⟨Int.natCast_nonneg n, hDiffNonneg⟩
      have hCast :
          Int.ofNat
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i))) =
            min (Int.ofNat n) (Int.ofNat xs.length - i) :=
        Int.toNat_of_nonneg hMinNonneg
      have hLenLe :
          Int.ofNat
              ((xs.drop (Int.toNat i)).take
                (Int.toNat
                  (min (Int.ofNat n)
                    (Int.ofNat xs.length - i)))).length <=
            Int.ofNat
              (Int.toNat
                (min (Int.ofNat n) (Int.ofNat xs.length - i))) :=
        Int.ofNat_le.mpr hTake
      have hMinLe :
          min (Int.ofNat n) (Int.ofNat xs.length - i) <=
            Int.ofNat n :=
        Int.min_le_left _ _
      omega
  exact Int.ofNat_le.mp hInt

private theorem concat_cprop_tail_eq_drop_append_of_append_eq_of_le
    {α : Type} (xs xtail ys ytail : List α)
    (h : xs ++ xtail = ys ++ ytail) (hle : xs.length <= ys.length) :
    xtail = ys.drop xs.length ++ ytail := by
  have hYs :
      ys = xs ++ ys.drop xs.length :=
    concat_split_left_eq_append_drop_of_append_eq_of_le ys xs ytail xtail
      (by simpa using h.symm) hle
  rw [hYs] at h
  rw [List.append_assoc] at h
  exact List.append_cancel_left h

private theorem cprop_reverse_end_true_eval_of_overlap
    (M : SmtModel) (hM : model_wf M)
    (t s sc : Term) (T : SmtType) (ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat n)) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
      SmtValue.Seq
        (native_pack_seq T
          (native_seq_extract (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
            (Int.ofNat n))) := by
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hscNe : sc ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck sc T hscTy
  have hEndEq :
      concatCPropReverseEnd (Term.Boolean true) t s =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_substr) sc)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) sc))
              (Term.Numeral (Int.ofNat n))))
          (Term.Numeral (Int.ofNat n)) := by
    dsimp [concatCPropReverseEnd, k]
    rw [← hScEq, hOverlap]
    simp [__eo_mk_apply]
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  rw [hEndEq]
  change
    __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt sc)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt sc))
            (SmtTerm.Numeral (Int.ofNat n)))
          (SmtTerm.Numeral (Int.ofNat n))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_seq_extract (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
            (Int.ofNat n)))
  simp [hscEval, __smtx_model_eval, __smtx_model_eval_str_len,
    __smtx_model_eval_str_substr, __smtx_model_eval__, native_seq_len,
    native_zplus, native_zneg, hElem]

private theorem cprop_reverse_suffix_true_eval_of_end_eval
    (M : SmtModel) (hM : model_wf M)
    (t s tc : Term) (T : SmtType) (st send : SmtSeq)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hEndTy :
      __smtx_typeof
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtType.Seq T)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hEndEval :
      __smtx_model_eval M
          (__eo_to_smt (concatCPropReverseEnd (Term.Boolean true) t s)) =
        SmtValue.Seq send)
    (hle : (native_unpack_seq send).length <= (native_unpack_seq st).length) :
    __smtx_model_eval M
        (__eo_to_smt (concatCPropReverseSuffix (Term.Boolean true) t s tc)) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - (native_unpack_seq send).length))) := by
  let endPart := concatCPropReverseEnd (Term.Boolean true) t s
  have hEndNe : endPart ≠ Term.Stuck :=
    cprop_seq_type_ne_stuck endPart T (by simpa [endPart] using hEndTy)
  have hLenEndEq :
      __eo_mk_apply (Term.UOp UserOp.str_len) endPart =
        Term.Apply (Term.UOp UserOp.str_len) endPart :=
    cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp.str_len) endPart (by simp) hEndNe
  have hNegEq :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (__eo_mk_apply (Term.UOp UserOp.str_len) endPart) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart) := by
    rw [hLenEndEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp.str_len) tc))
      (Term.Apply (Term.UOp UserOp.str_len) endPart) (by simp) (by simp)
  have hOuterEq :
      __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)) =
        Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (Term.Apply (Term.UOp UserOp.str_len) endPart)) := by
    rw [hNegEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp.str_len) tc))
        (Term.Apply (Term.UOp UserOp.str_len) endPart)) (by simp) (by simp)
  have hSuffixEq :
      concatCPropReverseSuffix (Term.Boolean true) t s tc =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart))) := by
    change
      __eo_mk_apply (Term.UOp UserOp._at_purify)
        (__eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
            (Term.Numeral 0))
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp.str_len) tc))
            (__eo_mk_apply (Term.UOp UserOp.str_len) endPart))) =
        Term.Apply (Term.UOp UserOp._at_purify)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
              (Term.Numeral 0))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp.str_len) tc))
              (Term.Apply (Term.UOp UserOp.str_len) endPart)))
    rw [hOuterEq]
    exact cprop_mk_apply_eq_apply_of_args_ne_stuck
      (Term.UOp UserOp._at_purify)
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
          (Term.Numeral 0))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp.str_len) tc))
          (Term.Apply (Term.UOp UserOp.str_len) endPart)))
      (by simp) (by simp)
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hSub :
      native_seq_extract (native_unpack_seq st) 0
          (Int.ofNat
            ((native_unpack_seq st).length - (native_unpack_seq send).length)) =
        (native_unpack_seq st).take
          ((native_unpack_seq st).length - (native_unpack_seq send).length) :=
    native_seq_extract_zero_nat (native_unpack_seq st)
      ((native_unpack_seq st).length - (native_unpack_seq send).length)
      (Nat.sub_le _ _)
  have hDiff :
      Int.ofNat
          ((native_unpack_seq st).length - (native_unpack_seq send).length) =
        Int.ofNat (native_unpack_seq st).length -
          Int.ofNat (native_unpack_seq send).length :=
    Int.ofNat_sub hle
  have hSubEval :
      native_seq_extract (native_unpack_seq st) 0
          (Int.ofNat (native_unpack_seq st).length +
            -Int.ofNat (native_unpack_seq send).length) =
        (native_unpack_seq st).take
          ((native_unpack_seq st).length - (native_unpack_seq send).length) := by
    have hSub' := hSub
    rw [hDiff] at hSub'
    simpa [Int.sub_eq_add_neg] using hSub'
  rw [hSuffixEq]
  change
    __smtx_model_eval M
        (SmtTerm._at_purify
          (SmtTerm.str_substr (__eo_to_smt tc) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt tc))
              (SmtTerm.str_len (__eo_to_smt endPart))))) =
      SmtValue.Seq
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - (native_unpack_seq send).length)))
  simp [endPart, htcEval, hEndEval, __smtx_model_eval,
    __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
    __smtx_model_eval__at_purify, __smtx_model_eval__,
    native_seq_len, native_zplus, native_zneg, hElem]
  exact congrArg (native_pack_seq T) hSubEval

private theorem cprop_length_ne_zero_of_not_len_eq_eval
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

private theorem cprop_false_formula_of_overlap_bounds
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc tTail sTail : Term) (T : SmtType)
    (st stail ss sstail : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (htTailEval :
      __smtx_model_eval M (__eo_to_smt tTail) = SmtValue.Seq stail)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hsTailEval :
      __smtx_model_eval M (__eo_to_smt sTail) = SmtValue.Seq sstail)
    (hAppend :
      native_unpack_seq st ++ native_unpack_seq stail =
        native_unpack_seq ss ++ native_unpack_seq sstail)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat n))
    (hnPfx :
      ((native_unpack_seq ss).take n).length <=
        (native_unpack_seq st).length) :
    eo_interprets M (concatCPropFormula (Term.Boolean false) t s tc) true := by
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  let sfx := concatCPropSuffix (Term.Boolean false) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
  let tail := mkConcat sfx nil
  let rhs := mkConcat pfx tail
  have hPfxTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [pfx, hScEq] using cprop_prefix_false_seq_type t s tc T
      (by simpa [hScEq] using hscTy) hProg
  have hSfxTy : __smtx_typeof (__eo_to_smt sfx) = SmtType.Seq T := by
    simpa [sfx] using cprop_suffix_false_seq_type t s tc T htcTy hPfxTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq pfx T hPfxTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq sfx nil T hSfxTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq pfx tail T hPfxTy hTailTy
  have hpfxEval :
      __smtx_model_eval M (__eo_to_smt pfx) =
        SmtValue.Seq (native_pack_seq T ((native_unpack_seq ss).take n)) := by
    simpa [pfx] using cprop_prefix_false_eval_of_overlap M hM t s sc T ss n
      hScEq hscTy hscEval hOverlap
  have hsfxEval :
      __smtx_model_eval M (__eo_to_smt sfx) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).drop ((native_unpack_seq ss).take n).length)) := by
    have hDrop :
        (native_unpack_seq
              (native_pack_seq T ((native_unpack_seq ss).take n))).length <=
          (native_unpack_seq st).length := by
      simpa [_root_.native_unpack_pack_seq] using hnPfx
    have hEval :=
      cprop_suffix_false_eval_of_prefix_eval M hM t s tc T st
        (native_pack_seq T ((native_unpack_seq ss).take n)) htcTy
        (by simpa [pfx] using hPfxTy) htcEval (by simpa [pfx] using hpfxEval)
        hDrop
    simpa [sfx, _root_.native_unpack_pack_seq] using hEval
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M pfx T hPfxTy
  have hPfxElem :
      __smtx_elem_typeof_seq_value
          (native_pack_seq T ((native_unpack_seq ss).take n)) = T :=
    elem_typeof_pack_seq T ((native_unpack_seq ss).take n)
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq ss).take n ++
              (native_unpack_seq st).drop ((native_unpack_seq ss).take n).length ++
              native_unpack_seq (SmtSeq.empty T))) := by
    simpa [rhs, tail, _root_.native_unpack_pack_seq] using
      eval_mkConcat_right_nested M pfx sfx nil T
        (native_pack_seq T ((native_unpack_seq ss).take n))
        (native_pack_seq T
          ((native_unpack_seq st).drop ((native_unpack_seq ss).take n).length))
        (SmtSeq.empty T) hpfxEval hsfxEval hNilEval hPfxElem
  have hTakeEq :
      (native_unpack_seq ss).take n =
        (native_unpack_seq st).take ((native_unpack_seq ss).take n).length := by
    let p := ((native_unpack_seq ss).take n).length
    have hpSs : p <= (native_unpack_seq ss).length := by
      simp [p, List.length_take]
      exact Nat.min_le_right n (native_unpack_seq ss).length
    have hTakeSsP :
        (native_unpack_seq ss).take p = (native_unpack_seq ss).take n := by
      let xs := native_unpack_seq ss
      change xs.take (xs.take n).length = xs.take n
      by_cases hle : n <= xs.length
      · have hLen : (xs.take n).length = n := by
          simp [List.length_take, Nat.min_eq_left hle]
        rw [hLen]
      · have hLenLe : xs.length <= n :=
          Nat.le_of_lt (Nat.lt_of_not_ge hle)
        have hLen : (xs.take n).length = xs.length := by
          simp [List.length_take, Nat.min_eq_right hLenLe]
        rw [hLen, List.take_of_length_le (Nat.le_refl xs.length),
          List.take_of_length_le hLenLe]
    have hTake := congrArg (List.take p) hAppend
    rw [List.take_append_of_le_length hnPfx,
      List.take_append_of_le_length hpSs] at hTake
    exact (hTake.trans hTakeSsP).symm
  have hRhsEvalTc :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T (native_unpack_seq st)) := by
    let p := ((native_unpack_seq ss).take n).length
    have hList :
        (native_unpack_seq ss).take n ++
            (native_unpack_seq st).drop ((native_unpack_seq ss).take n).length ++
            native_unpack_seq (SmtSeq.empty T) =
          native_unpack_seq st := by
      change
        ((native_unpack_seq ss).take n ++
            (native_unpack_seq st).drop p) ++ [] =
          native_unpack_seq st
      rw [hTakeEq]
      change
        ((native_unpack_seq st).take p ++
            (native_unpack_seq st).drop p) ++ [] =
          native_unpack_seq st
      simp [List.take_append_drop]
    rw [hRhsEval]
    exact congrArg SmtValue.Seq (congrArg (native_pack_seq T) hList)
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [htcEval, hRhsEvalTc]
    change RuleProofs.smt_seq_rel st (native_pack_seq T (native_unpack_seq st))
    have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
      have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
        (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
      simpa [htcEval, __smtx_typeof_value] using htcValTy
    exact smt_seq_rel_pack_unpack T st
      (elem_typeof_seq_value_of_typeof_seq_value hstTy)
  have hEqTrue : eo_interprets M (mkEq tc rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhs hEqBool hRel
  have hpfxNe : pfx ≠ Term.Stuck := cprop_seq_type_ne_stuck pfx T hPfxTy
  have hsfxNe : sfx ≠ Term.Stuck := cprop_seq_type_ne_stuck sfx T hSfxTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) sfx =
          Term.Apply (Term.UOp UserOp.str_concat) sfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) sfx (by simp) hsfxNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) sfx) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) pfx =
          Term.Apply (Term.UOp UserOp.str_concat) pfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) pfx (by simp) hpfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) pfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean false) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_false, pfx, sfx, nil] using hEqGenEq
  simpa [hFormulaEq] using hEqTrue

private theorem cprop_true_formula_of_overlap_bounds
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc tPrefix sPrefix : Term) (T : SmtType)
    (stp st ssp ss : SmtSeq) (n : Nat)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htPrefixEval :
      __smtx_model_eval M (__eo_to_smt tPrefix) = SmtValue.Seq stp)
    (htcEval : __smtx_model_eval M (__eo_to_smt tc) = SmtValue.Seq st)
    (hsPrefixEval :
      __smtx_model_eval M (__eo_to_smt sPrefix) = SmtValue.Seq ssp)
    (hscEval : __smtx_model_eval M (__eo_to_smt sc) = SmtValue.Seq ss)
    (hAppend :
      native_unpack_seq stp ++ native_unpack_seq st =
        native_unpack_seq ssp ++ native_unpack_seq ss)
    (hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat n))
    (hnEnd :
      (native_seq_extract (native_unpack_seq ss)
          (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n)
          (Int.ofNat n)).length <=
        (native_unpack_seq st).length) :
    eo_interprets M (concatCPropFormula (Term.Boolean true) t s tc) true := by
  let rEnd := concatCPropReverseEnd (Term.Boolean true) t s
  let rSfx := concatCPropReverseSuffix (Term.Boolean true) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof rSfx)
  let tail := mkConcat rEnd nil
  let rhs := mkConcat rSfx tail
  let endList :=
    native_seq_extract (native_unpack_seq ss)
      (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat n) (Int.ofNat n)
  have hEndTy : __smtx_typeof (__eo_to_smt rEnd) = SmtType.Seq T := by
    simpa [rEnd] using cprop_reverse_end_true_seq_type t s tc T
      (by simpa [hScEq] using hscTy) hProg
  have hSfxTy : __smtx_typeof (__eo_to_smt rSfx) = SmtType.Seq T := by
    simpa [rSfx] using cprop_reverse_suffix_true_seq_type t s tc T
      htcTy hEndTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq rSfx T hSfxTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq rEnd nil T hEndTy hNilTy
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq rSfx tail T hSfxTy hTailTy
  have hEndEval :
      __smtx_model_eval M (__eo_to_smt rEnd) =
        SmtValue.Seq (native_pack_seq T endList) := by
    simpa [rEnd, endList] using
      cprop_reverse_end_true_eval_of_overlap M hM t s sc T ss n
        hScEq hscTy hscEval hOverlap
  have hSfxEval :
      __smtx_model_eval M (__eo_to_smt rSfx) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length))) := by
    have hEndDrop :
        (native_unpack_seq (native_pack_seq T endList)).length <=
          (native_unpack_seq st).length := by
      simpa [endList, _root_.native_unpack_pack_seq] using hnEnd
    have hEval :=
      cprop_reverse_suffix_true_eval_of_end_eval M hM t s tc T st
        (native_pack_seq T endList) htcTy hEndTy htcEval
        (by simpa [rEnd, endList] using hEndEval) hEndDrop
    simpa [rSfx, endList, _root_.native_unpack_pack_seq] using hEval
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nil] using eval_nil_str_concat_typeof_of_smt_type_seq M rSfx T hSfxTy
  have hSfxElem :
      __smtx_elem_typeof_seq_value
          (native_pack_seq T
            ((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length))) = T :=
    elem_typeof_pack_seq T
      ((native_unpack_seq st).take
        ((native_unpack_seq st).length - endList.length))
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq
          (native_pack_seq T
            ((native_unpack_seq st).take
                ((native_unpack_seq st).length - endList.length) ++
              endList ++ native_unpack_seq (SmtSeq.empty T))) := by
    simpa [rhs, tail, _root_.native_unpack_pack_seq] using
      eval_mkConcat_right_nested M rSfx rEnd nil T
        (native_pack_seq T
          ((native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length)))
        (native_pack_seq T endList) (SmtSeq.empty T) hSfxEval hEndEval
        hNilEval hSfxElem
  rcases native_seq_extract_suffix_nat_suffix (native_unpack_seq ss) n with
    ⟨ssPre, hSsPre⟩
  have hSuffixSt :
      native_unpack_seq st =
        (native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length) ++
          endList := by
    have hAppendEnd :
        native_unpack_seq stp ++ native_unpack_seq st =
          (native_unpack_seq ssp ++ ssPre) ++ endList := by
      rw [hAppend]
      change
        native_unpack_seq ssp ++ native_unpack_seq ss =
          (native_unpack_seq ssp ++ ssPre) ++ endList
      rw [hSsPre]
      simp [List.append_assoc, endList]
    exact concat_split_suffix_eq_take_append_of_append_eq_of_le
      (native_unpack_seq stp) (native_unpack_seq st)
      (native_unpack_seq ssp ++ ssPre) endList hAppendEnd hnEnd
  have hRhsEvalTc :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.Seq (native_pack_seq T (native_unpack_seq st)) := by
    have hList :
        (native_unpack_seq st).take
            ((native_unpack_seq st).length - endList.length) ++
          endList ++ native_unpack_seq (SmtSeq.empty T) =
        native_unpack_seq st := by
      change
        (((native_unpack_seq st).take
              ((native_unpack_seq st).length - endList.length) ++
            endList) ++ []) =
          native_unpack_seq st
      rw [← hSuffixSt]
      simp
    rw [hRhsEval]
    exact congrArg SmtValue.Seq (congrArg (native_pack_seq T) hList)
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt tc))
        (__smtx_model_eval M (__eo_to_smt rhs)) := by
    rw [htcEval, hRhsEvalTc]
    change RuleProofs.smt_seq_rel st (native_pack_seq T (native_unpack_seq st))
    have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
      have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
        (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
      simpa [htcEval, __smtx_typeof_value] using htcValTy
    exact smt_seq_rel_pack_unpack T st
      (elem_typeof_seq_value_of_typeof_seq_value hstTy)
  have hEqTrue : eo_interprets M (mkEq tc rhs) true :=
    RuleProofs.eo_interprets_eq_of_rel M tc rhs hEqBool hRel
  have hSfxNe : rSfx ≠ Term.Stuck := cprop_seq_type_ne_stuck rSfx T hSfxTy
  have hEndNe : rEnd ≠ Term.Stuck := cprop_seq_type_ne_stuck rEnd T hEndTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rEnd =
          Term.Apply (Term.UOp UserOp.str_concat) rEnd :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rEnd (by simp) hEndNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rEnd) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rSfx =
          Term.Apply (Term.UOp UserOp.str_concat) rSfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rSfx (by simp) hSfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rSfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean true) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_true, rSfx, rEnd, nil] using hEqGenEq
  simpa [hFormulaEq] using hEqTrue

private theorem facts_concat_cprop_false_formula
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc tTail sTail : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean false) s)
    (hIntroT : __str_nary_intro t = mkConcat tc tTail)
    (hIntroS : __str_nary_intro s = mkConcat sc sTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hSTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true) :
    eo_interprets M (concatCPropFormula (Term.Boolean false) t s tc) true := by
  rcases concat_split_append_eq_of_concat_eq M hM tc tTail sc sTail T
      htcTy htTailTy hscTy hsTailTy hConcatEq with
    ⟨st, stail, ss, sstail, htcEval, htTailEval, hscEval, hsTailEval,
      hAppend⟩
  have htcLenNe : (native_unpack_seq st).length ≠ 0 :=
    cprop_length_ne_zero_of_not_len_eq_eval M tc st htcEval hNonzero
  let recS := concatCPropSHeadTailWord (Term.Boolean false) s
  let recT := concatCPropFlatSecond (Term.Boolean false) t
  let k := concatCPropOverlapLen (Term.Boolean false) t s
  have hPrefixNe := cprop_prefix_false_ne_of_prog t s tc hProg
  have hKNe : k ≠ Term.Stuck := by
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by simpa [k, concatCPropPrefix] using hPrefixNe)
  have hRecNe : __str_overlap_rec recS recT ≠ Term.Stuck := by
    apply cprop_eo_add_one_arg_ne_stuck
    simpa [k, recS, recT, concatCPropOverlapLen, eo_ite_false] using hKNe
  have hRecSNe : recS ≠ Term.Stuck :=
    str_overlap_rec_left_ne_stuck_of_ne_stuck recS recT hRecNe
  have hRecTNe : recT ≠ Term.Stuck :=
    str_overlap_rec_right_ne_stuck_of_ne_stuck recS recT hRecNe
  rcases cprop_false_head_string_of_tailword_ne s sc T hScEq hscTy
      (by simpa [recS] using hRecSNe) with
    ⟨scWord, hScString⟩
  have hSsWord :
      native_unpack_seq ss = scWord.map SmtValue.Char := by
    exact string_eval_unpack_eq M scWord ss (by simpa [hScString] using hscEval)
  rcases cprop_flat_second_false_tail_head_of_ne_stuck t tc tTail
      hIntroT hTTailList (by simpa [recT] using hRecTNe) with
    ⟨tSecond, tSecondTail, hTTailHead, hTSecondTailList, hRecTEq⟩
  have htTailConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat tSecond tSecondTail)) =
        SmtType.Seq T := by
    simpa [hTTailHead] using htTailTy
  rcases str_concat_args_of_seq_type tSecond tSecondTail T htTailConsTy with
    ⟨htSecondTy, htSecondTailTy⟩
  have htTailConsEval :
      __smtx_model_eval M (__eo_to_smt (mkConcat tSecond tSecondTail)) =
        SmtValue.Seq stail := by
    simpa [hTTailHead] using htTailEval
  rcases strConcat_args_seq_eval_of_concat_seq_eval M tSecond tSecondTail
      ⟨stail, htTailConsEval⟩ with
    ⟨⟨stSecond, htSecondEval⟩,
      ⟨stSecondTail, htSecondTailEval⟩⟩
  have hStailSplit :
      native_unpack_seq stail =
        native_unpack_seq stSecond ++ native_unpack_seq stSecondTail :=
    mkConcat_eval_unpack_eq M tSecond tSecondTail stail stSecond
      stSecondTail htTailConsEval htSecondEval htSecondTailEval
  rcases str_overlap_rec_numeral_of_ne_stuck recS recT hRecNe with
    ⟨m, hRec⟩
  have hOverlap :
      concatCPropOverlapLen (Term.Boolean false) t s =
        Term.Numeral (Int.ofNat (m + 1)) := by
    simp [concatCPropOverlapLen, eo_ite_false, recS, recT, hRec, __eo_add,
      native_zplus]
    rw [Int.add_comm]
  have hnPfx :
      ((native_unpack_seq ss).take (m + 1)).length <=
        (native_unpack_seq st).length := by
    by_cases hleSS :
        (native_unpack_seq ss).length <= (native_unpack_seq st).length
    · have hTakeLeSS :
          ((native_unpack_seq ss).take (m + 1)).length <=
            (native_unpack_seq ss).length := by
        simp [List.length_take]
        exact Nat.min_le_right (m + 1) (native_unpack_seq ss).length
      exact Nat.le_trans hTakeLeSS hleSS
    · by_cases hGoal :
          ((native_unpack_seq ss).take (m + 1)).length <=
            (native_unpack_seq st).length
      · exact hGoal
      have hstPos : 0 < (native_unpack_seq st).length :=
        Nat.pos_of_ne_zero htcLenNe
      have hstLeSs :
          (native_unpack_seq st).length <= (native_unpack_seq ss).length :=
        Nat.le_of_lt (Nat.lt_of_not_ge hleSS)
      have hStailBoundary :
          native_unpack_seq stail =
            (native_unpack_seq ss).drop (native_unpack_seq st).length ++
              native_unpack_seq sstail :=
        concat_cprop_tail_eq_drop_append_of_append_eq_of_le
          (native_unpack_seq st) (native_unpack_seq stail)
          (native_unpack_seq ss) (native_unpack_seq sstail)
          hAppend hstLeSs
      have hStailBoundaryWord :
          native_unpack_seq stail =
            (scWord.map SmtValue.Char).drop (native_unpack_seq st).length ++
              native_unpack_seq sstail := by
        simpa [hSsWord] using hStailBoundary
      have hDropLt : (native_unpack_seq st).length - 1 < m := by
        have hTakeLen :
            ((native_unpack_seq ss).take (m + 1)).length =
              min (m + 1) (native_unpack_seq ss).length := by
          simp [List.length_take]
        rw [hTakeLen] at hGoal
        omega
      have hCompatFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT =
            Term.Boolean false :=
        str_overlap_rec_compatible_drop_false_of_lt recS recT m
          ((native_unpack_seq st).length - 1) hRec hDropLt
      have hCompatNotFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT ≠
            Term.Boolean false := by
        intro hBad
        dsimp [recS, recT] at hBad
        simp only [concatCPropSHeadTailWord, concatCPropFlatSecond] at hBad
        rw [show concatCPropHead (Term.Boolean false) s = Term.String scWord by
          rw [← hScEq, hScString]] at hBad
        simp [eo_ite_false, hRecTEq] at hBad
        cases scWord with
        | nil =>
            have hSsLen : (native_unpack_seq ss).length = 0 := by
              simp [hSsWord]
            omega
        | cons c cs =>
            rw [eo_extract_tail_len_cons c cs] at hBad
            cases cs with
            | nil =>
                exact str_is_compatible_empty_left_ne_false
                  (__str_flatten (__str_nary_intro tSecond))
                  (by simpa [RuleProofs.str_flatten_nary_intro_empty,
                    strConcatDrop_string_empty] using hBad)
            | cons d ds =>
                rw [RuleProofs.str_flatten_nary_intro_cons d ds] at hBad
                have hDropLeTail :
                    (native_unpack_seq st).length - 1 <=
                      (d :: ds).length := by
                  have hSsLen :
                      (native_unpack_seq ss).length =
                        (d :: ds).length + 1 := by
                    simp [hSsWord]
                  omega
                rw [strConcatDrop_substrWord (d :: ds) (d :: ds).length
                  ((native_unpack_seq st).length - 1) 0 hDropLeTail] at hBad
                let kDrop := (native_unpack_seq st).length - 1
                let suf := (d :: ds).drop kDrop
                have hSubDrop :
                    RuleProofs.substrWord (d :: ds) (0 + Int.ofNat kDrop)
                        ((d :: ds).length - kDrop) =
                      RuleProofs.substrWord suf 0 suf.length := by
                  simpa [kDrop, suf] using
                    substrWord_drop_suffix (d :: ds) kDrop hDropLeTail
                rw [hSubDrop] at hBad
                have hDropMap :
                    (List.map SmtValue.Char (c :: d :: ds)).drop
                        (native_unpack_seq st).length =
                      suf.map SmtValue.Char := by
                  dsimp [suf, kDrop]
                  cases hLen : (native_unpack_seq st).length with
                  | zero =>
                      omega
                  | succ k =>
                      simp
                have hAlign :
                    native_unpack_seq stSecond ++
                        native_unpack_seq stSecondTail =
                      suf.map SmtValue.Char ++ native_unpack_seq sstail := by
                  rw [← hStailSplit, hStailBoundaryWord, hDropMap]
                exact
                  str_is_compatible_full_word_flatten_intro_ne_false_of_append_eval
                    M hM tSecond T stSecond suf
                    (native_unpack_seq stSecondTail)
                    (native_unpack_seq sstail) htSecondTy htSecondEval
                    hAlign hBad
      exact False.elim (hCompatNotFalse hCompatFalse)
  exact cprop_false_formula_of_overlap_bounds M hM t s tc sc tTail sTail T
    st stail ss sstail (m + 1) hScEq htcTy hscTy htTailTy hsTailTy hProg
    htcEval htTailEval hscEval hsTailEval hAppend hOverlap hnPfx

private theorem facts_concat_cprop_true_formula
    (M : SmtModel) (hM : model_wf M)
    (t s tc sc tPrefix sPrefix tTail sTail : Term) (T : SmtType)
    (hScEq : sc = concatCPropHead (Term.Boolean true) s)
    (hRevIntroT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        mkConcat tc tTail)
    (hRevIntroS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat sc sTail)
    (hTTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tTail = Term.Boolean true)
    (hSTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) sTail = Term.Boolean true)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hNonzero :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true)
    (hTPrefixConsEq :
      ∀ a aTail, tTail = mkConcat a aTail ->
        tPrefix =
          __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) tTail))
    (hSPrefixConsEq :
      ∀ a aTail, sTail = mkConcat a aTail ->
        sPrefix =
          __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) sTail)) :
    eo_interprets M (concatCPropFormula (Term.Boolean true) t s tc) true := by
  rcases concat_split_append_eq_of_concat_eq M hM tPrefix tc sPrefix sc T
      htPrefixTy htcTy hsPrefixTy hscTy hConcatEq with
    ⟨stp, st, ssp, ss, htPrefixEval, htcEval, hsPrefixEval, hscEval,
      hAppend⟩
  have htcLenNe : (native_unpack_seq st).length ≠ 0 :=
    cprop_length_ne_zero_of_not_len_eq_eval M tc st htcEval hNonzero
  let recS :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (concatCPropSHeadTailWord (Term.Boolean true) s)
  let recT :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (concatCPropFlatSecond (Term.Boolean true) t)
  let k := concatCPropOverlapLen (Term.Boolean true) t s
  have hEndNe := cprop_reverse_end_true_ne_of_prog t s tc hProg
  have hKNe : k ≠ Term.Stuck := by
    exact cprop_mk_apply_arg_ne_stuck_of_ne_stuck _ _
      (by simpa [k, concatCPropReverseEnd] using hEndNe)
  have hRecNe : __str_overlap_rec recS recT ≠ Term.Stuck := by
    apply cprop_eo_add_one_arg_ne_stuck
    simpa [k, recS, recT, concatCPropOverlapLen, eo_ite_true] using hKNe
  have hRecSNe : recS ≠ Term.Stuck :=
    str_overlap_rec_left_ne_stuck_of_ne_stuck recS recT hRecNe
  have hRecTNe : recT ≠ Term.Stuck :=
    str_overlap_rec_right_ne_stuck_of_ne_stuck recS recT hRecNe
  have hTailWordNe :
      concatCPropSHeadTailWord (Term.Boolean true) s ≠ Term.Stuck :=
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (concatCPropSHeadTailWord (Term.Boolean true) s)
      (by simpa [recS] using hRecSNe)
  rcases cprop_true_head_string_of_tailword_ne s sc T hScEq hscTy
      hTailWordNe with
    ⟨scWord, hScString⟩
  have hSsWord :
      native_unpack_seq ss = scWord.map SmtValue.Char := by
    exact string_eval_unpack_eq M scWord ss (by simpa [hScString] using hscEval)
  rcases cprop_flat_second_true_tail_head_of_rev_ne_stuck t tc tTail
      hRevIntroT hTTailList (by simpa [recT] using hRecTNe) with
    ⟨tSecond, tSecondTail, hTTailHead, hTSecondTailList, hFlatSecondEq⟩
  have htTailConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat tSecond tSecondTail)) =
        SmtType.Seq T := by
    simpa [hTTailHead] using htTailTy
  rcases str_concat_args_of_seq_type tSecond tSecondTail T htTailConsTy with
    ⟨htSecondTy, htSecondTailTy⟩
  have hTPrefixEq :
      tPrefix =
        __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat tSecond tSecondTail)) := by
    rw [hTPrefixConsEq tSecond tSecondTail hTTailHead, hTTailHead]
  have hTailConsList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (mkConcat tSecond tSecondTail) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.str_concat)
      tSecond tSecondTail (by decide) hTSecondTailList
  have hRevTailCons :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat tSecond tSecondTail) ≠ Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat)
      (mkConcat tSecond tSecondTail) hTailConsList
  have hElimTailCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat tSecond tSecondTail)) ≠ Term.Stuck :=
    str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq tSecond
      tSecondTail T htTailConsTy hRevTailCons
  rcases eo_interprets_rev_cons_snoc_prefix_of_seq M hM tSecond
      tSecondTail T htSecondTy hTSecondTailList htSecondTailTy
      hRevTailCons hElimTailCons with
    ⟨tSecondPrefix, htSecondPrefixTy, hSnocSecond⟩
  have hTPrefixSnoc :
      eo_interprets M (mkEq tPrefix (mkConcat tSecondPrefix tSecond)) true := by
    rw [hTPrefixEq]
    exact hSnocSecond
  have hTPrefixSplit :
      ∃ stSecondPrefix stSecond,
        __smtx_model_eval M (__eo_to_smt tSecond) = SmtValue.Seq stSecond ∧
        native_unpack_seq stp =
          native_unpack_seq stSecondPrefix ++ native_unpack_seq stSecond := by
    have hPrefixValTy := smt_model_eval_preserves_type M hM
      (__eo_to_smt tSecondPrefix) (SmtType.Seq T) htSecondPrefixTy
      (seq_ne_none T) (type_inhabited_seq T)
    have hSecondValTy := smt_model_eval_preserves_type M hM
      (__eo_to_smt tSecond) (SmtType.Seq T) htSecondTy
      (seq_ne_none T) (type_inhabited_seq T)
    rcases seq_value_canonical hPrefixValTy with
      ⟨stSecondPrefix, htSecondPrefixEval⟩
    rcases seq_value_canonical hSecondValTy with
      ⟨stSecond, htSecondEval⟩
    refine ⟨stSecondPrefix, stSecond, htSecondEval, ?_⟩
    have hRel := RuleProofs.eo_interprets_eq_rel M tPrefix
      (mkConcat tSecondPrefix tSecond) hTPrefixSnoc
    unfold RuleProofs.smt_value_rel at hRel
    rw [htPrefixEval, smtx_model_eval_str_concat_term_eq,
      htSecondPrefixEval, htSecondEval] at hRel
    simp [__smtx_model_eval_str_concat, native_seq_concat] at hRel
    have hSeqEq :=
      (RuleProofs.smt_seq_rel_iff_eq stp
        (native_pack_seq (__smtx_elem_typeof_seq_value stSecondPrefix)
          (native_unpack_seq stSecondPrefix ++
            native_unpack_seq stSecond))).mp hRel
    rw [hSeqEq]
    simp [_root_.native_unpack_pack_seq]
  rcases str_overlap_rec_numeral_of_ne_stuck recS recT hRecNe with
    ⟨m, hRec⟩
  have hOverlap :
      concatCPropOverlapLen (Term.Boolean true) t s =
        Term.Numeral (Int.ofNat (m + 1)) := by
    simp [concatCPropOverlapLen, eo_ite_true, recS, recT, hRec, __eo_add,
      native_zplus]
    rw [Int.add_comm]
  have hnEnd :
      (native_seq_extract (native_unpack_seq ss)
          (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
          (Int.ofNat (m + 1))).length <=
        (native_unpack_seq st).length := by
    by_cases hleSS :
        (native_unpack_seq ss).length <= (native_unpack_seq st).length
    · rcases native_seq_extract_suffix_nat_suffix (native_unpack_seq ss)
          (m + 1) with
        ⟨pre, hSuffix⟩
      have hEndLeSS :
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
            (native_unpack_seq ss).length := by
        calc
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
              (pre ++
                native_seq_extract (native_unpack_seq ss)
                  (Int.ofNat (native_unpack_seq ss).length +
                    -Int.ofNat (m + 1))
                  (Int.ofNat (m + 1))).length := by
            simp
          _ = (native_unpack_seq ss).length := by
            exact (congrArg List.length hSuffix).symm
      exact Nat.le_trans hEndLeSS hleSS
    · by_cases hGoal :
          (native_seq_extract (native_unpack_seq ss)
              (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
              (Int.ofNat (m + 1))).length <=
            (native_unpack_seq st).length
      · exact hGoal
      have hstPos : 0 < (native_unpack_seq st).length :=
        Nat.pos_of_ne_zero htcLenNe
      have hDropLt : (native_unpack_seq st).length - 1 < m := by
        have hEndLeN :
            (native_seq_extract (native_unpack_seq ss)
                (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
                (Int.ofNat (m + 1))).length <=
              m + 1 :=
          native_seq_extract_length_le_nat_arg (native_unpack_seq ss)
            (Int.ofNat (native_unpack_seq ss).length + -Int.ofNat (m + 1))
            (m + 1)
        omega
      rcases hTPrefixSplit with
        ⟨stSecondPrefix, stSecond, htSecondEval, hStpSplit⟩
      have hstLeSs :
          (native_unpack_seq st).length <= (native_unpack_seq ss).length :=
        Nat.le_of_lt (Nat.lt_of_not_ge hleSS)
      have hSsBoundary :
          native_unpack_seq ss =
            (native_unpack_seq ss).take
              ((native_unpack_seq ss).length - (native_unpack_seq st).length) ++
            native_unpack_seq st :=
        concat_split_suffix_eq_take_append_of_append_eq_of_le
          (native_unpack_seq ssp) (native_unpack_seq ss)
          (native_unpack_seq stp) (native_unpack_seq st)
          (by simpa using hAppend.symm) hstLeSs
      have hStpBoundary :
          native_unpack_seq stp =
            native_unpack_seq ssp ++
              (native_unpack_seq ss).take
                ((native_unpack_seq ss).length -
                  (native_unpack_seq st).length) := by
        have hAppend' := hAppend
        rw [hSsBoundary, ← List.append_assoc] at hAppend'
        exact List.append_cancel_right hAppend'
      have hSecondBoundary :
          native_unpack_seq stSecondPrefix ++ native_unpack_seq stSecond =
            native_unpack_seq ssp ++
              (native_unpack_seq ss).take
                ((native_unpack_seq ss).length -
                  (native_unpack_seq st).length) := by
        rw [← hStpSplit]
        exact hStpBoundary
      have hCompatFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT =
            Term.Boolean false :=
        str_overlap_rec_compatible_drop_false_of_lt recS recT m
          ((native_unpack_seq st).length - 1) hRec hDropLt
      have hCompatNotFalse :
          __str_is_compatible
              (strConcatDrop recS ((native_unpack_seq st).length - 1))
              recT ≠
            Term.Boolean false := by
        intro hBad
        dsimp [recS, recT] at hBad
        simp only [concatCPropSHeadTailWord, concatCPropFlatSecond] at hBad
        rw [show concatCPropHead (Term.Boolean true) s = Term.String scWord by
          rw [← hScEq, hScString]] at hBad
        simp [eo_ite_true, hFlatSecondEq] at hBad
        rw [eo_extract_prefix_dropLast scWord] at hBad
        cases scWord with
        | nil =>
            have hSsLen : (native_unpack_seq ss).length = 0 := by
              simp [hSsWord]
            omega
        | cons c cs =>
            cases cs with
            | nil =>
                have hSsLen : (native_unpack_seq ss).length = 1 := by
                  simp [hSsWord]
                omega
            | cons d ds =>
                rw [show (c :: d :: ds).dropLast =
                    c :: (d :: ds).dropLast by rfl] at hBad
                rw [RuleProofs.str_flatten_nary_intro_cons c
                  ((d :: ds).dropLast)] at hBad
                let pLen :=
                  (native_unpack_seq ss).length -
                    (native_unpack_seq st).length
                let pWord := (c :: d :: ds).take pLen
                have hpLenPos : 0 < pLen := by
                  dsimp [pLen]
                  have hSsLen :
                      (native_unpack_seq ss).length =
                        (c :: d :: ds).length := by
                    simp [hSsWord]
                  omega
                have hpLenLe : pLen <= (c :: d :: ds).length := by
                  dsimp [pLen]
                  exact Nat.le_trans (Nat.sub_le _ _)
                    (by simp [hSsWord])
                have hPrefixTakeMap :
                    (native_unpack_seq ss).take pLen =
                      pWord.map SmtValue.Char := by
                  dsimp [pWord, pLen]
                  rw [hSsWord]
                  simp
                have hSecondBoundaryWord :
                    native_unpack_seq stSecondPrefix ++
                        native_unpack_seq stSecond =
                      native_unpack_seq ssp ++
                        pWord.map SmtValue.Char := by
                  dsimp [pLen] at hPrefixTakeMap
                  simpa [pLen, hPrefixTakeMap] using hSecondBoundary
                cases hpWord : (c :: d :: ds).take pLen with
                | nil =>
                    have hLenP : pLen = 0 := by
                      have hLenTake :
                          ((c :: d :: ds).take pLen).length = pLen := by
                        rw [List.length_take]
                        exact Nat.min_eq_left hpLenLe
                      rw [hpWord] at hLenTake
                      simpa using hLenTake.symm
                    omega
                | cons pHead pTail =>
                  have hSecondBoundaryWordCons :
                    native_unpack_seq stSecondPrefix ++
                        native_unpack_seq stSecond =
                      native_unpack_seq ssp ++
                        (pHead :: pTail).map SmtValue.Char := by
                    simpa [pWord, hpWord] using hSecondBoundaryWord
                  have hSsLenWord :
                      (native_unpack_seq ss).length =
                        (c :: d :: ds).length := by
                    simp [hSsWord]
                  have hStLenLeWord :
                      (native_unpack_seq st).length <=
                        (c :: d :: ds).length := by
                    rw [← hSsLenWord]
                    exact hstLeSs
                  have hDropLenWord :
                      (c :: (d :: ds).dropLast).length =
                        (c :: d :: ds).length - 1 := by
                    simp
                  have hDropRevLe :
                      (native_unpack_seq st).length - 1 <=
                        (c :: (d :: ds).dropLast).length := by
                    omega
                  have hKeepLen :
                      (c :: (d :: ds).dropLast).length -
                          ((native_unpack_seq st).length - 1) =
                        pLen := by
                    cases hStLen :
                        (native_unpack_seq st).length with
                    | zero =>
                        omega
                    | succ stPred =>
                        rw [hDropLenWord]
                        dsimp [pLen]
                        rw [hSsLenWord, hStLen]
                        simp
                  have hpLenLeDrop :
                      pLen <= (c :: d :: ds).length - 1 := by
                    cases hStLen :
                        (native_unpack_seq st).length with
                    | zero =>
                        omega
                    | succ stPred =>
                        dsimp [pLen]
                        rw [hSsLenWord, hStLen]
                        simp
                  have hPWordLen :
                      (pHead :: pTail).length = pLen := by
                    have hLenTake :
                        ((c :: d :: ds).take pLen).length = pLen := by
                      rw [List.length_take]
                      exact Nat.min_eq_left hpLenLe
                    rw [hpWord] at hLenTake
                    simpa using hLenTake
                  have hTakePrefix :
                      (c :: (d :: ds).dropLast).take
                          ((c :: (d :: ds).dropLast).length -
                            ((native_unpack_seq st).length - 1)) =
                        pHead :: pTail := by
                    calc
                      (c :: (d :: ds).dropLast).take
                          ((c :: (d :: ds).dropLast).length -
                            ((native_unpack_seq st).length - 1)) =
                        (c :: (d :: ds).dropLast).take pLen := by
                          rw [hKeepLen]
                      _ = (c :: d :: ds).take pLen := by
                          simpa using
                            take_dropLast_eq_take_of_le
                              (c :: d :: ds) pLen hpLenLeDrop
                      _ = pHead :: pTail := hpWord
                  have hTakePrefixLen :
                      (c :: (d :: ds).dropLast).length -
                          ((native_unpack_seq st).length - 1) =
                        (pHead :: pTail).length := by
                    rw [hKeepLen, hPWordLen]
                  have hTakePrefix' :
                      List.take
                          ((d :: ds).dropLast.length + 1 -
                            ((native_unpack_seq st).length - 1))
                          (c :: (d :: ds).dropLast) =
                        pHead :: pTail := by
                    simpa using hTakePrefix
                  have hTakePrefixLen' :
                      (d :: ds).dropLast.length + 1 -
                          ((native_unpack_seq st).length - 1) =
                        (pHead :: pTail).length := by
                    simpa using hTakePrefixLen
                  have hTakePrefix'' :
                      List.take
                          (ds.length + 1 -
                            ((native_unpack_seq st).length - 1))
                          (c :: (d :: ds).dropLast) =
                        pHead :: pTail := by
                    simpa using hTakePrefix'
                  have hTakePrefixLen'' :
                      ds.length + 1 -
                          ((native_unpack_seq st).length - 1) =
                        (pHead :: pTail).length := by
                    simpa using hTakePrefixLen'
                  have hTakePrefixCore :
                      c :: List.take pTail.length (d :: ds).dropLast =
                        pHead :: pTail := by
                    have h := hTakePrefix''
                    rw [hTakePrefixLen''] at h
                    simpa using h
                  have hTailLenMin :
                      min pTail.length ds.length = pTail.length := by
                    have hLen := congrArg List.length hTakePrefixCore
                    simp [List.length_take] at hLen
                    omega
                  have hBadPrefix :
                      __str_is_compatible
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (RuleProofs.substrWord (pHead :: pTail) 0
                              (pHead :: pTail).length))
                          (__eo_list_rev (Term.UOp UserOp.str_concat)
                            (__str_flatten (__str_nary_intro tSecond))) =
                        Term.Boolean false := by
                    rw [strConcatDrop_rev_substrWord_eq_rev_take
                      (c :: (d :: ds).dropLast)
                      ((native_unpack_seq st).length - 1) hDropRevLe] at hBad
                    simpa [hTakePrefix, hTakePrefixLen, hTakePrefix',
                      hTakePrefixLen', hTakePrefix'', hTakePrefixLen'',
                      hTakePrefixCore, hTailLenMin] using hBad
                  exact
                    (str_is_compatible_rev_word_flatten_intro_ne_false_of_append_eval
                      M hM tSecond T stSecond (pHead :: pTail)
                      (native_unpack_seq stSecondPrefix)
                      (native_unpack_seq ssp) htSecondTy htSecondEval
                      hSecondBoundaryWordCons) hBadPrefix
      exact False.elim (hCompatNotFalse hCompatFalse)
  exact cprop_true_formula_of_overlap_bounds M hM t s tc sc tPrefix
    sPrefix T stp st ssp ss (m + 1) hScEq htcTy hscTy htPrefixTy
    hsPrefixTy hProg htPrefixEval htcEval hsPrefixEval hscEval hAppend
    hOverlap hnEnd

private theorem concatCPropFormula_has_smt_translation_false
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop (Term.Boolean false) (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (concatCPropFormula (Term.Boolean false) t s tc) := by
  rcases cprop_context_false_head_type t s tc hPremBool hNonzeroBool hProg with
    ⟨T, htcTy, hscTy⟩
  let pfx := concatCPropPrefix (Term.Boolean false) t s
  let sfx := concatCPropSuffix (Term.Boolean false) t s tc
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pfx)
  let tail := mkConcat sfx nil
  let rhs := mkConcat pfx tail
  have hPfxTy :
      __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T := by
    simpa [pfx] using cprop_prefix_false_seq_type t s tc T hscTy hProg
  have hSfxTy :
      __smtx_typeof (__eo_to_smt sfx) = SmtType.Seq T := by
    simpa [sfx] using cprop_suffix_false_seq_type t s tc T htcTy hPfxTy
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq pfx T hPfxTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq sfx nil T hSfxTy hNilTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq pfx tail T hPfxTy hTailTy
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hpfxNe : pfx ≠ Term.Stuck := cprop_seq_type_ne_stuck pfx T hPfxTy
  have hsfxNe : sfx ≠ Term.Stuck := cprop_seq_type_ne_stuck sfx T hSfxTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) sfx =
          Term.Apply (Term.UOp UserOp.str_concat) sfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) sfx (by simp) hsfxNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) sfx) nil
        (by simp) hnilNe
  have hTailGenNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil ≠
        Term.Stuck := by
    rw [hTailGenEq]
    simp [tail, mkConcat]
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) pfx =
          Term.Apply (Term.UOp UserOp.str_concat) pfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) pfx (by simp) hpfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) pfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) pfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) sfx) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean false) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_false, pfx, sfx, nil] using hEqGenEq
  rw [hFormulaEq]
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

private theorem concatCPropFormula_has_smt_translation_true
    (t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop (Term.Boolean true) (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (concatCPropFormula (Term.Boolean true) t s tc) := by
  rcases cprop_context_true_head_type t s tc hPremBool hNonzeroBool hProg with
    ⟨T, htcTy, hscTy⟩
  let rSfx := concatCPropReverseSuffix (Term.Boolean true) t s tc
  let rEnd := concatCPropReverseEnd (Term.Boolean true) t s
  let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof rSfx)
  let tail := mkConcat rEnd nil
  let rhs := mkConcat rSfx tail
  have hEndTy :
      __smtx_typeof (__eo_to_smt rEnd) = SmtType.Seq T := by
    simpa [rEnd] using cprop_reverse_end_true_seq_type t s tc T hscTy hProg
  have hSfxTy :
      __smtx_typeof (__eo_to_smt rSfx) = SmtType.Seq T := by
    simpa [rSfx] using cprop_reverse_suffix_true_seq_type t s tc T htcTy hEndTy
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq rSfx T hSfxTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
    simpa [tail] using smt_typeof_mkConcat_seq rEnd nil T hEndTy hNilTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.Seq T := by
    simpa [rhs] using smt_typeof_mkConcat_seq rSfx tail T hSfxTy hTailTy
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq tc rhs) :=
    eo_has_bool_type_eq_of_seq_type tc rhs T htcTy hRhsTy
  have hSfxNe : rSfx ≠ Term.Stuck := cprop_seq_type_ne_stuck rSfx T hSfxTy
  have hEndNe : rEnd ≠ Term.Stuck := cprop_seq_type_ne_stuck rEnd T hEndTy
  have hnilNe : nil ≠ Term.Stuck := cprop_seq_type_ne_stuck nil T hNilTy
  have hTailGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil =
        tail := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rEnd =
          Term.Apply (Term.UOp UserOp.str_concat) rEnd :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rEnd (by simp) hEndNe
    rw [hFun]
    simpa [tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rEnd) nil
        (by simp) hnilNe
  have hRhsGenEq :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil) =
        rhs := by
    have hFun :
        __eo_mk_apply (Term.UOp UserOp.str_concat) rSfx =
          Term.Apply (Term.UOp UserOp.str_concat) rSfx :=
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.UOp UserOp.str_concat) rSfx (by simp) hSfxNe
    rw [hFun, hTailGenEq]
    simpa [rhs, tail, mkConcat] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) rSfx) tail
        (by simp) (by simp [tail, mkConcat])
  have hEqGenEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_concat) rSfx)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat) rEnd) nil)) =
        mkEq tc rhs := by
    rw [hRhsGenEq]
    simpa [mkEq] using
      cprop_mk_apply_eq_apply_of_args_ne_stuck
        (Term.Apply (Term.UOp UserOp.eq) tc) rhs (by simp)
        (by simp [rhs, mkConcat])
  have hFormulaEq :
      concatCPropFormula (Term.Boolean true) t s tc = mkEq tc rhs := by
    simpa [concatCPropFormula, eo_ite_true, rSfx, rEnd, nil] using hEqGenEq
  rw [hFormulaEq]
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

private theorem step_concat_cprop_core
    (M : SmtModel) (hM : model_wf M)
    (rev t s tc : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))))) =
        Term.Bool) :
    StepRuleProperties M
      [mkEq t s, mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))]
      (__eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ) := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck rev t s tc hProg with
    ⟨hProgEq, _hHeadT⟩
  rcases len_nonzero_seq_type_of_bool tc hNonzeroBool with ⟨T, htcTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htcTy]
        exact seq_ne_none T)
  rcases concatCProp_rev_cases_of_prog_ne_stuck rev t s tc hProg htcNe with
    hRev | hRev
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M
            (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true :=
        hPremisesTrue
          (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) (by simp)
      rcases cprop_context_true M hM t s tc hPremBool hNonzeroBool
          hProg hST with
        ⟨U, sc, tPrefix, sPrefix, tTail, sTail, hScEq, hRevIntroT,
          hRevIntroS, hTTailList, hSTailList, htTailTy, _hsTailTy,
          htcTy', hscTy, htPrefixTy, hsPrefixTy, hConcatEq,
          hTPrefixConsEq, hSPrefixConsEq⟩
      rw [hProgEq]
      exact facts_concat_cprop_true_formula M hM t s tc sc tPrefix sPrefix
        tTail sTail U hScEq hRevIntroT hRevIntroS hTTailList hSTailList
        htcTy' hscTy htTailTy htPrefixTy hsPrefixTy hProg hNonzero hConcatEq
        hTPrefixConsEq hSPrefixConsEq
    · rw [hProgEq]
      exact concatCPropFormula_has_smt_translation_true t s tc hPremBool
        hNonzeroBool hProg hResultTy
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hNonzero :
          eo_interprets M
            (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) true :=
        hPremisesTrue
          (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0))) (by simp)
      rcases cprop_context_false M hM t s tc hPremBool hNonzeroBool
          hProg hST with
        ⟨U, sc, tTail, sTail, hScEq, hIntroT, hIntroS, hTTailList,
          hSTailList, htcTy', hscTy, htTailTy, hsTailTy, hConcatEq⟩
      rw [hProgEq]
      exact facts_concat_cprop_false_formula M hM t s tc sc tTail sTail
        U hScEq hIntroT hIntroS hTTailList hSTailList htcTy' hscTy
        htTailTy hsTailTy hProg hNonzero hConcatEq
    · rw [hProgEq]
      exact concatCPropFormula_has_smt_translation_false t s tc hPremBool
        hNonzeroBool hProg hResultTy

public theorem cmd_step_concat_cprop_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_cprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_cprop args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_cprop args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_cprop args premises ≠
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
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_cprop a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_cprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_cprop_premise_shapes_of_ne_stuck
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
                          __eo_prog_concat_cprop a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_cprop a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkNot
                                    (mkEq (mkStrLen u) (Term.Numeral 0))))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_cprop a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_cprop a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_cprop_core M hM a1 lhs rhs u
                        hPremEqBool hNonzeroBool hProgRule hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
