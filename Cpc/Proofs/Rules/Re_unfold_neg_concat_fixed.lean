module

public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
public import Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
import all Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
public import Cpc.Proofs.RuleSupport.StringEagerReductionSupport
import all Cpc.Proofs.RuleSupport.StringEagerReductionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

open ReUnfoldNegSupport

private abbrev mkNot := ReUnfoldNegSupport.mkNot
private abbrev mkAnd := ReUnfoldNegSupport.mkAnd
private abbrev mkOr := ReUnfoldNegSupport.mkOr
private abbrev mkEq := ReUnfoldNegSupport.mkEq
private abbrev mkLt := ReUnfoldNegSupport.mkLt
private abbrev mkLeq := ReUnfoldNegSupport.mkLeq
private abbrev mkNeg := ReUnfoldNegSupport.mkNeg
private abbrev mkStrLen := ReUnfoldNegSupport.mkStrLen
private abbrev mkSubstr := ReUnfoldNegSupport.mkSubstr
private abbrev mkStrInRe := ReUnfoldNegSupport.mkStrInRe
private abbrev mkReMult := ReUnfoldNegSupport.mkReMult
private abbrev mkReConcat := ReUnfoldNegSupport.mkReConcat

abbrev reConcatNil : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])

abbrev reUnfoldNegConcatFixedFalseFormula
    (t r1 r2 n : Term) : Term :=
  mkOr
    (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) n) r1))
    (mkOr
      (mkNot (mkStrInRe
        (mkSubstr t n (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))
      (Term.Boolean false))

abbrev reUnfoldNegConcatFixedTrueFormula
    (t r1 r2 n : Term) : Term :=
  mkOr
    (mkNot (mkStrInRe
      (mkSubstr t (mkNeg (mkStrLen t) n) n) r1))
    (mkOr
      (mkNot (mkStrInRe
        (mkSubstr t (Term.Numeral 0) (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2))))
      (Term.Boolean false))

theorem reConcat_nil_eq_empty_of_is_list_nil_true {nil : Term} :
    __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true ->
    nil = reConcatNil := by
  intro hNil
  cases nil <;> try cases hNil
  case Apply f x =>
    cases f <;> try cases hNil
    case UOp op =>
      cases op <;> try cases hNil
      case str_to_re =>
        cases x <;> try cases hNil
        case String s =>
          cases s with
          | nil => rfl
          | cons _ _ => cases hNil

theorem eo_get_nil_rec_re_concat_eq_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil = nil := by
  have hNilEq := reConcat_nil_eq_empty_of_is_list_nil_true hNil
  subst nil
  simp [reConcatNil, __eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not]

theorem eo_is_list_re_concat_nil_true_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.re_concat) nil = Term.Boolean true := by
  have hNilEq := reConcat_nil_eq_empty_of_is_list_nil_true hNil
  subst nil
  simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

theorem eo_list_rev_rec_re_concat_nil_eq_of_nil_true
    (nil acc : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __eo_list_rev_rec nil acc = acc := by
  have hNilEq := reConcat_nil_eq_empty_of_is_list_nil_true hNil
  subst nil
  cases acc <;> rfl

theorem eo_list_concat_rec_re_concat_nil_eq_of_nil_true
    (nil z : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil = Term.Boolean true) :
    __eo_list_concat_rec nil z = z := by
  have hNilEq := reConcat_nil_eq_empty_of_is_list_nil_true hNil
  subst nil
  cases z <;> rfl

theorem eo_list_concat_rec_re_concat_cons_eq_of_tail_ne_stuck
    (head tail z : Term)
    (hTail : __eo_list_concat_rec tail z ≠ Term.Stuck) :
    __eo_list_concat_rec (mkReConcat head tail) z =
      mkReConcat head (__eo_list_concat_rec tail z) := by
  exact eo_list_concat_rec_cons_eq_of_tail_ne_stuck
    (Term.UOp UserOp.re_concat) head tail z hTail

theorem eo_list_rev_re_concat_cons_eq_of_ne_stuck (x y : Term)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat x y) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat x y) =
      __eo_list_rev_rec y
        (mkReConcat x (__eo_get_nil_rec (Term.UOp UserOp.re_concat) y)) := by
  exact eo_list_rev_cons_eq_of_ne_stuck (Term.UOp UserOp.re_concat) x y hRev

theorem eo_list_rev_rec_re_concat_list_concat_rec_singleton_eq
    (tail acc head nil : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec tail
        (__eo_list_concat_rec acc (mkReConcat head nil)) =
      __eo_list_concat_rec (__eo_list_rev_rec tail acc)
        (mkReConcat head nil) := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hSingletonNonStuck : mkReConcat head nil ≠ Term.Stuck := by
        intro h
        cases h
      have hAccSnocNonStuck :
          __eo_list_concat_rec acc (mkReConcat head nil) ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.re_concat) acc (mkReConcat head nil)
          hAccList hSingletonNonStuck
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat) x acc (by decide) hAccList
      have hAccSnoc :
          mkReConcat x (__eo_list_concat_rec acc (mkReConcat head nil)) =
            __eo_list_concat_rec (mkReConcat x acc) (mkReConcat head nil) := by
        exact (eo_list_concat_rec_re_concat_cons_eq_of_tail_ne_stuck
          x acc (mkReConcat head nil) hAccSnocNonStuck).symm
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x y
        (__eo_list_concat_rec acc (mkReConcat head nil)) hAccSnocNonStuck]
      change __eo_list_rev_rec y
          (mkReConcat x (__eo_list_concat_rec acc (mkReConcat head nil))) =
        __eo_list_concat_rec
          (__eo_list_rev_rec (mkReConcat x y) acc) (mkReConcat head nil)
      rw [hAccSnoc]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x y acc
        hAccNonStuck]
      exact ih hTailTailList hConsAccList
  | case4 tail acc hTail hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.re_concat) tail ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.re_concat) tail hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.re_concat) tail)
              (Term.Boolean true) tail ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailNil :
          __eo_is_list_nil (Term.UOp UserOp.re_concat) tail =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.re_concat) tail)
          (Term.Boolean true) tail hReq
      rw [eo_list_rev_rec_re_concat_nil_eq_of_nil_true tail
        (__eo_list_concat_rec acc (mkReConcat head nil)) hTailNil]
      rw [eo_list_rev_rec_re_concat_nil_eq_of_nil_true tail acc hTailNil]

theorem eo_get_nil_rec_re_concat_list_rev_rec_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.re_concat)
        (__eo_list_rev_rec tail acc) =
      __eo_get_nil_rec (Term.UOp UserOp.re_concat) acc := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat) x acc (by decide) hAccList
      have hsimpa := ih hTailTailList hConsAccList
      try simp [__eo_list_rev_rec] at hsimpa ⊢
      exact hsimpa
  | case4 nil acc hNil hAcc hNot =>
      simp [__eo_list_rev_rec]

theorem eo_list_rev_rec_re_concat_rev_rec_get_nil_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.re_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec (__eo_list_rev_rec tail acc)
        (__eo_get_nil_rec (Term.UOp UserOp.re_concat) tail) =
      __eo_list_rev_rec acc tail := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hTailNonStuck : y ≠ Term.Stuck := by
        intro h
        subst y
        simp [__eo_is_list] at hTailTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.re_concat) (mkReConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.re_concat) x acc (by decide) hAccList
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat)
              (mkReConcat x y) =
            __eo_get_nil_rec (Term.UOp UserOp.re_concat) y :=
        eo_get_nil_rec_cons_self_eq_of_tail_list
          (Term.UOp UserOp.re_concat) x y (by decide) hTailTailList
      rw [hGetEq]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x y acc
        hAccNonStuck]
      rw [ih hTailTailList hConsAccList]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.re_concat) x acc y
        hTailNonStuck]
  | case4 nil acc hNil hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.re_concat) nil hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
              (Term.Boolean true) nil ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.re_concat) nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil = nil :=
        eo_get_nil_rec_re_concat_eq_of_nil_true nil hNilTrue
      rw [eo_list_rev_rec_re_concat_nil_eq_of_nil_true nil acc hNilTrue]
      rw [hGetEq]

theorem eo_list_rev_list_rev_re_concat_eq_of_list_true
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.re_concat)
        (__eo_list_rev (Term.UOp UserOp.re_concat) a) = a := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) a
  have hNilList :
      __eo_is_list (Term.UOp UserOp.re_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.re_concat) a hList
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.re_concat) a hList
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.re_concat) a =
        __eo_list_rev_rec a nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat) a hRev
  have hRevRecNonStuck :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [hRevEq] using hRev
  have hRevRecList :
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__eo_list_rev_rec a nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.re_concat)
      a nil hList hNilList hRevRecNonStuck
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) ≠ Term.Stuck := by
    rw [hRevEq]
    exact eo_list_rev_ne_stuck_of_is_list_true
      (Term.UOp UserOp.re_concat) (__eo_list_rev_rec a nil) hRevRecList
  have hGetRev :
      __eo_get_nil_rec (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) = nil := by
    rw [hRevEq]
    calc
      __eo_get_nil_rec (Term.UOp UserOp.re_concat)
          (__eo_list_rev_rec a nil) =
        __eo_get_nil_rec (Term.UOp UserOp.re_concat) nil := by
          exact eo_get_nil_rec_re_concat_list_rev_rec_eq a nil hList hNilList
      _ = nil :=
        eo_get_nil_rec_re_concat_eq_of_nil_true nil hNilNil
  have hRevRevEq :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a) =
        __eo_list_rev_rec (__eo_list_rev (Term.UOp UserOp.re_concat) a)
          (__eo_get_nil_rec (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) a)) :=
    eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__eo_list_rev (Term.UOp UserOp.re_concat) a) hRevRev
  rw [hRevRevEq, hGetRev, hRevEq]
  rw [eo_list_rev_rec_re_concat_rev_rec_get_nil_eq a nil hList hNilList]
  rw [eo_list_rev_rec_re_concat_nil_eq_of_nil_true nil a hNilNil]

theorem eo_list_rev_re_concat_cons_as_concat_rec
    (r1 r2 : Term)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat r1 r2) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat r1 r2) =
      __eo_list_concat_rec
        (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
        (mkReConcat r1 (__eo_get_nil_rec (Term.UOp UserOp.re_concat) r2)) := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) r2
  have hTailList :
      __eo_is_list (Term.UOp UserOp.re_concat) r2 = Term.Boolean true :=
    eo_list_rev_cons_tail_list_of_ne_stuck
      (Term.UOp UserOp.re_concat) r1 r2 hRev
  have hNilList :
      __eo_is_list (Term.UOp UserOp.re_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.re_concat) r2 hTailList
  have hRevTail :
      __eo_list_rev (Term.UOp UserOp.re_concat) r2 ≠ Term.Stuck :=
    eo_list_rev_ne_stuck_of_is_list_true
      (Term.UOp UserOp.re_concat) r2 hTailList
  have hRevTailEq :
      __eo_list_rev (Term.UOp UserOp.re_concat) r2 =
        __eo_list_rev_rec r2 nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck
        (Term.UOp UserOp.re_concat) r2 hRevTail
  have hConsEq :=
    eo_list_rev_re_concat_cons_eq_of_ne_stuck r1 r2 hRev
  rw [hConsEq]
  change __eo_list_rev_rec r2 (mkReConcat r1 nil) =
    __eo_list_concat_rec
      (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
      (mkReConcat r1 nil)
  rw [hRevTailEq]
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.re_concat) r2 hTailList
  have hConcatNil :
      __eo_list_concat_rec nil (mkReConcat r1 nil) =
        mkReConcat r1 nil :=
    eo_list_concat_rec_re_concat_nil_eq_of_nil_true nil
      (mkReConcat r1 nil) hNilNil
  simpa [hConcatNil] using
    eo_list_rev_rec_re_concat_list_concat_rec_singleton_eq
      r2 nil r1 nil hTailList hNilList

theorem eo_list_rev_eq_cons_original_eq_concat_rec_rev_tail_singleton
    (r r1 r2 : Term)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) r ≠ Term.Stuck)
    (hEq :
      __eo_list_rev (Term.UOp UserOp.re_concat) r =
        mkReConcat r1 r2) :
    r =
      __eo_list_concat_rec
        (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
        (mkReConcat r1 (__eo_get_nil_rec (Term.UOp UserOp.re_concat) r2)) := by
  have hList :
      __eo_is_list (Term.UOp UserOp.re_concat) r = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck
      (Term.UOp UserOp.re_concat) r hRev
  have hDouble :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r) = r :=
    eo_list_rev_list_rev_re_concat_eq_of_list_true r hList hRev
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r) ≠ Term.Stuck :=
    eo_list_rev_list_rev_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.re_concat) r hRev
  have hConsRev :
      __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat r1 r2) ≠
        Term.Stuck := by
    simpa [← hEq] using hRevRev
  calc
    r = __eo_list_rev (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r) := hDouble.symm
    _ = __eo_list_rev (Term.UOp UserOp.re_concat) (mkReConcat r1 r2) := by
          rw [hEq]
    _ = __eo_list_concat_rec
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
          (mkReConcat r1 (__eo_get_nil_rec (Term.UOp UserOp.re_concat) r2)) :=
          eo_list_rev_re_concat_cons_as_concat_rec r1 r2 hConsRev

theorem eo_get_nil_rec_re_concat_eq_empty_of_is_list_true (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.re_concat) a = reConcatNil := by
  have hNil :
      __eo_is_list_nil (Term.UOp UserOp.re_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.re_concat) a) =
        Term.Boolean true :=
    eo_is_list_nil_get_nil_rec_of_is_list_true
      (Term.UOp UserOp.re_concat) a hList
  exact reConcat_nil_eq_empty_of_is_list_nil_true hNil

theorem smtx_typeof_reConcatNil :
    __smtx_typeof (__eo_to_smt reConcatNil) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [__smtx_typeof, native_string_valid, native_ite, native_Teq]

theorem smt_typeof_list_rev_rec_re_concat_of_reglan
    (a acc : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.RegLan)
    (hRev : __eo_list_rev_rec a acc ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) =
      SmtType.RegLan := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hList
  | case2 a hA =>
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.re_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.re_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y
          hList
      have hArgs := smtx_typeof_re_concat_args_of_reglan x y haTy
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkReConcat x acc)) =
            SmtType.RegLan :=
        smtx_typeof_re_concat_of_reglan x acc hArgs.1 hAccTy
      have hTailRev :
          __eo_list_rev_rec y (mkReConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailList hArgs.2 hNewAccTy hTailRev
  | case4 nil acc hNil hAcc hNot =>
      simpa [__eo_list_rev_rec] using hAccTy

theorem smt_typeof_list_rev_re_concat_of_reglan
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.RegLan)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.re_concat) a)) =
      SmtType.RegLan := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) a
  have hNilTy :
      __smtx_typeof (__eo_to_smt nil) = SmtType.RegLan := by
    have hNilEq :=
      eo_get_nil_rec_re_concat_eq_empty_of_is_list_true a hList
    simpa [nil, hNilEq] using smtx_typeof_reConcatNil
  have hRecNe :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [nil] using
      eo_list_rev_rec_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.re_concat) a hRev
  rw [eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.re_concat) a hRev]
  exact smt_typeof_list_rev_rec_re_concat_of_reglan a nil hList haTy
    hNilTy hRecNe

theorem re_unfold_neg_concat_fixed_false_formula_has_bool_type
    (t r1 r2 n : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)) =
        SmtType.RegLan)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type
      (reUnfoldNegConcatFixedFalseFormula t r1 r2 n) := by
  have hLen := smtx_typeof_str_len_of_seq_char t ht
  have hNeg := smtx_typeof_neg_of_int (mkStrLen t) n hLen hn
  have hLeftSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) n)) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t (Term.Numeral 0) n
      ht smtx_typeof_zero hn
  have hRightSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t n (mkNeg (mkStrLen t) n))) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t n (mkNeg (mkStrLen t) n)
      ht hn hNeg
  have hLeftIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t (Term.Numeral 0) n) r1 hLeftSub hr1
  have hRightIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t n (mkNeg (mkStrLen t) n))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)
      hRightSub hTail
  exact RuleProofs.eo_has_bool_type_or_of_bool_args
    (mkNot (mkStrInRe (mkSubstr t (Term.Numeral 0) n) r1))
    (mkOr
      (mkNot (mkStrInRe
        (mkSubstr t n (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))
      (Term.Boolean false))
    (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hLeftIn)
    (RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkNot (mkStrInRe
        (mkSubstr t n (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))
      (Term.Boolean false)
      (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hRightIn)
      RuleProofs.eo_has_bool_type_false)

theorem re_unfold_neg_concat_fixed_true_formula_has_bool_type
    (t r1 r2 n : Term)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) r2))) =
        SmtType.RegLan)
    (hn : __smtx_typeof (__eo_to_smt n) = SmtType.Int) :
    RuleProofs.eo_has_bool_type
      (reUnfoldNegConcatFixedTrueFormula t r1 r2 n) := by
  have hLen := smtx_typeof_str_len_of_seq_char t ht
  have hNeg := smtx_typeof_neg_of_int (mkStrLen t) n hLen hn
  have hLeftSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t (mkNeg (mkStrLen t) n) n)) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t (mkNeg (mkStrLen t) n) n
      ht hNeg hn
  have hRightSub :
      __smtx_typeof
          (__eo_to_smt (mkSubstr t (Term.Numeral 0)
            (mkNeg (mkStrLen t) n))) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_substr_of_seq_char t (Term.Numeral 0)
      (mkNeg (mkStrLen t) n) ht smtx_typeof_zero hNeg
  have hLeftIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t (mkNeg (mkStrLen t) n) n) r1 hLeftSub hr1
  have hRightIn :=
    smtx_typeof_str_in_re_of_seq_reglan
      (mkSubstr t (Term.Numeral 0) (mkNeg (mkStrLen t) n))
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__eo_list_rev (Term.UOp UserOp.re_concat) r2))
      hRightSub hTail
  exact RuleProofs.eo_has_bool_type_or_of_bool_args
    (mkNot (mkStrInRe
      (mkSubstr t (mkNeg (mkStrLen t) n) n) r1))
    (mkOr
      (mkNot (mkStrInRe
        (mkSubstr t (Term.Numeral 0) (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2))))
      (Term.Boolean false))
    (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hLeftIn)
    (RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkNot (mkStrInRe
        (mkSubstr t (Term.Numeral 0) (mkNeg (mkStrLen t) n))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2))))
      (Term.Boolean false)
      (RuleProofs.eo_has_bool_type_not_of_bool_arg _ hRightIn)
      RuleProofs.eo_has_bool_type_false)

theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simp [native_unpack_string]

private theorem eval_str_in_re_of_typed_seq_reglan
    (M : SmtModel) (s r : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hs : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hr : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_model_eval M (__eo_to_smt (mkStrInRe s r)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
  rw [eval_str_in_re_of_seq_reglan M s r ss rv hs hr]
  rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTy]
  rw [← native_str_in_re_eq_model]

theorem native_seq_extract_len_le_len
    (xs : List SmtValue) (i n : native_Int) :
    Int.ofNat (native_seq_extract xs i n).length <= Int.ofNat xs.length := by
  simp only [native_seq_extract]
  split
  · simp
  · have hTake :
        ((xs.drop (Int.toNat i)).take
          (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          (xs.drop (Int.toNat i)).length := by
        rw [List.length_take]
        exact Nat.min_le_right _ _
    have hDrop : (xs.drop (Int.toNat i)).length <= xs.length := by
        rw [List.length_drop]
        exact Nat.sub_le _ _
    exact Int.ofNat_le.mpr (Nat.le_trans hTake hDrop)

theorem term_ne_stuck_of_smtx_typeof_eq
    (t : Term) {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = T)
    (hNonNone : T ≠ SmtType.None) :
    t ≠ Term.Stuck :=
  term_ne_stuck_of_has_smt_translation t (by
    unfold eo_has_smt_translation
    rw [hTy]
    exact hNonNone)

theorem re_unfold_neg_concat_fixed_false_eq_formula
    (t r1 r2 : Term) (n : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)) =
        SmtType.RegLan)
    (hFixed : __str_fixed_len_re r1 = Term.Numeral n) :
    __mk_re_unfold_neg_concat_fixed t (mkReConcat r1 r2)
        (Term.Boolean false) =
      reUnfoldNegConcatFixedFalseFormula t r1 r2 (Term.Numeral n) := by
  have htNe : t ≠ Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq t ht (by decide)
  have hr1Ne : r1 ≠ Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq r1 hr1 (by decide)
  have hTailNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2 ≠
        Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)
      hTail (by decide)
  simp [__mk_re_unfold_neg_concat_fixed,
    reUnfoldNegConcatFixedFalseFormula, mkOr, mkNot, mkStrInRe, mkSubstr,
    mkNeg, mkStrLen, mkReConcat, hFixed, __eo_mk_apply, __eo_ite, native_ite, native_teq]

theorem re_unfold_neg_concat_fixed_true_eq_formula
    (t r1 r2 : Term) (n : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) r2))) =
        SmtType.RegLan)
    (hFixed : __str_fixed_len_re r1 = Term.Numeral n) :
    __mk_re_unfold_neg_concat_fixed t (mkReConcat r1 r2)
        (Term.Boolean true) =
      reUnfoldNegConcatFixedTrueFormula t r1 r2 (Term.Numeral n) := by
  have htNe : t ≠ Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq t ht (by decide)
  have hr1Ne : r1 ≠ Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq r1 hr1 (by decide)
  have hTailNe :
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2) ≠
        Term.Stuck :=
    term_ne_stuck_of_smtx_typeof_eq
      (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__eo_list_rev (Term.UOp UserOp.re_concat) r2))
      hTail (by decide)
  simp [__mk_re_unfold_neg_concat_fixed,
    reUnfoldNegConcatFixedTrueFormula, mkOr, mkNot, mkStrInRe, mkSubstr,
    mkNeg, mkStrLen, mkReConcat, hFixed, __eo_mk_apply, __eo_ite, native_ite, native_teq]

theorem re_unfold_neg_concat_fixed_false_fixed_ne_of_ne_stuck
    (t r1 r2 : Term) :
    __mk_re_unfold_neg_concat_fixed t (mkReConcat r1 r2)
        (Term.Boolean false) ≠ Term.Stuck ->
    __str_fixed_len_re r1 ≠ Term.Stuck := by
  intro h hFixed
  cases t <;>
    simp [__mk_re_unfold_neg_concat_fixed, hFixed,
      __eo_mk_apply, __eo_ite, native_ite, native_teq] at h

theorem re_unfold_neg_concat_fixed_true_fixed_ne_of_ne_stuck
    (t r1 r2 : Term) :
    __mk_re_unfold_neg_concat_fixed t (mkReConcat r1 r2)
        (Term.Boolean true) ≠ Term.Stuck ->
    __str_fixed_len_re r1 ≠ Term.Stuck := by
  intro h hFixed
  cases t <;>
    simp [__mk_re_unfold_neg_concat_fixed, hFixed,
      __eo_mk_apply, __eo_ite, native_ite, native_teq] at h

theorem re_unfold_neg_concat_fixed_false_singleton_ne_of_ne_stuck
    (t r1 r2 : Term) (n : native_Int) :
    __mk_re_unfold_neg_concat_fixed t (mkReConcat r1 r2)
        (Term.Boolean false) ≠ Term.Stuck ->
    __str_fixed_len_re r1 = Term.Numeral n ->
    __eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2 ≠
      Term.Stuck := by
  intro h hFixed
  change __mk_re_unfold_neg_concat_fixed t
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
      (Term.Boolean false) ≠ Term.Stuck at h
  cases t
  case Stuck =>
    simp [__mk_re_unfold_neg_concat_fixed] at h
  all_goals
    simp [__mk_re_unfold_neg_concat_fixed, hFixed, __eo_ite, native_ite,
      native_teq] at h
    have hRightOr := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
    have hRightFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRightOr
    have hRightNot := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRightFun
    have hRightIn := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRightNot
    exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRightIn

theorem re_unfold_neg_concat_fixed_false_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r1 r2 : Term) (n : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hList : __eo_is_list (Term.UOp UserOp.re_concat) r2 =
      Term.Boolean true)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)) =
        SmtType.RegLan)
    (hFixed : __str_fixed_len_re r1 = Term.Numeral n) :
    eo_interprets M
      (mkNot (mkStrInRe t (mkReConcat r1 r2))) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (reUnfoldNegConcatFixedFalseFormula t r1 r2
            (Term.Numeral n))) =
      SmtValue.Boolean true := by
  intro hPrem
  rcases negated_str_in_re_re_concat_native_false M hM t r1 r2
      ht hr1 hr2 hPrem with
    ⟨ss, rv1, rv2, htEval, hr1Eval, hr2Eval, hNo⟩
  have htEvalTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
      unfold term_has_non_none_type
      rw [ht]
      simp)
  have hSsTy :
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [htEval, ht, __smtx_typeof_value] using htEvalTy
  have hSsElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hSsTy
  have hSsTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hSsTy
  rcases smt_eval_reglan_of_smt_type_reglan M hM
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))
      hTail with
    ⟨rvTail, hTailEval⟩
  have hTailRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)))
        (__smtx_model_eval M (__eo_to_smt r2)) :=
    reConcat_singleton_elim_rel_eval M r2 hList ⟨rv2, hr2Eval⟩
  have hTailRelReg :
      RuleProofs.smt_value_rel (SmtValue.RegLan rvTail)
        (SmtValue.RegLan rv2) := by
    simpa [hTailEval, hr2Eval] using hTailRel
  let len : native_Int := native_seq_len (native_unpack_seq ss)
  let leftSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) 0 n)
  let rightSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) n (len - n))
  let leftStr : native_String := native_unpack_string leftSeq
  let rightStr : native_String := native_unpack_string rightSeq
  have hLeftSeqTy :
      __smtx_typeof_seq_value leftSeq = SmtType.Seq SmtType.Char := by
    dsimp [leftSeq]
    rw [hSsElem]
    exact typeof_seq_value_pack_seq_of_typed
      (list_typed_extract hSsTyped 0 n)
  have hRightSeqTy :
      __smtx_typeof_seq_value rightSeq = SmtType.Seq SmtType.Char := by
    dsimp [rightSeq]
    rw [hSsElem]
    exact typeof_seq_value_pack_seq_of_typed
      (list_typed_extract hSsTyped n (len - n))
  have hLenEval :
      __smtx_model_eval M (__eo_to_smt (mkStrLen t)) =
        SmtValue.Numeral len := by
    simpa [len] using eval_strlen_of_seq M t ss htEval
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (mkNeg (mkStrLen t) (Term.Numeral n))) =
        SmtValue.Numeral (len - n) :=
    eval_neg_of_ints M (mkStrLen t) (Term.Numeral n) len n hLenEval (by
      change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
      simp [__smtx_model_eval])
  have hLeftSubEval :
      __smtx_model_eval M
          (__eo_to_smt (mkSubstr t (Term.Numeral 0) (Term.Numeral n))) =
        SmtValue.Seq leftSeq := by
    simpa [leftSeq] using
      eval_substr_of_seq_ints M t (Term.Numeral 0) (Term.Numeral n) ss 0 n
        htEval (by
          change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
          simp [__smtx_model_eval]) (by
          change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
          simp [__smtx_model_eval])
  have hRightSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkSubstr t (Term.Numeral n)
              (mkNeg (mkStrLen t) (Term.Numeral n)))) =
        SmtValue.Seq rightSeq := by
    simpa [rightSeq] using
      eval_substr_of_seq_ints M t (Term.Numeral n)
        (mkNeg (mkStrLen t) (Term.Numeral n)) ss n (len - n)
        htEval (by
          change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
          simp [__smtx_model_eval]) hNegEval
  have hLeftInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t (Term.Numeral 0) (Term.Numeral n)) r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    simpa [leftStr] using
      eval_str_in_re_of_typed_seq_reglan M
        (mkSubstr t (Term.Numeral 0) (Term.Numeral n)) r1 leftSeq rv1
        hLeftSeqTy hLeftSubEval hr1Eval
  have hRightInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t (Term.Numeral n)
                (mkNeg (mkStrLen t) (Term.Numeral n)))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    simpa [rightStr] using
      eval_str_in_re_of_typed_seq_reglan M
        (mkSubstr t (Term.Numeral n)
          (mkNeg (mkStrLen t) (Term.Numeral n)))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2)
        rightSeq rvTail hRightSeqTy hRightSubEval hTailEval
  have hLenEval' :
      __smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.Numeral len := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)) =
      SmtValue.Numeral len at hLenEval
    simpa [__smtx_model_eval] using hLenEval
  have hNegEval' :
      __smtx_model_eval__
          (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
          (SmtValue.Numeral n) =
        SmtValue.Numeral (len - n) := by
    change __smtx_model_eval M
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.Numeral n)) =
      SmtValue.Numeral (len - n) at hNegEval
    simpa [__smtx_model_eval] using hNegEval
  have hNegEval'' :
      __smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n) =
        SmtValue.Numeral (len - n) := by
    simpa [hLenEval'] using hNegEval'
  have hLeftSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (SmtValue.Numeral n) =
        SmtValue.Seq leftSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
          (SmtTerm.Numeral n)) =
      SmtValue.Seq leftSeq at hLeftSubEval
    simpa [__smtx_model_eval] using hLeftSubEval
  have hRightSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral n) (SmtValue.Numeral (len - n)) =
        SmtValue.Seq rightSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral n)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
            (SmtTerm.Numeral n))) =
      SmtValue.Seq rightSeq at hRightSubEval
    have hsimpa := hRightSubEval
    try simp [__smtx_model_eval, hLenEval'] at hsimpa ⊢
    exact hsimpa
  have hRightSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral n)
          (__smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n)) =
        SmtValue.Seq rightSeq := by
    simpa [hNegEval''] using hRightSubEval'
  have hLeftInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0) (SmtValue.Numeral n))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
            (SmtTerm.Numeral n))
          (__eo_to_smt r1)) =
      SmtValue.Boolean (native_str_in_re leftStr rv1) at hLeftInEval
    simpa [__smtx_model_eval] using hLeftInEval
  have hRightInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral n) (SmtValue.Numeral (len - n)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral n)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Numeral n)))
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))) =
      SmtValue.Boolean (native_str_in_re rightStr rvTail) at hRightInEval
    have hsimpa := hRightInEval
    try simp [__smtx_model_eval, hLenEval'] at hsimpa ⊢
    exact hsimpa
  have hLeftInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq leftSeq)
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re leftStr rv1) := by
    simpa [hLeftSubEval'] using hLeftInEval'
  have hRightInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq rightSeq)
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))) =
        SmtValue.Boolean (native_str_in_re rightStr rvTail) := by
    simpa [hRightSubEval'] using hRightInEval'
  change __smtx_model_eval M
      (SmtTerm.or
        (SmtTerm.not
          (SmtTerm.str_in_re
            (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
              (SmtTerm.Numeral n))
            (__eo_to_smt r1)))
        (SmtTerm.or
          (SmtTerm.not
            (SmtTerm.str_in_re
              (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral n)
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
                  (SmtTerm.Numeral n)))
              (__eo_to_smt
                (__eo_list_singleton_elim (Term.UOp UserOp.re_concat) r2))))
          (SmtTerm.Boolean false))) = SmtValue.Boolean true
  by_cases hLeft : native_str_in_re leftStr rv1 = true
  · by_cases hRight : native_str_in_re rightStr rvTail = true
    · have hRightR2 :
          native_str_in_re rightStr rv2 = true :=
        native_str_in_re_of_reglan_rel rightStr rvTail rv2 hTailRelReg hRight
      have hFixedLen :
          Int.ofNat leftStr.length = n :=
        str_fixed_len_re_sound M r1 leftStr rv1 n hFixed hr1Eval hLeft
      have hn0 : 0 <= n := by
        rw [← hFixedLen]
        exact Int.natCast_nonneg _
      have hLeftLenLe : Int.ofNat leftStr.length <= len := by
        have hExtractLe :=
          native_seq_extract_len_le_len (native_unpack_seq ss) 0 n
        have hLeftLen :
            Int.ofNat leftStr.length =
              Int.ofNat
                (native_seq_extract (native_unpack_seq ss) 0 n).length := by
          simp [leftStr, leftSeq, native_unpack_string_length_eq,
            native_unpack_seq_pack_seq]
        calc
          Int.ofNat leftStr.length =
              Int.ofNat
                (native_seq_extract (native_unpack_seq ss) 0 n).length := hLeftLen
          _ <= Int.ofNat (native_unpack_seq ss).length := hExtractLe
          _ = len := by simp [len, native_seq_len]
      have hnle : n <= len := by
        rw [← hFixedLen]
        exact hLeftLenLe
      have hSplit :
          leftStr ++ rightStr = native_unpack_string ss := by
        simpa [leftStr, rightStr, leftSeq, rightSeq, len] using
          native_unpack_string_substr_split ss n hn0 hnle
      have hWhole :
          native_str_in_re (native_unpack_string ss)
            (native_re_concat rv1 rv2) = true := by
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro leftStr rightStr rv1 rv2
          hLeft hRightR2
      rw [hNo] at hWhole
      cases hWhole
    · simp [__smtx_model_eval, __smtx_model_eval_or,
        __smtx_model_eval_not, hLenEval', hLeftSubEval',
        hNegEval'', hRightSubEval', hLeftInEvalSeq, hRightInEvalSeq,
        hLeft, bool_eq_false_of_not_true hRight, SmtEval.native_or,
        SmtEval.native_not]
  · simp [__smtx_model_eval, __smtx_model_eval_or,
      __smtx_model_eval_not, hLenEval', hLeftSubEval',
      hNegEval'', hRightSubEval', hLeftInEvalSeq, hRightInEvalSeq,
      bool_eq_false_of_not_true hLeft, SmtEval.native_or,
      SmtEval.native_not]

theorem re_unfold_neg_concat_fixed_true_eval_true
    (M : SmtModel) (hM : model_wf M)
    (t r r1 r2 : Term) (n : native_Int)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hR2List :
      __eo_is_list (Term.UOp UserOp.re_concat) r2 = Term.Boolean true)
    (hRevR2List :
      __eo_is_list (Term.UOp UserOp.re_concat)
        (__eo_list_rev (Term.UOp UserOp.re_concat) r2) =
          Term.Boolean true)
    (hRevR2Ty :
      __smtx_typeof
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.re_concat) r2)) =
        SmtType.RegLan)
    (hTail :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) r2))) =
        SmtType.RegLan)
    (hRev : __eo_list_rev (Term.UOp UserOp.re_concat) r ≠ Term.Stuck)
    (hNorm :
      __eo_list_rev (Term.UOp UserOp.re_concat) r =
        mkReConcat r1 r2)
    (hFixed : __str_fixed_len_re r1 = Term.Numeral n) :
    eo_interprets M (mkNot (mkStrInRe t r)) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (reUnfoldNegConcatFixedTrueFormula t r1 r2
            (Term.Numeral n))) =
      SmtValue.Boolean true := by
  intro hPrem
  rcases negated_str_in_re_native_false M hM t r ht hr hPrem with
    ⟨ss, rvOrig, htEval, hrEval, hNo⟩
  have htEvalTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
      unfold term_has_non_none_type
      rw [ht]
      simp)
  have hSsTy :
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [htEval, ht, __smtx_typeof_value] using htEvalTy
  have hSsElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hSsTy
  have hSsTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hSsTy
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r1) hr1 with
    ⟨rv1, hr1Eval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM
      (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.re_concat) r2))
      hRevR2Ty with
    ⟨rvRevR2, hRevR2Eval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))
      hTail with
    ⟨rvTail, hTailEval⟩
  have hTailRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) r2))))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.re_concat) r2))) :=
    reConcat_singleton_elim_rel_eval M
      (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
      hRevR2List ⟨rvRevR2, hRevR2Eval⟩
  have hTailRelReg :
      RuleProofs.smt_value_rel (SmtValue.RegLan rvTail)
        (SmtValue.RegLan rvRevR2) := by
    simpa [hTailEval, hRevR2Eval] using hTailRel
  let len : native_Int := native_seq_len (native_unpack_seq ss)
  let cut : native_Int := len - n
  let suffixSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) cut n)
  let prefixSeq : SmtSeq :=
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
      (native_seq_extract (native_unpack_seq ss) 0 cut)
  let suffixStr : native_String := native_unpack_string suffixSeq
  let prefixStr : native_String := native_unpack_string prefixSeq
  have hSuffixSeqTy :
      __smtx_typeof_seq_value suffixSeq = SmtType.Seq SmtType.Char := by
    dsimp [suffixSeq]
    rw [hSsElem]
    exact typeof_seq_value_pack_seq_of_typed
      (list_typed_extract hSsTyped cut n)
  have hPrefixSeqTy :
      __smtx_typeof_seq_value prefixSeq = SmtType.Seq SmtType.Char := by
    dsimp [prefixSeq]
    rw [hSsElem]
    exact typeof_seq_value_pack_seq_of_typed
      (list_typed_extract hSsTyped 0 cut)
  have hLenEval :
      __smtx_model_eval M (__eo_to_smt (mkStrLen t)) =
        SmtValue.Numeral len := by
    simpa [len] using eval_strlen_of_seq M t ss htEval
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (mkNeg (mkStrLen t) (Term.Numeral n))) =
        SmtValue.Numeral cut := by
    simpa [cut] using
      eval_neg_of_ints M (mkStrLen t) (Term.Numeral n) len n
        hLenEval (by
          change __smtx_model_eval M (SmtTerm.Numeral n) =
            SmtValue.Numeral n
          simp [__smtx_model_eval])
  have hSuffixSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkSubstr t (mkNeg (mkStrLen t) (Term.Numeral n))
              (Term.Numeral n))) =
        SmtValue.Seq suffixSeq := by
    simpa [suffixSeq, cut] using
      eval_substr_of_seq_ints M t
        (mkNeg (mkStrLen t) (Term.Numeral n)) (Term.Numeral n)
        ss cut n htEval hNegEval (by
          change __smtx_model_eval M (SmtTerm.Numeral n) =
            SmtValue.Numeral n
          simp [__smtx_model_eval])
  have hPrefixSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkSubstr t (Term.Numeral 0)
              (mkNeg (mkStrLen t) (Term.Numeral n)))) =
        SmtValue.Seq prefixSeq := by
    simpa [prefixSeq, cut] using
      eval_substr_of_seq_ints M t (Term.Numeral 0)
        (mkNeg (mkStrLen t) (Term.Numeral n)) ss 0 cut
        htEval (by
          change __smtx_model_eval M (SmtTerm.Numeral 0) =
            SmtValue.Numeral 0
          simp [__smtx_model_eval]) hNegEval
  have hSuffixInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t (mkNeg (mkStrLen t) (Term.Numeral n))
                (Term.Numeral n)) r1)) =
        SmtValue.Boolean (native_str_in_re suffixStr rv1) := by
    simpa [suffixStr] using
      eval_str_in_re_of_typed_seq_reglan M
        (mkSubstr t (mkNeg (mkStrLen t) (Term.Numeral n))
          (Term.Numeral n)) r1 suffixSeq rv1
        hSuffixSeqTy hSuffixSubEval hr1Eval
  have hPrefixInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrInRe
              (mkSubstr t (Term.Numeral 0)
                (mkNeg (mkStrLen t) (Term.Numeral n)))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))) =
        SmtValue.Boolean (native_str_in_re prefixStr rvTail) := by
    simpa [prefixStr] using
      eval_str_in_re_of_typed_seq_reglan M
        (mkSubstr t (Term.Numeral 0)
          (mkNeg (mkStrLen t) (Term.Numeral n)))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2))
        prefixSeq rvTail hPrefixSeqTy hPrefixSubEval hTailEval
  have hLenEval' :
      __smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.Numeral len := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt t)) =
      SmtValue.Numeral len at hLenEval
    simpa [__smtx_model_eval] using hLenEval
  have hNegEval' :
      __smtx_model_eval__
          (__smtx_model_eval_str_len (__smtx_model_eval M (__eo_to_smt t)))
          (SmtValue.Numeral n) =
        SmtValue.Numeral cut := by
    change __smtx_model_eval M
        (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
          (SmtTerm.Numeral n)) =
      SmtValue.Numeral cut at hNegEval
    simpa [__smtx_model_eval] using hNegEval
  have hNegEval'' :
      __smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n) =
        SmtValue.Numeral cut := by
    simpa [hLenEval'] using hNegEval'
  have hSuffixSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral cut) (SmtValue.Numeral n) =
        SmtValue.Seq suffixSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
            (SmtTerm.Numeral n))
          (SmtTerm.Numeral n)) =
      SmtValue.Seq suffixSeq at hSuffixSubEval
    have hsimpa := hSuffixSubEval
    try simp [__smtx_model_eval, hLenEval'] at hsimpa ⊢
    exact hsimpa
  have hSuffixSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (__smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n))
          (SmtValue.Numeral n) =
        SmtValue.Seq suffixSeq := by
    simpa [hNegEval''] using hSuffixSubEval'
  have hPrefixSubEval' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0) (SmtValue.Numeral cut) =
        SmtValue.Seq prefixSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
          (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
            (SmtTerm.Numeral n))) =
      SmtValue.Seq prefixSeq at hPrefixSubEval
    have hsimpa := hPrefixSubEval
    try simp [__smtx_model_eval, hLenEval'] at hsimpa ⊢
    exact hsimpa
  have hPrefixSubEval'' :
      __smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
          (SmtValue.Numeral 0)
          (__smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n)) =
        SmtValue.Seq prefixSeq := by
    simpa [hNegEval''] using hPrefixSubEval'
  have hSuffixInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n))
            (SmtValue.Numeral n))
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re suffixStr rv1) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Numeral n))
            (SmtTerm.Numeral n))
          (__eo_to_smt r1)) =
      SmtValue.Boolean (native_str_in_re suffixStr rv1) at hSuffixInEval
    simpa [__smtx_model_eval, hLenEval', hNegEval', hNegEval''] using
      hSuffixInEval
  have hPrefixInEval' :
      __smtx_model_eval_str_in_re
          (__smtx_model_eval_str_substr (__smtx_model_eval M (__eo_to_smt t))
            (SmtValue.Numeral 0)
            (__smtx_model_eval__ (SmtValue.Numeral len) (SmtValue.Numeral n)))
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))) =
        SmtValue.Boolean (native_str_in_re prefixStr rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
            (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Numeral n)))
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))) =
      SmtValue.Boolean (native_str_in_re prefixStr rvTail) at hPrefixInEval
    simpa [__smtx_model_eval, hLenEval', hNegEval', hNegEval''] using
      hPrefixInEval
  have hSuffixInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq suffixSeq)
          (__smtx_model_eval M (__eo_to_smt r1)) =
        SmtValue.Boolean (native_str_in_re suffixStr rv1) := by
    simpa [hSuffixSubEval''] using hSuffixInEval'
  have hPrefixInEvalSeq :
      __smtx_model_eval_str_in_re (SmtValue.Seq prefixSeq)
          (__smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))) =
        SmtValue.Boolean (native_str_in_re prefixStr rvTail) := by
    simpa [hPrefixSubEval''] using hPrefixInEval'
  change __smtx_model_eval M
      (SmtTerm.or
        (SmtTerm.not
          (SmtTerm.str_in_re
            (SmtTerm.str_substr (__eo_to_smt t)
              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
                (SmtTerm.Numeral n))
              (SmtTerm.Numeral n))
            (__eo_to_smt r1)))
        (SmtTerm.or
          (SmtTerm.not
            (SmtTerm.str_in_re
              (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt t))
                  (SmtTerm.Numeral n)))
              (__eo_to_smt
                (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                  (__eo_list_rev (Term.UOp UserOp.re_concat) r2)))))
          (SmtTerm.Boolean false))) = SmtValue.Boolean true
  by_cases hSuffix : native_str_in_re suffixStr rv1 = true
  · by_cases hPrefix : native_str_in_re prefixStr rvTail = true
    · have hPrefixRev :
          native_str_in_re prefixStr rvRevR2 = true :=
        native_str_in_re_of_reglan_rel prefixStr rvTail rvRevR2
          hTailRelReg hPrefix
      have hFixedLen :
          Int.ofNat suffixStr.length = n :=
        str_fixed_len_re_sound M r1 suffixStr rv1 n hFixed hr1Eval hSuffix
      have hn0 : 0 <= n := by
        rw [← hFixedLen]
        exact Int.natCast_nonneg _
      have hSuffixLenLe : Int.ofNat suffixStr.length <= len := by
        have hExtractLe :=
          native_seq_extract_len_le_len (native_unpack_seq ss) cut n
        have hSuffixLen :
            Int.ofNat suffixStr.length =
              Int.ofNat
                (native_seq_extract (native_unpack_seq ss) cut n).length := by
          simp [suffixStr, suffixSeq, native_unpack_string_length_eq,
            native_unpack_seq_pack_seq]
        calc
          Int.ofNat suffixStr.length =
              Int.ofNat
                (native_seq_extract (native_unpack_seq ss) cut n).length :=
                hSuffixLen
          _ <= Int.ofNat (native_unpack_seq ss).length := hExtractLe
          _ = len := by simp [len, native_seq_len]
      have hnle : n <= len := by
        rw [← hFixedLen]
        exact hSuffixLenLe
      have hcut0 : 0 <= cut := by
        dsimp [cut]
        exact Int.sub_nonneg.mpr hnle
      have hcutle : cut <= len := by
        have h : len - n <= len := Int.sub_le_self len hn0
        simpa [cut] using h
      have hLenCut : len - cut = n := by
        have h : len - (len - n) = n := by
          apply (Int.sub_eq_iff_eq_add).2
          omega
        simpa [cut] using h
      have hSplit :
          prefixStr ++ suffixStr = native_unpack_string ss := by
        simpa [prefixStr, suffixStr, prefixSeq, suffixSeq, cut, len,
          hLenCut] using
          native_unpack_string_substr_split ss cut hcut0 hcutle
      let nil := __eo_get_nil_rec (Term.UOp UserOp.re_concat) r2
      let singleton := mkReConcat r1 nil
      have hNilNil :
          __eo_is_list_nil (Term.UOp UserOp.re_concat) nil =
            Term.Boolean true := by
        simpa [nil] using
          eo_is_list_nil_get_nil_rec_of_is_list_true
            (Term.UOp UserOp.re_concat) r2 hR2List
      have hNilList :
          __eo_is_list (Term.UOp UserOp.re_concat) nil =
            Term.Boolean true := by
        simpa [nil] using
          eo_get_nil_rec_is_list_true_of_is_list_true
            (Term.UOp UserOp.re_concat) r2 hR2List
      have hNilEval :
          __smtx_model_eval M (__eo_to_smt nil) =
            SmtValue.RegLan (native_str_to_re ([] : native_String)) :=
        reConcat_nil_eval_empty_of_is_list_nil_true M nil hNilNil
      have hNilTy :
          __smtx_typeof (__eo_to_smt nil) = SmtType.RegLan := by
        have hNilEq :=
          eo_get_nil_rec_re_concat_eq_empty_of_is_list_true r2 hR2List
        simpa [nil, hNilEq] using smtx_typeof_reConcatNil
      have hSingletonList :
          __eo_is_list (Term.UOp UserOp.re_concat) singleton =
            Term.Boolean true := by
        simpa [singleton] using
          eo_is_list_cons_self_true_of_tail_list
            (Term.UOp UserOp.re_concat) r1 nil (by decide) hNilList
      have hSingletonTy :
          __smtx_typeof (__eo_to_smt singleton) = SmtType.RegLan := by
        simpa [singleton] using
          smtx_typeof_re_concat_of_reglan r1 nil hr1 hNilTy
      have hSingletonEval :
          __smtx_model_eval M (__eo_to_smt singleton) =
            SmtValue.RegLan
              (native_re_concat rv1 (native_str_to_re ([] : native_String))) := by
        simpa [singleton] using
          eval_re_concat_of_reglan M r1 nil rv1
            (native_str_to_re ([] : native_String)) hr1Eval hNilEval
      rcases reConcat_list_concat_rec_eval_rel M
          (__eo_list_rev (Term.UOp UserOp.re_concat) r2) singleton
          rvRevR2
          (native_re_concat rv1 (native_str_to_re ([] : native_String)))
          hRevR2List hSingletonList hRevR2Ty hSingletonTy hRevR2Eval
          hSingletonEval with
        ⟨rvConcat, hConcatEval, _hConcatTy, hConcatRel⟩
      have hEmptyMem :
          native_str_in_re ([] : native_String)
            (native_str_to_re ([] : native_String)) = true := by
        simp [RuleProofs.native_str_in_re, RuleProofs.nativeListInRe,
          native_str_to_re, impl_native_re_of_list, native_re_nullable,
          native_string_valid]
      have hSuffixSingleton :
          native_str_in_re suffixStr
            (native_re_concat rv1 (native_str_to_re ([] : native_String))) =
            true := by
        simpa using
          native_str_in_re_re_concat_intro suffixStr ([] : native_String)
            rv1 (native_str_to_re ([] : native_String)) hSuffix hEmptyMem
      have hWholeNative :
          native_str_in_re (native_unpack_string ss)
            (native_re_concat rvRevR2
              (native_re_concat rv1
                (native_str_to_re ([] : native_String)))) = true := by
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro prefixStr suffixStr rvRevR2
          (native_re_concat rv1 (native_str_to_re ([] : native_String)))
          hPrefixRev hSuffixSingleton
      have hWholeConcat :
          native_str_in_re (native_unpack_string ss) rvConcat = true :=
        native_str_in_re_of_reglan_rel (native_unpack_string ss)
          (native_re_concat rvRevR2
            (native_re_concat rv1 (native_str_to_re ([] : native_String))))
          rvConcat
          (RuleProofs.smt_value_rel_symm _ _ hConcatRel)
          hWholeNative
      have hOrigEq :=
        eo_list_rev_eq_cons_original_eq_concat_rec_rev_tail_singleton
          r r1 r2 hRev hNorm
      have hConcatEvalOrig :
          __smtx_model_eval M
              (__eo_to_smt
                (__eo_list_concat_rec
                  (__eo_list_rev (Term.UOp UserOp.re_concat) r2)
                  singleton)) =
            SmtValue.RegLan rvOrig := by
        rw [← hOrigEq]
        exact hrEval
      rw [hConcatEvalOrig] at hConcatEval
      cases hConcatEval
      rw [hNo] at hWholeConcat
      cases hWholeConcat
    · simp [__smtx_model_eval, __smtx_model_eval_or,
        __smtx_model_eval_not, hLenEval', hNegEval'',
        hSuffixSubEval', hPrefixSubEval',
        hSuffixInEvalSeq, hPrefixInEvalSeq, hSuffix,
        bool_eq_false_of_not_true hPrefix, SmtEval.native_or,
        SmtEval.native_not]
  · simp [__smtx_model_eval, __smtx_model_eval_or,
      __smtx_model_eval_not, hLenEval', hNegEval'',
      hSuffixSubEval', hPrefixSubEval',
      hSuffixInEvalSeq, hPrefixInEvalSeq,
      bool_eq_false_of_not_true hSuffix, SmtEval.native_or,
      SmtEval.native_not]

private theorem re_unfold_neg_concat_fixed_nonstuck_shape
    (rev p : Term) :
    __eo_prog_re_unfold_neg_concat_fixed rev (Proof.pf p) ≠ Term.Stuck ->
    ∃ t r,
      p = mkNot (mkStrInRe t r) ∧
      __eo_prog_re_unfold_neg_concat_fixed rev (Proof.pf p) =
        __mk_re_unfold_neg_concat_fixed t
          (__eo_ite rev (__eo_list_rev (Term.UOp UserOp.re_concat) r) r)
          rev := by
  intro h
  cases rev <;> try (simp [__eo_prog_re_unfold_neg_concat_fixed] at h)
  all_goals
    cases p with
    | Apply f inner =>
        cases f with
        | UOp op =>
            cases op <;>
              try (simp at h)
            case not =>
              cases inner with
              | Apply f2 r =>
                  cases f2 with
                  | Apply op2 t =>
                      cases op2 with
                      | UOp op3 =>
                          cases op3 <;>
                            try (simp at h)
                          case str_in_re =>
                            exact ⟨t, r, rfl, rfl⟩
                      | _ =>
                          simp at h
                  | _ =>
                      simp at h
              | _ =>
                  simp at h
        | _ =>
            simp at h
    | _ =>
        simp at h

end RuleProofs

public theorem cmd_step_re_unfold_neg_concat_fixed_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_neg_concat_fixed args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_unfold_neg_concat_fixed args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_neg_concat_fixed args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_unfold_neg_concat_fixed args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons rev argsTail =>
      cases argsTail with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n premisesTail =>
              cases premisesTail with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  let p := __eo_state_proven_nth s n
                  change StepRuleProperties M [p]
                    (__eo_prog_re_unfold_neg_concat_fixed rev
                      (Proof.pf p))
                  have hProgLocal :
                      __eo_prog_re_unfold_neg_concat_fixed rev
                          (Proof.pf p) ≠ Term.Stuck := by
                    change __eo_prog_re_unfold_neg_concat_fixed rev
                        (Proof.pf (__eo_state_proven_nth s n)) ≠
                      Term.Stuck at hProg
                    simpa [p] using hProg
                  rcases
                    RuleProofs.re_unfold_neg_concat_fixed_nonstuck_shape
                      rev p hProgLocal with
                    ⟨t, r, hp, hProgEq⟩
                  have hpBool :
                      RuleProofs.eo_has_bool_type
                        (RuleProofs.ReUnfoldNegSupport.mkNot
                          (RuleProofs.ReUnfoldNegSupport.mkStrInRe t r)) := by
                    have h := hPremisesBool p (by simp [p, premiseTermList])
                    simpa [hp] using h
                  have hInnerBool :
                      RuleProofs.eo_has_bool_type
                        (RuleProofs.ReUnfoldNegSupport.mkStrInRe t r) :=
                    RuleProofs.eo_has_bool_type_not_arg
                      (RuleProofs.ReUnfoldNegSupport.mkStrInRe t r) hpBool
                  have hArgs :=
                    RuleProofs.ReUnfoldNegSupport.str_in_re_args_of_bool_type
                      t r hInnerBool
                  have hMkNe :
                      __mk_re_unfold_neg_concat_fixed t
                          (__eo_ite rev
                            (__eo_list_rev (Term.UOp UserOp.re_concat) r)
                            r) rev ≠ Term.Stuck := by
                    intro hStuck
                    apply hProgLocal
                    rw [hProgEq, hStuck]
                  have hIteNe :
                      __eo_ite rev
                          (__eo_list_rev (Term.UOp UserOp.re_concat) r)
                          r ≠ Term.Stuck := by
                    intro hIte
                    apply hMkNe
                    rw [hIte]
                    cases t <;> cases rev <;>
                      simp [__mk_re_unfold_neg_concat_fixed]
                  rcases
                    eo_ite_cases_of_ne_stuck rev
                      (__eo_list_rev (Term.UOp UserOp.re_concat) r) r
                      hIteNe with hRevTrue | hRevFalse
                  · subst rev
                    have hRevOrig :
                        __eo_list_rev (Term.UOp UserOp.re_concat) r ≠
                          Term.Stuck := by
                      simpa [__eo_ite, native_ite, native_teq] using hIteNe
                    have hMkTrueNe :
                        __mk_re_unfold_neg_concat_fixed t
                            (__eo_list_rev (Term.UOp UserOp.re_concat) r)
                            (Term.Boolean true) ≠ Term.Stuck := by
                      simpa [__eo_ite, native_ite, native_teq] using hMkNe
                    generalize hNorm :
                        __eo_list_rev (Term.UOp UserOp.re_concat) r = norm
                        at hMkTrueNe
                    cases norm with
                    | Apply f rArg =>
                        cases f with
                        | Apply fHead r1 =>
                            cases fHead with
                            | UOp op =>
                                by_cases hop : op = UserOp.re_concat
                                · subst op
                                  let r2 := rArg
                                  have hNormEq :
                                      __eo_list_rev
                                          (Term.UOp UserOp.re_concat) r =
                                        RuleProofs.ReUnfoldNegSupport.mkReConcat
                                          r1 r2 := by
                                    simpa [r2,
                                      RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                      using
                                      hNorm
                                  have hListR :
                                      __eo_is_list
                                          (Term.UOp UserOp.re_concat) r =
                                        Term.Boolean true :=
                                    eo_list_rev_is_list_true_of_ne_stuck
                                      (Term.UOp UserOp.re_concat) r hRevOrig
                                  have hNormTy :
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__eo_list_rev
                                              (Term.UOp UserOp.re_concat)
                                              r)) =
                                        SmtType.RegLan :=
                                    RuleProofs.smt_typeof_list_rev_re_concat_of_reglan
                                      r hListR hArgs.2 hRevOrig
                                  have hNormTyConcat :
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                              r1 r2)) =
                                        SmtType.RegLan := by
                                    simpa [hNormEq] using hNormTy
                                  have hRArgs :
                                      __smtx_typeof (__eo_to_smt r1) =
                                          SmtType.RegLan ∧
                                        __smtx_typeof (__eo_to_smt r2) =
                                          SmtType.RegLan :=
                                    RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_args_of_reglan
                                      r1 r2 hNormTyConcat
                                  have hRevRev :
                                      __eo_list_rev
                                          (Term.UOp UserOp.re_concat)
                                          (__eo_list_rev
                                            (Term.UOp UserOp.re_concat) r) ≠
                                        Term.Stuck :=
                                    eo_list_rev_list_rev_ne_stuck_of_ne_stuck
                                      (Term.UOp UserOp.re_concat) r
                                      hRevOrig
                                  have hConsRev :
                                      __eo_list_rev
                                          (Term.UOp UserOp.re_concat)
                                          (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                            r1 r2) ≠
                                        Term.Stuck := by
                                    simpa [hNormEq] using hRevRev
                                  have hR2List :
                                      __eo_is_list
                                          (Term.UOp UserOp.re_concat) r2 =
                                        Term.Boolean true := by
                                    simpa [RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                      using
                                      eo_list_rev_cons_tail_list_of_ne_stuck
                                        (Term.UOp UserOp.re_concat) r1 r2
                                        hConsRev
                                  have hRevR2Ne :
                                      __eo_list_rev
                                          (Term.UOp UserOp.re_concat) r2 ≠
                                        Term.Stuck :=
                                    eo_list_rev_ne_stuck_of_is_list_true
                                      (Term.UOp UserOp.re_concat) r2
                                      hR2List
                                  have hRevR2List :
                                      __eo_is_list
                                          (Term.UOp UserOp.re_concat)
                                          (__eo_list_rev
                                            (Term.UOp UserOp.re_concat) r2) =
                                        Term.Boolean true :=
                                    eo_list_rev_result_is_list_true_of_ne_stuck
                                      (Term.UOp UserOp.re_concat) r2
                                      hRevR2Ne
                                  have hRevR2Ty :
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__eo_list_rev
                                              (Term.UOp UserOp.re_concat)
                                              r2)) =
                                        SmtType.RegLan :=
                                    RuleProofs.smt_typeof_list_rev_re_concat_of_reglan
                                      r2 hR2List hRArgs.2 hRevR2Ne
                                  have hTailTy :
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__eo_list_singleton_elim
                                              (Term.UOp UserOp.re_concat)
                                              (__eo_list_rev
                                                (Term.UOp UserOp.re_concat)
                                                r2))) =
                                        SmtType.RegLan :=
                                    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
                                      (__eo_list_rev
                                        (Term.UOp UserOp.re_concat) r2)
                                      hRevR2List hRevR2Ty
                                  have hMkNormNe :
                                      __mk_re_unfold_neg_concat_fixed t
                                          (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                            r1 r2)
                                          (Term.Boolean true) ≠
                                        Term.Stuck := by
                                    simpa [r2,
                                      RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                      using
                                      hMkTrueNe
                                  have hFixedNe :
                                      __str_fixed_len_re r1 ≠ Term.Stuck :=
                                    RuleProofs.re_unfold_neg_concat_fixed_true_fixed_ne_of_ne_stuck
                                      t r1 r2 hMkNormNe
                                  rcases
                                    str_fixed_len_re_numeral_of_ne_stuck r1
                                      hFixedNe with
                                    ⟨i, hFixed⟩
                                  have hiTy :
                                      __smtx_typeof
                                          (__eo_to_smt (Term.Numeral i)) =
                                        SmtType.Int := by
                                    change __smtx_typeof
                                        (SmtTerm.Numeral i) = SmtType.Int
                                    simp [__smtx_typeof]
                                  have hResultBool :
                                      RuleProofs.eo_has_bool_type
                                        (RuleProofs.reUnfoldNegConcatFixedTrueFormula
                                          t r1 r2 (Term.Numeral i)) :=
                                    RuleProofs.re_unfold_neg_concat_fixed_true_formula_has_bool_type
                                      t r1 r2 (Term.Numeral i)
                                      hArgs.1 hRArgs.1 hTailTy hiTy
                                  have hFormulaEq :
                                      __mk_re_unfold_neg_concat_fixed t
                                          (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                            r1 r2)
                                          (Term.Boolean true) =
                                        RuleProofs.reUnfoldNegConcatFixedTrueFormula
                                          t r1 r2 (Term.Numeral i) :=
                                    RuleProofs.re_unfold_neg_concat_fixed_true_eq_formula
                                      t r1 r2 i hArgs.1 hRArgs.1 hTailTy
                                      hFixed
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPremM :
                                        eo_interprets M
                                          (RuleProofs.ReUnfoldNegSupport.mkNot
                                            (RuleProofs.ReUnfoldNegSupport.mkStrInRe
                                              t r))
                                          true := by
                                      have h :=
                                        hTrue.true_here p (by simp [p])
                                      simpa [hp] using h
                                    have hEval :=
                                      RuleProofs.re_unfold_neg_concat_fixed_true_eval_true
                                        M hM t r r1 r2 i hArgs.1
                                        hArgs.2 hRArgs.1 hRArgs.2
                                        hR2List hRevR2List hRevR2Ty
                                        hTailTy hRevOrig hNormEq hFixed
                                        hPremM
                                    have hInterp :
                                        eo_interprets M
                                          (RuleProofs.reUnfoldNegConcatFixedTrueFormula
                                            t r1 r2 (Term.Numeral i))
                                          true := by
                                      apply RuleProofs.eo_interprets_of_bool_eval
                                        M _ true hResultBool
                                      exact hEval
                                    simpa [hProgEq, hNormEq, hFormulaEq,
                                      __eo_ite, native_ite, native_teq] using
                                      hInterp
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (by
                                          simpa [hProgEq, hNormEq,
                                            hFormulaEq, __eo_ite,
                                            native_ite, native_teq] using
                                            hResultBool)
                                · cases t <;> cases op <;>
                                    first
                                    | exact False.elim (hop rfl)
                                    | simp [__mk_re_unfold_neg_concat_fixed] at hMkTrueNe
                            | _ =>
                                cases t <;>
                                  simp [__mk_re_unfold_neg_concat_fixed] at hMkTrueNe
                        | _ =>
                            cases t <;>
                              simp [__mk_re_unfold_neg_concat_fixed] at hMkTrueNe
                    | _ =>
                        cases t <;>
                          simp [__mk_re_unfold_neg_concat_fixed] at hMkTrueNe
                  · subst rev
                    have hMkFalseNe :
                        __mk_re_unfold_neg_concat_fixed t r
                            (Term.Boolean false) ≠ Term.Stuck := by
                      simpa [__eo_ite, native_ite, native_teq] using hMkNe
                    cases r with
                    | Apply f rArg =>
                        cases f with
                        | Apply fHead r1 =>
                            cases fHead with
                            | UOp op =>
                                by_cases hop : op = UserOp.re_concat
                                · subst op
                                  let r2 := rArg
                                  have hRArgs :
                                      __smtx_typeof (__eo_to_smt r1) =
                                          SmtType.RegLan ∧
                                        __smtx_typeof (__eo_to_smt r2) =
                                          SmtType.RegLan :=
                                      RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_args_of_reglan
                                      r1 r2
                                      (by
                                        simpa [r2,
                                          RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                          using hArgs.2)
                                  have hMkConcatNe :
                                      __mk_re_unfold_neg_concat_fixed t
                                          (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                            r1 r2)
                                          (Term.Boolean false) ≠
                                        Term.Stuck := by
                                    simpa [r2,
                                      RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                      using
                                      hMkFalseNe
                                  have hFixedNe :
                                      __str_fixed_len_re r1 ≠ Term.Stuck :=
                                    RuleProofs.re_unfold_neg_concat_fixed_false_fixed_ne_of_ne_stuck
                                      t r1 r2 hMkConcatNe
                                  rcases
                                    str_fixed_len_re_numeral_of_ne_stuck r1
                                      hFixedNe with
                                    ⟨i, hFixed⟩
                                  have hSingletonNe :
                                      __eo_list_singleton_elim
                                          (Term.UOp UserOp.re_concat) r2 ≠
                                        Term.Stuck :=
                                    RuleProofs.re_unfold_neg_concat_fixed_false_singleton_ne_of_ne_stuck
                                      t r1 r2 i hMkConcatNe hFixed
                                  have hList :
                                      __eo_is_list
                                          (Term.UOp UserOp.re_concat) r2 =
                                        Term.Boolean true :=
                                    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_list_of_ne_stuck
                                      r2 hSingletonNe
                                  have hTailTy :
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__eo_list_singleton_elim
                                              (Term.UOp UserOp.re_concat)
                                              r2)) =
                                        SmtType.RegLan :=
                                    RuleProofs.ReUnfoldNegSupport.reConcat_singleton_elim_has_reglan_type
                                      r2 hList hRArgs.2
                                  have hiTy :
                                      __smtx_typeof
                                          (__eo_to_smt (Term.Numeral i)) =
                                        SmtType.Int := by
                                    change __smtx_typeof
                                        (SmtTerm.Numeral i) = SmtType.Int
                                    simp [__smtx_typeof]
                                  have hResultBool :
                                      RuleProofs.eo_has_bool_type
                                        (RuleProofs.reUnfoldNegConcatFixedFalseFormula
                                          t r1 r2 (Term.Numeral i)) :=
                                    RuleProofs.re_unfold_neg_concat_fixed_false_formula_has_bool_type
                                      t r1 r2 (Term.Numeral i)
                                      hArgs.1 hRArgs.1 hTailTy hiTy
                                  have hFormulaEq :
                                      __mk_re_unfold_neg_concat_fixed t
                                          (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                            r1 r2)
                                          (Term.Boolean false) =
                                        RuleProofs.reUnfoldNegConcatFixedFalseFormula
                                          t r1 r2 (Term.Numeral i) :=
                                    RuleProofs.re_unfold_neg_concat_fixed_false_eq_formula
                                      t r1 r2 i hArgs.1 hRArgs.1 hTailTy
                                      hFixed
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPremM :
                                        eo_interprets M
                                          (RuleProofs.ReUnfoldNegSupport.mkNot
                                            (RuleProofs.ReUnfoldNegSupport.mkStrInRe
                                              t
                                              (RuleProofs.ReUnfoldNegSupport.mkReConcat
                                                r1 r2)))
                                          true := by
                                      have h :=
                                        hTrue.true_here p (by simp [p])
                                      simpa [hp, r2,
                                        RuleProofs.ReUnfoldNegSupport.mkReConcat]
                                        using h
                                    have hEval :=
                                      RuleProofs.re_unfold_neg_concat_fixed_false_eval_true
                                        M hM t r1 r2 i hArgs.1
                                        hRArgs.1 hRArgs.2 hList hTailTy
                                        hFixed hPremM
                                    have hInterp :
                                        eo_interprets M
                                          (RuleProofs.reUnfoldNegConcatFixedFalseFormula
                                            t r1 r2 (Term.Numeral i))
                                          true := by
                                      apply RuleProofs.eo_interprets_of_bool_eval
                                        M _ true hResultBool
                                      exact hEval
                                    simpa [hProgEq, r2,
                                      RuleProofs.ReUnfoldNegSupport.mkReConcat,
                                      hFormulaEq, __eo_ite, native_ite,
                                      native_teq] using hInterp
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (by
                                          simpa [hProgEq, r2,
                                            RuleProofs.ReUnfoldNegSupport.mkReConcat,
                                            hFormulaEq, __eo_ite,
                                            native_ite, native_teq] using
                                            hResultBool)
                                · cases t <;> cases op <;>
                                    first
                                    | exact False.elim (hop rfl)
                                    | simp [__mk_re_unfold_neg_concat_fixed] at hMkFalseNe
                            | _ =>
                                cases t <;>
                                  simp [__mk_re_unfold_neg_concat_fixed] at hMkFalseNe
                        | _ =>
                            cases t <;>
                              simp [__mk_re_unfold_neg_concat_fixed] at hMkFalseNe
                    | _ =>
                        cases t <;>
                          simp [__mk_re_unfold_neg_concat_fixed] at hMkFalseNe
