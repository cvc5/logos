module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem smt_typeof_dt_cons_rec_non_none_of_lt
    {T : SmtType} (hT : T ≠ SmtType.None) :
    ∀ {d : SmtDatatype} {i : Nat},
      i < smtDatatypeNumCtors d ->
      __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None
  | SmtDatatype.null, i, hlt => by
      simp [smtDatatypeNumCtors] at hlt
  | SmtDatatype.sum c d, 0, hlt => by
      cases c <;>
        simp [__smtx_typeof_dt_cons_rec, hT]
  | SmtDatatype.sum c d, Nat.succ i, hlt => by
      have hlt' : i < smtDatatypeNumCtors d := by
        simpa [smtDatatypeNumCtors] using Nat.succ_lt_succ_iff.mp hlt
      simpa [__smtx_typeof_dt_cons_rec] using
        smt_typeof_dt_cons_rec_non_none_of_lt (T := T) hT hlt'

private theorem eo_prog_dt_split_of_non_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_prog_dt_split x =
      __eo_list_singleton_elim (Term.UOp UserOp.or)
        (__mk_dt_split (__dt_get_constructors (__eo_typeof x)) x) := by
  intro hx
  cases x <;> simp [__eo_prog_dt_split] at hx ⊢

private theorem eo_mk_apply_of_ne_stuck {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem datatype_constructors_rec_ne_stuck
    (s : native_String) (dd : DatatypeDecl) :
    ∀ current start,
      __eo_datatype_constructors_rec s dd current start ≠ Term.Stuck
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      have hTail : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s dd start)) tail ≠
          Term.Stuck
      rw [eo_mk_apply_of_ne_stuck (by simp) hTail]
      simp

private theorem mk_dt_split_nil_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __mk_dt_split Term.__eo_List_nil x = Term.Boolean false := by
  intro hx
  cases x <;> simp [__mk_dt_split] at hx ⊢

private theorem mk_dt_split_cons_of_ne_stuck (c xs x : Term) :
    x ≠ Term.Stuck ->
    __mk_dt_split (Term.Apply (Term.Apply Term.__eo_List_cons c) xs) x =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply (Term.UOp1 UserOp1.is c) x)) (__mk_dt_split xs x) := by
  intro hx
  cases x <;> simp [__mk_dt_split] at hx ⊢

private theorem dt_split_ctor_tester_has_bool_type
    (x : Term) (s : native_String) (dd : DatatypeDecl) (idx : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl dd))
    (hIdx : idx < eoDatatypeNumCtors (__eo_dd_lookup s dd)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s dd idx)) x) := by
  let smtDD := __eo_to_smt_datatype_decl dd
  let smtBody := __smtx_dt_resolve (__smtx_dd_lookup s smtDD) smtDD
  have hCount :
      smtDatatypeNumCtors smtBody =
        eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
    calc
      smtDatatypeNumCtors smtBody =
          smtDatatypeNumCtors (__smtx_dd_lookup s smtDD) := by
        exact smtDatatypeNumCtors_resolve smtDD (__smtx_dd_lookup s smtDD)
      _ = smtDatatypeNumCtors (__eo_to_smt_datatype (__eo_dd_lookup s dd)) := by
        rw [TranslationProofs.eo_to_smt_dd_lookup]
      _ = eoDatatypeNumCtors (__eo_dd_lookup s dd) :=
        smtDatatypeNumCtors_eo_to_smt (__eo_dd_lookup s dd)
  have hCtorLt :
      idx < smtDatatypeNumCtors smtBody := by
    simpa only [hCount] using hIdx
  have hCtorNN :
      __smtx_typeof_dt_cons_rec
          (SmtType.Datatype s smtDD) smtBody idx ≠
        SmtType.None :=
    smt_typeof_dt_cons_rec_non_none_of_lt
      (T := SmtType.Datatype s smtDD) (by simp) hCtorLt
  unfold RuleProofs.eo_has_bool_type
  rw [show
      __eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s dd idx)) x) =
        SmtTerm.Apply (SmtTerm.DtTester s smtDD idx)
          (__eo_to_smt x) by
    change
      SmtTerm.Apply
          (__eo_to_smt_tester
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s smtDD idx)))
          (__eo_to_smt x) =
        SmtTerm.Apply (SmtTerm.DtTester s smtDD idx)
          (__eo_to_smt x)
    rw [hReserved]
    rfl]
  rw [typeof_dt_tester_apply_eq]
  simp [smtBody, smtDD, hxTy, hCtorNN, __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
    native_Teq]

private theorem mk_dt_split_has_bool_type
    (x : Term) (s : native_String) (dd : DatatypeDecl)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl dd)) :
    ∀ current start,
      start + eoDatatypeNumCtors current ≤
        eoDatatypeNumCtors (__eo_dd_lookup s dd) ->
      RuleProofs.eo_has_bool_type
        (__mk_dt_split (__eo_datatype_constructors_rec s dd current start) x)
  | Datatype.null, start, _hRange => by
      have hxTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hxTy]
        simp
      have hxNe : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
      rw [show __eo_datatype_constructors_rec s dd Datatype.null start =
          Term.__eo_List_nil by rfl]
      rw [mk_dt_split_nil_of_ne_stuck x hxNe]
      exact RuleProofs.eo_has_bool_type_false
  | Datatype.sum c d, start, hRange => by
      let ctor := Term.DtCons s dd start
      let tester := Term.Apply (Term.UOp1 UserOp1.is ctor) x
      let ctorTail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      let tail := __mk_dt_split ctorTail x
      have hxTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hxTy]
        simp
      have hxNe : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
      have hStartLt : start < eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
        have hPos : 0 < eoDatatypeNumCtors (Datatype.sum c d) := by
          simp [eoDatatypeNumCtors]
        omega
      have hTesterBool : RuleProofs.eo_has_bool_type tester := by
        simpa [tester, ctor] using
          dt_split_ctor_tester_has_bool_type x s dd start hReserved hxTy hStartLt
      have hTailRange :
          Nat.succ start + eoDatatypeNumCtors d ≤
            eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
        have hRange' : start + Nat.succ (eoDatatypeNumCtors d) ≤
            eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
          simpa [eoDatatypeNumCtors] using hRange
        omega
      have hTailBool : RuleProofs.eo_has_bool_type tail :=
        mk_dt_split_has_bool_type x s dd hReserved hxTy d (Nat.succ start) hTailRange
      have hCtorTailNe : ctorTail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation tail
          (RuleProofs.eo_has_smt_translation_of_has_bool_type tail hTailBool)
      change
        RuleProofs.eo_has_bool_type
          (__mk_dt_split
            (__eo_mk_apply (Term.Apply Term.__eo_List_cons ctor) ctorTail) x)
      rw [eo_mk_apply_of_ne_stuck (by simp [ctor]) hCtorTailNe]
      rw [mk_dt_split_cons_of_ne_stuck ctor ctorTail x hxNe]
      change
        RuleProofs.eo_has_bool_type
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) tester) tail)
      rw [eo_mk_apply_of_ne_stuck (by simp [tester]) hTailNe]
      exact RuleProofs.eo_has_bool_type_or_of_bool_args tester tail hTesterBool hTailBool

private theorem dt_split_ctor_tester_interprets_true
    (M : SmtModel) (x : Term) (s : native_String) (dd : DatatypeDecl) (idx : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl dd))
    (hIdx : idx < eoDatatypeNumCtors (__eo_dd_lookup s dd))
    (hHead :
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtValue.DtCons s (__eo_to_smt_datatype_decl dd) idx) :
    eo_interprets M
      (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s dd idx)) x) true := by
  have hBool :=
    dt_split_ctor_tester_has_bool_type x s dd idx hReserved hxTy hIdx
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · rw [show
        __eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s dd idx)) x) =
          SmtTerm.Apply (SmtTerm.DtTester s (__eo_to_smt_datatype_decl dd) idx)
            (__eo_to_smt x) by
      change
        SmtTerm.Apply
            (__eo_to_smt_tester
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtCons s (__eo_to_smt_datatype_decl dd) idx)))
            (__eo_to_smt x) =
          SmtTerm.Apply (SmtTerm.DtTester s (__eo_to_smt_datatype_decl dd) idx)
            (__eo_to_smt x)
      rw [hReserved]
      rfl]
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester, hHead, native_veq]

private theorem mk_dt_split_interprets_true
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (s : native_String) (dd : DatatypeDecl)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl dd)) :
    ∀ current start rel,
      start + eoDatatypeNumCtors current ≤
        eoDatatypeNumCtors (__eo_dd_lookup s dd) ->
      rel < eoDatatypeNumCtors current ->
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtValue.DtCons s (__eo_to_smt_datatype_decl dd) (start + rel) ->
      eo_interprets M
        (__mk_dt_split (__eo_datatype_constructors_rec s dd current start) x) true
  | Datatype.null, start, rel, _hRange, hRel, _hHead => by
      simp [eoDatatypeNumCtors] at hRel
  | Datatype.sum c d, start, rel, hRange, hRel, hHead => by
      let ctor := Term.DtCons s dd start
      let tester := Term.Apply (Term.UOp1 UserOp1.is ctor) x
      let ctorTail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      let tail := __mk_dt_split ctorTail x
      have hxTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hxTy]
        simp
      have hxNe : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
      have hStartLt : start < eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
        have hPos : 0 < eoDatatypeNumCtors (Datatype.sum c d) := by
          simp [eoDatatypeNumCtors]
        omega
      have hTesterBool : RuleProofs.eo_has_bool_type tester := by
        simpa [tester, ctor] using
          dt_split_ctor_tester_has_bool_type x s dd start hReserved hxTy hStartLt
      have hTailRange :
          Nat.succ start + eoDatatypeNumCtors d ≤
            eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
        have hRange' : start + Nat.succ (eoDatatypeNumCtors d) ≤
            eoDatatypeNumCtors (__eo_dd_lookup s dd) := by
          simpa [eoDatatypeNumCtors] using hRange
        omega
      have hTailBool : RuleProofs.eo_has_bool_type tail :=
        mk_dt_split_has_bool_type x s dd hReserved hxTy d (Nat.succ start) hTailRange
      have hCtorTailNe : ctorTail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation tail
          (RuleProofs.eo_has_smt_translation_of_has_bool_type tail hTailBool)
      change
        eo_interprets M
          (__mk_dt_split
            (__eo_mk_apply (Term.Apply Term.__eo_List_cons ctor) ctorTail) x) true
      rw [eo_mk_apply_of_ne_stuck (by simp [ctor]) hCtorTailNe]
      rw [mk_dt_split_cons_of_ne_stuck ctor ctorTail x hxNe]
      change
        eo_interprets M
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) tester) tail) true
      rw [eo_mk_apply_of_ne_stuck (by simp [tester]) hTailNe]
      cases rel with
      | zero =>
          have hTesterTrue : eo_interprets M tester true := by
            simpa [tester, ctor] using
              dt_split_ctor_tester_interprets_true M x s dd start
                hReserved hxTy hStartLt (by simpa using hHead)
          exact RuleProofs.eo_interprets_or_left_intro M hM tester tail
            hTesterTrue hTailBool
      | succ rel' =>
          have hRel' : rel' < eoDatatypeNumCtors d := by
            simpa [eoDatatypeNumCtors] using Nat.succ_lt_succ_iff.mp hRel
          have hHead' :
              __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt x)) =
                SmtValue.DtCons s (__eo_to_smt_datatype_decl dd)
                  (Nat.succ start + rel') := by
            rw [hHead]
            rw [Nat.add_succ, Nat.succ_add]
          have hTailTrue : eo_interprets M tail true :=
            mk_dt_split_interprets_true M hM x s dd hReserved hxTy
              d (Nat.succ start) rel' hTailRange hRel' hHead'
          exact RuleProofs.eo_interprets_or_right_intro M hM tester tail
            hTesterBool hTailTrue

private theorem orList_get_nil_rec_ne_stuck_local {c : Term} :
    CnfSupport.OrList c ->
    __eo_get_nil_rec (Term.UOp UserOp.or) c ≠ Term.Stuck := by
  intro hList
  induction hList with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not] using ih

private theorem mk_dt_split_orList
    (x : Term) (s : native_String) (dd : DatatypeDecl) :
    x ≠ Term.Stuck ->
    ∀ current start,
      CnfSupport.OrList
        (__mk_dt_split (__eo_datatype_constructors_rec s dd current start) x)
  | hx, Datatype.null, start => by
      rw [show __eo_datatype_constructors_rec s dd Datatype.null start =
          Term.__eo_List_nil by rfl]
      rw [mk_dt_split_nil_of_ne_stuck x hx]
      exact CnfSupport.OrList.false
  | hx, Datatype.sum c d, start => by
      let ctor := Term.DtCons s dd start
      let tester := Term.Apply (Term.UOp1 UserOp1.is ctor) x
      let ctorTail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      let tail := __mk_dt_split ctorTail x
      have hCtorTailNe : ctorTail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      have hTailList : CnfSupport.OrList tail :=
        mk_dt_split_orList x s dd hx d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        CnfSupport.orList_ne_stuck hTailList
      change
        CnfSupport.OrList
          (__mk_dt_split
            (__eo_mk_apply (Term.Apply Term.__eo_List_cons ctor) ctorTail) x)
      rw [eo_mk_apply_of_ne_stuck (by simp [ctor]) hCtorTailNe]
      rw [mk_dt_split_cons_of_ne_stuck ctor ctorTail x hx]
      change
        CnfSupport.OrList
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) tester) tail)
      rw [eo_mk_apply_of_ne_stuck (by simp [tester]) hTailNe]
      exact CnfSupport.OrList.cons tester tail hTailList

private theorem eo_interprets_or_left_of_right_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true ->
    eo_interprets M A true := by
  intro hBFalse hOrTrue
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ hOrTrue
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_or_left A B hOrBool
  rcases CnfSupport.eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · exact hATrue
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBFalse hOrTrue
    rw [RuleProofs.eo_to_smt_or_eq A B] at hOrTrue
    cases hAFalse with
    | intro_false _ hEvalA =>
        cases hBFalse with
        | intro_false _ hEvalB =>
            cases hOrTrue with
            | intro_true _ hEvalOr =>
                rw [__smtx_model_eval.eq_8, hEvalA, hEvalB] at hEvalOr
                simp [__smtx_model_eval_or, SmtEval.native_or] at hEvalOr

private theorem list_singleton_elim_or_singleton (x : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.or)
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) (Term.Boolean false)) = x := by
  simp [__eo_list_singleton_elim, __eo_list_singleton_elim_2, __eo_is_list,
    __eo_get_nil_rec, __eo_is_ok, __eo_requires, __eo_is_list_nil,
    __eo_ite, native_ite, native_teq, native_not, SmtEval.native_not]

private theorem list_singleton_elim_or_multiple (x y ys : Term)
    (hYs : __eo_get_nil_rec (Term.UOp UserOp.or) ys ≠ Term.Stuck) :
    __eo_list_singleton_elim (Term.UOp UserOp.or)
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) ys)) =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) ys) := by
  simp [__eo_list_singleton_elim, __eo_list_singleton_elim_2, __eo_is_list,
    __eo_get_nil_rec, __eo_is_ok, __eo_requires, __eo_is_list_nil,
    __eo_ite, native_ite, native_teq, native_not, SmtEval.native_not, hYs]

private theorem dt_split_datatype_program_true
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (s : native_String) (dd : DatatypeDecl)
    (hType : __eo_typeof x = Term.DatatypeType s dd)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl dd))
    (idx : Nat)
    (hIdx : idx < eoDatatypeNumCtors (__eo_dd_lookup s dd))
    (hHead :
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtValue.DtCons s (__eo_to_smt_datatype_decl dd) idx) :
    eo_interprets M (__eo_prog_dt_split x) true := by
  have hxTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxTy]
    simp
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  let root := __eo_dd_lookup s dd
  let raw := __mk_dt_split (__eo_datatype_constructors_rec s dd root 0) x
  have hRawBool : RuleProofs.eo_has_bool_type raw := by
    have hRange : 0 + eoDatatypeNumCtors root ≤ eoDatatypeNumCtors root := by
      omega
    simpa [raw] using
      mk_dt_split_has_bool_type x s dd hReserved hxTy root 0 hRange
  have hRawTrue : eo_interprets M raw true := by
    have hRange : 0 + eoDatatypeNumCtors root ≤ eoDatatypeNumCtors root := by
      omega
    have hHead' :
        __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt x)) =
          SmtValue.DtCons s (__eo_to_smt_datatype_decl dd) (0 + idx) := by
      simpa using hHead
    simpa [raw] using
      mk_dt_split_interprets_true M hM x s dd hReserved hxTy
        root 0 idx hRange hIdx hHead'
  rw [eo_prog_dt_split_of_non_stuck x hxNe, hType]
  change eo_interprets M (__eo_list_singleton_elim (Term.UOp UserOp.or) raw) true
  cases hRoot : __eo_dd_lookup s dd with
  | null =>
      simp [hRoot, eoDatatypeNumCtors] at hIdx
  | sum c rest =>
      cases rest with
      | null =>
          let tester :=
            Term.Apply (Term.UOp1 UserOp1.is
              (Term.DtCons s dd 0)) x
          have hRawEq :
              raw =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester)
                  (Term.Boolean false) := by
            dsimp [raw, root]
            rw [hRoot]
            change
              __mk_dt_split
                  (__eo_mk_apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.DtCons s dd 0))
                    Term.__eo_List_nil) x =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester)
                  (Term.Boolean false)
            rw [eo_mk_apply_of_ne_stuck (by simp) (by simp)]
            rw [mk_dt_split_cons_of_ne_stuck
              (Term.DtCons s dd 0)
              Term.__eo_List_nil x hxNe]
            rw [mk_dt_split_nil_of_ne_stuck x hxNe]
            rw [eo_mk_apply_of_ne_stuck (by simp) (by simp)]
          have hTesterTrue : eo_interprets M tester true := by
            rw [hRawEq] at hRawTrue
            exact eo_interprets_or_left_of_right_false M hM tester (Term.Boolean false)
              (CnfSupport.eo_interprets_false M) hRawTrue
          rw [hRawEq]
          rw [list_singleton_elim_or_singleton tester]
          exact hTesterTrue
      | sum c2 d2 =>
          let tester0 :=
            Term.Apply (Term.UOp1 UserOp1.is
              (Term.DtCons s dd 0)) x
          let tester1 :=
            Term.Apply (Term.UOp1 UserOp1.is
              (Term.DtCons s dd 1)) x
          let ys :=
            __mk_dt_split
              (__eo_datatype_constructors_rec s dd d2 2) x
          have hYsList : CnfSupport.OrList ys := by
            simpa [ys] using
              mk_dt_split_orList x s dd hxNe d2 2
          have hYsGet : __eo_get_nil_rec (Term.UOp UserOp.or) ys ≠ Term.Stuck :=
            orList_get_nil_rec_ne_stuck_local hYsList
          have hYsNe : ys ≠ Term.Stuck :=
            CnfSupport.orList_ne_stuck hYsList
          have hTailEq :
              __mk_dt_split
                  (__eo_datatype_constructors_rec s dd (Datatype.sum c2 d2) 1) x =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester1) ys := by
            let ctorTail :=
              __eo_datatype_constructors_rec s dd d2 2
            have hCtorTailNe : ctorTail ≠ Term.Stuck :=
              datatype_constructors_rec_ne_stuck s dd d2 2
            change
              __mk_dt_split
                  (__eo_mk_apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.DtCons s dd 1))
                    ctorTail) x =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester1) ys
            rw [eo_mk_apply_of_ne_stuck (by simp) hCtorTailNe]
            rw [mk_dt_split_cons_of_ne_stuck
              (Term.DtCons s dd 1)
              ctorTail x hxNe]
            change
              __eo_mk_apply (Term.Apply (Term.UOp UserOp.or) tester1) ys =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester1) ys
            rw [eo_mk_apply_of_ne_stuck (by simp [tester1]) hYsNe]
          have hRawEq :
              raw =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester0)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) tester1) ys) := by
            let ctorTail :=
              __eo_datatype_constructors_rec s dd (Datatype.sum c2 d2) 1
            have hCtorTailNe : ctorTail ≠ Term.Stuck :=
              datatype_constructors_rec_ne_stuck s dd (Datatype.sum c2 d2) 1
            dsimp [raw, root]
            rw [hRoot]
            change
              __mk_dt_split
                  (__eo_mk_apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.DtCons s dd 0))
                    ctorTail) x =
                Term.Apply (Term.Apply (Term.UOp UserOp.or) tester0)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) tester1) ys)
            rw [eo_mk_apply_of_ne_stuck (by simp) hCtorTailNe]
            rw [mk_dt_split_cons_of_ne_stuck
              (Term.DtCons s dd 0)
              ctorTail x hxNe]
            rw [hTailEq]
            rw [eo_mk_apply_of_ne_stuck (by simp)
              (by
                rw [← hTailEq]
                exact CnfSupport.orList_ne_stuck
                  (mk_dt_split_orList x s dd
                    hxNe (Datatype.sum c2 d2) 1))]
          rw [hRawEq]
          rw [list_singleton_elim_or_multiple tester0 tester1 ys hYsGet]
          simpa [hRawEq] using hRawTrue

private def smtUnitTupleDatatype : SmtDatatypeDecl :=
  __eo_to_smt_tuple_decl
    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)

private theorem eo_typeof_stuck :
    __eo_typeof Term.Stuck = Term.Stuck := by
  rfl

private theorem eo_typeof_tuple_constructor :
    __eo_typeof (Term.UOp UserOp.tuple) = Term.Stuck := by
  rfl

private theorem eo_typeof_tuple_tester_stuck (x : Term) :
    __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple)) x) =
      Term.Stuck := by
  change
    __eo_typeof_is (__eo_typeof (Term.UOp UserOp.tuple)) (__eo_typeof x) =
      Term.Stuck
  rw [eo_typeof_tuple_constructor]
  rfl

private theorem unit_tuple_tester_has_bool_type
    (x : Term)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x) := by
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtTester (native_string_lit "@Tuple") smtUnitTupleDatatype 0) (__eo_to_smt x)) =
      SmtType.Bool
  have hCtorNN :
      __smtx_typeof_dt_cons_rec
          (SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype)
          (__smtx_dt_resolve
            (__smtx_dd_lookup (native_string_lit "@Tuple") smtUnitTupleDatatype)
            smtUnitTupleDatatype) 0 ≠
        SmtType.None := by
    simp [smtUnitTupleDatatype, __eo_to_smt_tuple_decl,
      __smtx_dd_lookup, __smtx_dt_resolve, __smtx_dtc_resolve,
      native_ite, native_streq,
      __smtx_typeof_dt_cons_rec]
  have hCtorNN' :
      __smtx_typeof_dt_cons_rec
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)))
          (__smtx_dt_resolve
            (__smtx_dd_lookup (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)))
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))) 0 ≠
        SmtType.None := by
    simpa [smtUnitTupleDatatype] using hCtorNN
  rw [typeof_dt_tester_apply_eq]
  simp [smtUnitTupleDatatype, hxTy, hCtorNN', __smtx_typeof_apply,
    __smtx_typeof_guard, native_ite, native_Teq]

private theorem unit_tuple_tester_interprets_true
    (M : SmtModel) (x : Term)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype)
    (hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype) :
    eo_interprets M
      (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x) true := by
  have hBool := unit_tuple_tester_has_bool_type x hxTy
  rcases datatype_value_head_of_type hEvalTy with ⟨i, hHead⟩
  have hlt := datatype_head_index_lt hHead hEvalTy
  have hi : i = 0 := by
    simpa [smtUnitTupleDatatype, __eo_to_smt_tuple_decl,
      __smtx_dd_lookup, native_ite, native_streq,
      smtDatatypeNumCtors] using hlt
  subst i
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · change
      __smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.DtTester (native_string_lit "@Tuple") smtUnitTupleDatatype 0)
            (__eo_to_smt x)) =
        SmtValue.Boolean true
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester, hHead, native_veq]

private theorem dt_split_unit_tuple_program_true
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (hType : __eo_typeof x = Term.UOp UserOp.UnitTuple)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype)
    (hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype) :
    eo_interprets M (__eo_prog_dt_split x) true := by
  have hxTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hxTy]
    simp
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hxTrans
  let tester := Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x
  have hTesterTrue : eo_interprets M tester true := by
    simpa [tester] using unit_tuple_tester_interprets_true M x hxTy hEvalTy
  rw [eo_prog_dt_split_of_non_stuck x hxNe, hType]
  change
    eo_interprets M
      (__eo_list_singleton_elim (Term.UOp UserOp.or)
        (__mk_dt_split (__dt_get_constructors (Term.UOp UserOp.UnitTuple)) x)) true
  have hRawEq :
      __mk_dt_split (__dt_get_constructors (Term.UOp UserOp.UnitTuple)) x =
        Term.Apply (Term.Apply (Term.UOp UserOp.or) tester) (Term.Boolean false) := by
    change
      __mk_dt_split
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.UOp UserOp.tuple_unit))
            Term.__eo_List_nil) x =
        Term.Apply (Term.Apply (Term.UOp UserOp.or) tester) (Term.Boolean false)
    rw [mk_dt_split_cons_of_ne_stuck (Term.UOp UserOp.tuple_unit)
      Term.__eo_List_nil x hxNe]
    rw [mk_dt_split_nil_of_ne_stuck x hxNe]
    rw [eo_mk_apply_of_ne_stuck (by simp) (by simp)]
  rw [hRawEq]
  rw [list_singleton_elim_or_singleton tester]
  exact hTesterTrue

private theorem facts___eo_prog_dt_split_impl
    (M : SmtModel) (hM : model_wf M) (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hResultTy : __eo_typeof (__eo_prog_dt_split x) = Term.Bool) :
    eo_interprets M (__eo_prog_dt_split x) true := by
  have hxMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hxEvalTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXTrans
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  cases hT : __eo_typeof x with
  | DatatypeType s d =>
      have hxMatchT :
          __smtx_typeof (__eo_to_smt x) =
            __eo_to_smt_type (Term.DatatypeType s d) := by
        simpa [hT] using hxMatch
      cases hReserved : __eo_to_smt_reserved_datatype_name s
      · have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
          simpa [__eo_to_smt_type, hReserved, native_ite] using hxMatchT
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
          simpa [hxTy] using hxEvalTy
        rcases datatype_value_head_of_type hEvalTy with ⟨idx, hHead⟩
        have hIdxSmt := datatype_head_index_lt hHead hEvalTy
        have hIdx :
            idx < eoDatatypeNumCtors (__eo_dd_lookup s d) := by
          rw [← TranslationProofs.eo_to_smt_dd_lookup] at hIdxSmt
          simpa [smtDatatypeNumCtors_eo_to_smt] using hIdxSmt
        exact dt_split_datatype_program_true M hM x s d (by simpa using hT)
          hReserved hxTy idx hIdx hHead
      · have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
          simpa [__eo_to_smt_type, hReserved, native_ite] using hxMatchT
        exact False.elim (hXTrans hNone)
  | UOp op =>
      by_cases hUnit : op = UserOp.UnitTuple
      · subst op
        have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype := by
          simpa [hT, __eo_to_smt_type, smtUnitTupleDatatype, __eo_to_smt_tuple_decl, hxMatch] using hxMatch
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Datatype (native_string_lit "@Tuple") smtUnitTupleDatatype := by
          simpa [hxTy] using hxEvalTy
        exact dt_split_unit_tuple_program_true M hM x (by simpa using hT)
          hxTy hEvalTy
      · rw [eo_prog_dt_split_of_non_stuck x hxNe, hT] at hResultTy
        cases op <;>
          first
          | exact False.elim (hUnit rfl)
          | have hFalse : False := by
              simpa [__dt_get_constructors, __eo_dt_constructors,
                __eo_dt_constructors_main, __mk_dt_split, __eo_list_singleton_elim,
                __eo_is_list, __eo_requires, eo_typeof_stuck, native_ite,
                native_teq] using hResultTy
            exact False.elim hFalse
  | Apply f a =>
      have hxMatchT :
          __smtx_typeof (__eo_to_smt x) =
            __eo_to_smt_type (Term.Apply f a) := by
        simpa [hT] using hxMatch
      rw [eo_prog_dt_split_of_non_stuck x hxNe, hT] at hResultTy
      cases f with
      | UOp op =>
          cases op <;>
            first
            | have hFalse : False := by
                simpa [__dt_get_constructors, __eo_dt_constructors,
                  __eo_dt_constructors_main, __mk_dt_split, __eo_list_singleton_elim,
                  __eo_is_list, __eo_requires, eo_typeof_stuck, native_ite,
                  native_teq] using hResultTy
              exact False.elim hFalse
            | have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
                simpa [__eo_to_smt_type] using hxMatchT
              exact False.elim (hXTrans hNone)
      | Apply g b =>
          cases g with
          | UOp op =>
              cases op with
              | Tuple =>
                  let tester :=
                    Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple)) x
                  have hRawEq :
                      __mk_dt_split
                          (__dt_get_constructors
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.Tuple) b) a)) x =
                        Term.Apply (Term.Apply (Term.UOp UserOp.or) tester)
                          (Term.Boolean false) := by
                    change
                      __mk_dt_split
                          (Term.Apply
                            (Term.Apply Term.__eo_List_cons
                              (Term.UOp UserOp.tuple))
                            Term.__eo_List_nil) x =
                        Term.Apply (Term.Apply (Term.UOp UserOp.or) tester)
                          (Term.Boolean false)
                    rw [mk_dt_split_cons_of_ne_stuck (Term.UOp UserOp.tuple)
                      Term.__eo_List_nil x hxNe]
                    rw [mk_dt_split_nil_of_ne_stuck x hxNe]
                    rw [eo_mk_apply_of_ne_stuck (by simp) (by simp)]
                  rw [hRawEq] at hResultTy
                  rw [list_singleton_elim_or_singleton tester] at hResultTy
                  have hFalse : False := by
                    simpa [tester, eo_typeof_tuple_tester_stuck] using hResultTy
                  exact False.elim hFalse
              | _ =>
                  first
                  | have hFalse : False := by
                      simpa [__dt_get_constructors, __eo_dt_constructors,
                        __eo_dt_constructors_main, __mk_dt_split,
                        __eo_list_singleton_elim, __eo_is_list, __eo_requires,
                        eo_typeof_stuck, native_ite, native_teq] using hResultTy
                    exact False.elim hFalse
                  | have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
                      simpa [__eo_to_smt_type] using hxMatchT
                    exact False.elim (hXTrans hNone)
          | _ =>
              first
              | have hFalse : False := by
                  simpa [__dt_get_constructors, __eo_dt_constructors,
                    __eo_dt_constructors_main, __mk_dt_split, __eo_list_singleton_elim,
                    __eo_is_list, __eo_requires, eo_typeof_stuck, native_ite,
                    native_teq] using hResultTy
                exact False.elim hFalse
              | have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
                  simpa [__eo_to_smt_type] using hxMatchT
                exact False.elim (hXTrans hNone)
      | _ =>
          first
          | have hFalse : False := by
              simpa [__dt_get_constructors, __eo_dt_constructors,
                __eo_dt_constructors_main, __mk_dt_split, __eo_list_singleton_elim,
                __eo_is_list, __eo_requires, eo_typeof_stuck, native_ite,
                native_teq] using hResultTy
            exact False.elim hFalse
          | have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
              simpa [__eo_to_smt_type] using hxMatchT
            exact False.elim (hXTrans hNone)
  | _ =>
      rw [eo_prog_dt_split_of_non_stuck x hxNe, hT] at hResultTy
      simp [__dt_get_constructors, __eo_dt_constructors, __eo_dt_constructors_main,
        __mk_dt_split, __eo_list_singleton_elim,
        __eo_is_list,__eo_requires,
        eo_typeof_stuck, native_ite,
        native_teq] at hResultTy

public theorem cmd_step_dt_split_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_split args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_split args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a := hATransPair.1
              have hFact : eo_interprets M (__eo_prog_dt_split a) true := by
                exact facts___eo_prog_dt_split_impl M hM a hATrans (by
                  change __eo_typeof (__eo_prog_dt_split a) = Term.Bool at hResultTy
                  exact hResultTy)
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_split a) true
                exact hFact
              · change RuleProofs.eo_has_smt_translation (__eo_prog_dt_split a)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hFact)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
