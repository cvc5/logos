module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
public import Cpc.Proofs.Translation.EoTypeofCore
import all Cpc.Proofs.Translation.EoTypeofCore
public import Cpc.Proofs.Translation.Inversions
import all Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true -> x = y := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_eq, native_teq] at h ⊢
  all_goals
    simpa [eq_comm, and_left_comm, and_assoc] using h

private theorem eq_args_of_prog_dt_inst_ne_stuck
    (a1 : Term) :
    __eo_prog_dt_inst a1 ≠ Term.Stuck ->
    ∃ c x t,
      a1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is c) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t) ∧
      __mk_dt_inst (__eo_typeof x) c x = t ∧
      __eo_prog_dt_inst a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply isHead x =>
                      cases isHead with
                      | UOp1 isOp c =>
                          cases isOp with
                          | is =>
                              cases rhs with
                              | Apply rhsF t =>
                                  cases rhsF with
                                  | Apply rhsG x2 =>
                                      cases rhsG with
                                      | UOp rhsOp =>
                                          cases rhsOp with
                                          | eq =>
                                              let body :=
                                                Term.Apply
                                                  (Term.Apply (Term.UOp UserOp.eq)
                                                    (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq) x) t)
                                              let req :=
                                                __eo_requires
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body
                                              have hOuter :
                                                  __eo_requires (__eo_eq x x2)
                                                    (Term.Boolean true) req ≠
                                                    Term.Stuck := by
                                                simpa [__eo_prog_dt_inst, req, body] using hProg
                                              have hReq : req ≠ Term.Stuck := by
                                                exact eo_requires_result_ne_stuck_of_ne_stuck
                                                  (__eo_eq x x2) (Term.Boolean true) req hOuter
                                              have hXX : x = x2 := by
                                                have hEqReq :
                                                    __eo_eq x x2 = Term.Boolean true :=
                                                  eo_requires_eq_of_ne_stuck
                                                    (__eo_eq x x2) (Term.Boolean true) req
                                                    hOuter
                                                exact eo_eq_true_eq hEqReq
                                              subst x2
                                              have hMk : __mk_dt_inst (__eo_typeof x) c x = t :=
                                                eo_requires_eq_of_ne_stuck
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body hReq
                                              have hReqEq : req = body :=
                                                eo_requires_eq_result_of_ne_stuck
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body hReq
                                              have hProgEq :
                                                  __eo_prog_dt_inst
                                                    (Term.Apply
                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                        (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                      (Term.Apply
                                                        (Term.Apply (Term.UOp UserOp.eq) x) t)) =
                                                    Term.Apply
                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                        (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                      (Term.Apply
                                                        (Term.Apply (Term.UOp UserOp.eq) x) t) := by
                                                have hOuterEq :
                                                    __eo_requires (__eo_eq x x)
                                                      (Term.Boolean true) req = req :=
                                                  eo_requires_eq_result_of_ne_stuck
                                                    (__eo_eq x x) (Term.Boolean true) req
                                                    (by simpa using hOuter)
                                                simpa [__eo_prog_dt_inst, req, body, hReqEq]
                                                  using hOuterEq.trans hReqEq
                                              exact ⟨c, x, t, rfl, hMk, hProgEq⟩
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
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_inst_eq_arg_of_typeof_bool
    (a1 : Term) :
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    __eo_prog_dt_inst a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_inst a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_inst_ne_stuck a1 hProg with
    ⟨_c, _x, _t, _hEq, _hMk, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_inst_impl
    (a1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_dt_inst a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_inst a1 = a1 :=
    prog_dt_inst_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private def smtDatatypeNumCtorsLocal : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ d => Nat.succ (smtDatatypeNumCtorsLocal d)

private theorem smtDatatypeNumCtorsLocal_resolve
    (dd : SmtDatatypeDecl) :
    ∀ d : SmtDatatype,
      smtDatatypeNumCtorsLocal (__smtx_dt_resolve d dd) =
        smtDatatypeNumCtorsLocal d
  | SmtDatatype.null => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_resolve]
  | SmtDatatype.sum c d => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_resolve,
        smtDatatypeNumCtorsLocal_resolve dd d]

private theorem eoDtcNumSelsResolve
    (dd : DatatypeDecl) :
    ∀ c : DatatypeCons,
      __smtx_dtc_num_sels
          (__eo_to_smt_datatype_cons (__eo_dtc_resolve c dd)) =
        __smtx_dtc_num_sels (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit => by
      simp [__eo_dtc_resolve, __eo_to_smt_datatype_cons,
        __smtx_dtc_num_sels]
  | DatatypeCons.cons T c => by
      cases T <;>
        simp [__eo_dtc_resolve, __eo_to_smt_datatype_cons,
          __smtx_dtc_num_sels, eoDtcNumSelsResolve dd c]

private theorem eoDtNumSelsResolve
    (dd : DatatypeDecl) :
    ∀ (d : Datatype) (i : Nat),
      __smtx_dt_num_sels
          (__eo_to_smt_datatype (__eo_dt_resolve d dd)) i =
        __smtx_dt_num_sels (__eo_to_smt_datatype d) i
  | Datatype.null, i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels]
  | Datatype.sum c d, 0 => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        eoDtcNumSelsResolve dd c]
  | Datatype.sum c d, Nat.succ i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        eoDtNumSelsResolve dd d i]

private theorem eoDatatypeNumCtorsLocalResolve
    (dd : DatatypeDecl) :
    ∀ d : Datatype,
      smtDatatypeNumCtorsLocal
          (__eo_to_smt_datatype (__eo_dt_resolve d dd)) =
        smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d)
  | Datatype.null => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype,
        smtDatatypeNumCtorsLocal]
  | Datatype.sum c d => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype,
        smtDatatypeNumCtorsLocal, eoDatatypeNumCtorsLocalResolve dd d]

private theorem smt_typeof_dt_cons_rec_non_none_implies_lt
    (T : SmtType) :
    ∀ {d : SmtDatatype} {i : Nat},
      __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None ->
      i < smtDatatypeNumCtorsLocal d
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec] at h
  | SmtDatatype.sum c d, 0, h => by
      simp [smtDatatypeNumCtorsLocal]
  | SmtDatatype.sum c d, Nat.succ i, h => by
      have h' : __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None := by
        simpa [__smtx_typeof_dt_cons_rec] using h
      have ih := smt_typeof_dt_cons_rec_non_none_implies_lt T (d := d) (i := i) h'
      simpa [smtDatatypeNumCtorsLocal] using Nat.succ_lt_succ ih

private theorem eo_mk_apply_of_ne_stuck {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem datatype_constructors_rec_ne_stuck
    (s : native_String) (root : DatatypeDecl) :
    ∀ current start,
      __eo_datatype_constructors_rec s root current start ≠ Term.Stuck
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTail : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail ≠
          Term.Stuck
      rw [eo_mk_apply_of_ne_stuck (by simp) hTail]
      simp

private theorem datatype_constructors_rec_is_list
    (s : native_String) (root : DatatypeDecl) :
    ∀ current start,
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start) =
        Term.Boolean true
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec, __eo_is_list, __eo_get_nil_rec,
        __eo_is_list_nil, __eo_is_ok, __eo_requires,native_ite,
        native_teq, native_not, SmtEval.native_not]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      have hTailList :
          __eo_is_list Term.__eo_List_cons tail = Term.Boolean true :=
        datatype_constructors_rec_is_list s root d (Nat.succ start)
      have hTailGet : __eo_get_nil_rec Term.__eo_List_cons tail ≠ Term.Stuck := by
        cases hGet : __eo_get_nil_rec Term.__eo_List_cons tail <;>
          simp [__eo_is_list, __eo_is_ok, hGet, native_teq, native_not,
            SmtEval.native_not] at hTailList ⊢
      change
        __eo_is_list Term.__eo_List_cons
          (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s root start))
            tail) =
          Term.Boolean true
      rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
      simp [__eo_is_list, __eo_get_nil_rec,__eo_is_ok,
        __eo_requires,native_ite, native_teq, native_not,
        SmtEval.native_not,hTailGet]

private theorem datatype_constructors_find_rec_self
    (s : native_String) (root : DatatypeDecl) :
    ∀ current start rel k,
      rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current) ->
      __eo_list_find_rec
        (__eo_datatype_constructors_rec s root current start)
        (Term.DtCons s root (start + rel)) (Term.Numeral k) =
        Term.Numeral (k + rel)
  | Datatype.null, start, rel, k, hlt => by
      simp [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, k, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __eo_list_find_rec
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.DtCons s root (start + 0)) (Term.Numeral k) =
              Term.Numeral (k + 0)
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_eq, native_ite, native_teq]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] using
              Nat.succ_lt_succ_iff.mp hlt
          have ih :=
            datatype_constructors_find_rec_self
              s root d (Nat.succ start) rel (k + 1) hltTail
          have hIdx :
              start + Nat.succ rel = Nat.succ start + rel := by
            simp [Nat.add_comm, Nat.add_left_comm]
          have hIdxNe : ¬ Nat.succ start + rel = start := by
            intro h
            have hltStart : start < Nat.succ start + rel :=
              Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
                (Nat.le_add_right (Nat.succ start) rel)
            exact (Nat.ne_of_lt hltStart) h.symm
          change
            __eo_list_find_rec
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.DtCons s root (start + Nat.succ rel)) (Term.Numeral k) =
              Term.Numeral (k + Nat.succ rel)
          rw [hIdx]
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_add, __eo_eq, native_ite,
            native_teq,hIdxNe]
          simpa [native_zplus, Int.add_assoc, Int.add_comm, Int.add_left_comm]
            using ih

private theorem datatype_constructors_find_self
    (s : native_String) (root : DatatypeDecl) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current)) :
    __eo_list_find Term.__eo_List_cons
      (__eo_datatype_constructors_rec s root current start)
      (Term.DtCons s root (start + rel)) =
      Term.Numeral rel := by
  have hList :
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start) =
        Term.Boolean true :=
    datatype_constructors_rec_is_list s root current start
  simp [__eo_list_find, hList, __eo_requires,
    datatype_constructors_find_rec_self s root current start rel 0 hlt,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem assoc_nil_nth_cons_succ
    (x xs : Term) (rel : Nat) :
    __assoc_nil_nth Term.__eo_List_cons
      ((Term.Apply Term.__eo_List_cons x).Apply xs)
      (Term.Numeral (Nat.succ rel)) =
    __assoc_nil_nth Term.__eo_List_cons xs (Term.Numeral rel) := by
  have hRelNe : ((Nat.succ rel : Nat) : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero rel)
  rw [__assoc_nil_nth.eq_5]
  · rw [__eo_l_1___assoc_nil_nth.eq_3]
    · simp [__eo_requires, __eo_eq, __eo_add, native_zplus, native_ite,
        native_teq, native_not, SmtEval.native_not]
      congr
      exact Int.add_neg_cancel_right (rel : Int) (1 : Int)
    · intro h
      cases h
    · intro h
      cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro f y ys hList hZero
    injection hZero with hInt
    exact hRelNe hInt

private theorem assoc_nil_nth_datatype_constructors_nth
    (s : native_String) (root : DatatypeDecl) :
    ∀ current start rel,
      rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current) ->
      __assoc_nil_nth Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start)
        (Term.Numeral rel) =
        Term.DtCons s root (start + rel)
  | Datatype.null, start, rel, hlt => by
      simp [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __assoc_nil_nth Term.__eo_List_cons
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.Numeral 0) =
              Term.DtCons s root (start + 0)
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__assoc_nil_nth, __eo_eq, native_ite, native_teq]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] using
              Nat.succ_lt_succ_iff.mp hlt
          have ih :=
            assoc_nil_nth_datatype_constructors_nth
              s root d (Nat.succ start) rel hltTail
          have hIdx :
              start + Nat.succ rel = Nat.succ start + rel := by
            simp [Nat.add_comm, Nat.add_left_comm]
          change
            __assoc_nil_nth Term.__eo_List_cons
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.Numeral (Nat.succ rel)) =
              Term.DtCons s root (start + Nat.succ rel)
          rw [hIdx]
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          rw [assoc_nil_nth_cons_succ (Term.DtCons s root start) tail rel]
          exact ih

private theorem assoc_nil_nth_datatype_constructors_find_self
    (s : native_String) (root : DatatypeDecl) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current)) :
    __assoc_nil_nth Term.__eo_List_cons
      (__eo_datatype_constructors_rec s root current start)
      (__eo_list_find Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start)
        (Term.DtCons s root (start + rel))) =
      Term.DtCons s root (start + rel) := by
  rw [datatype_constructors_find_self s root current start rel hlt]
  exact assoc_nil_nth_datatype_constructors_nth s root current start rel hlt

private theorem assoc_nil_nth_dt_constructors_find_self
    (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hlt :
      i <
        smtDatatypeNumCtorsLocal
          (__eo_to_smt_datatype (__eo_dd_lookup s d))) :
    __assoc_nil_nth Term.__eo_List_cons
      (__eo_dt_constructors (Term.DatatypeType s d))
      (__eo_list_find Term.__eo_List_cons
        (__dt_get_constructors (Term.DatatypeType s d))
        (Term.DtCons s d i)) =
      Term.DtCons s d i := by
  simpa [__eo_dt_constructors, __dt_get_constructors] using
    assoc_nil_nth_datatype_constructors_find_self
      s d (__eo_dd_lookup s d) 0 i hlt

private theorem smt_value_eq_head_of_no_apply_args
    (v : SmtValue) :
    vsm_num_apply_args v = 0 ->
    v = __smtx_apply_head_value v := by
  intro h
  cases v <;> simp [vsm_num_apply_args, __smtx_apply_head_value] at h ⊢

private theorem tester_ctor_translation_of_non_none
    (c t : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is c) t)) ≠
        SmtType.None ->
    ∃ s d i, __eo_to_smt c = SmtTerm.DtCons s d i := by
  intro hNN
  cases hC : __eo_to_smt c with
  | DtCons s d i =>
      exact ⟨s, d, i, rfl⟩
  | _ =>
      exfalso
      apply hNN
      change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c))
              (__eo_to_smt t)) =
          SmtType.None
      rw [hC]
      simp [__eo_to_smt_tester, TranslationProofs.typeof_apply_none_eq]

private theorem smt_datatype_dt_wf_rec_of_typeof
    (x : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
    __smtx_dt_wf_rec d (__smtx_dd_lookup s d) = true :=
  Smtm.datatype_wf_rec_of_type_wf
    (Smtm.smt_datatype_wf_of_non_none_type x s d hxTy)

private theorem datatype_cons_selectors_rec_nil_of_num_sels_zero
    (s : native_String) (root : DatatypeDecl) (n : Nat) :
    ∀ (d : Datatype) (i : Nat),
      i < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d) ->
      __smtx_dt_num_sels (__eo_to_smt_datatype d) i = 0 ->
      __eo_datatype_cons_selectors_rec s root n d i 0 = Term.__eo_List_nil
  | Datatype.null, i, hlt, _hNum => by
      simp [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] at hlt
  | Datatype.sum c dTail, 0, _hlt, hNum => by
      cases c with
      | unit =>
          simp [__eo_datatype_cons_selectors_rec]
      | cons U cTail =>
          simp [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_dt_num_sels, __smtx_dtc_num_sels] at hNum
  | Datatype.sum c dTail, Nat.succ i, hlt, hNum => by
      have hltTail :
          i < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype dTail) := by
        simpa [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] using
          Nat.succ_lt_succ_iff.mp hlt
      have hNumTail :
          __smtx_dt_num_sels (__eo_to_smt_datatype dTail) i = 0 := by
        simpa [__eo_to_smt_datatype, __smtx_dt_num_sels] using hNum
      simpa [__eo_dt_selectors, __eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_nil_of_num_sels_zero
          s root n dTail i hltTail hNumTail

private theorem dt_selectors_nil_of_num_sels_zero
    (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hlt :
      i <
        smtDatatypeNumCtorsLocal
          (__eo_to_smt_datatype (__eo_dd_lookup s d)))
    (hNum :
      __smtx_dt_num_sels
          (__eo_to_smt_datatype (__eo_dd_lookup s d)) i =
        0) :
    __eo_dt_selectors (Term.DtCons s d i) = Term.__eo_List_nil := by
  simpa [__eo_dt_selectors] using
    datatype_cons_selectors_rec_nil_of_num_sels_zero
      s d i (__eo_dd_resolve s d) i
      (by
        simpa [__eo_dd_resolve, eoDatatypeNumCtorsLocalResolve] using hlt)
      (by
        simpa [__eo_dd_resolve, eoDtNumSelsResolve] using hNum)

private inductive DtConsSpineRoot :
    Term -> native_String -> DatatypeDecl -> native_Nat -> Prop where
  | root (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      DtConsSpineRoot (Term.DtCons s d i) s d i
  | app {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
      (x : Term) :
      DtConsSpineRoot t s d i ->
      DtConsSpineRoot (Term.Apply t x) s d i

private theorem dtConsSpineRoot_ne_stuck
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    t ≠ Term.Stuck := by
  intro h
  cases hSp <;> cases h

private theorem smtx_typeof_eo_to_smt_stuck_none :
    __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
  native_decide

private theorem dtConsSpineRoot_apply_generic
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) (x : Term) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  induction hSp generalizing x with
  | root s d i =>
      rfl
  | app x' hSp ih =>
      cases hSp with
      | root s d i =>
          rfl
      | app x'' hSp' =>
          cases hSp' with
          | root s d i =>
              rfl
          | app x''' hSp'' =>
              cases hSp'' <;> rfl

private def mkDtSmtAppSpineRev (head : SmtTerm) : List SmtTerm -> SmtTerm
  | [] => head
  | x :: xs => SmtTerm.Apply (mkDtSmtAppSpineRev head xs) x

private def mkDtSmtValueSpineRev (head : SmtValue) : List SmtValue -> SmtValue
  | [] => head
  | x :: xs => SmtValue.Apply (mkDtSmtValueSpineRev head xs) x

private theorem mkDtSmtAppSpineRev_append_singleton
    (head x : SmtTerm) :
    ∀ xs : List SmtTerm,
      mkDtSmtAppSpineRev head (xs ++ [x]) =
        mkDtSmtAppSpineRev (SmtTerm.Apply head x) xs
  | [] => by
      simp [mkDtSmtAppSpineRev]
  | y :: ys => by
      simp [mkDtSmtAppSpineRev,
        mkDtSmtAppSpineRev_append_singleton head x ys]

private theorem vsm_apply_head_mkDtSmtValueSpineRev_dtcons
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    ∀ xs : List SmtValue,
      __smtx_apply_head_value
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        SmtValue.DtCons s d i
  | [] => by
      simp [mkDtSmtValueSpineRev, __smtx_apply_head_value]
  | x :: xs => by
      simp [mkDtSmtValueSpineRev, __smtx_apply_head_value,
        vsm_apply_head_mkDtSmtValueSpineRev_dtcons s d i xs]

private theorem vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    ∀ xs : List SmtValue,
      vsm_num_apply_args
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        xs.length
  | [] => by
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args]
  | x :: xs => by
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args,
        vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons s d i xs]

private theorem mkDtSmtValueSpineRev_append_singleton
    (head x : SmtValue) :
    ∀ xs : List SmtValue,
      mkDtSmtValueSpineRev head (xs ++ [x]) =
        mkDtSmtValueSpineRev (SmtValue.Apply head x) xs
  | [] => by
      simp [mkDtSmtValueSpineRev]
  | y :: ys => by
      simp [mkDtSmtValueSpineRev,
        mkDtSmtValueSpineRev_append_singleton head x ys]

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg
    (head a : SmtValue) :
    ∀ ys : List SmtValue,
      __smtx_apply_arg_nth_value
          (mkDtSmtValueSpineRev (SmtValue.Apply head a) ys)
          0 (ys.length + 1) = a
  | [] => by
      simp [mkDtSmtValueSpineRev, __smtx_apply_arg_nth_value, native_nateq,
        native_ite]
  | y :: ys => by
      simp [mkDtSmtValueSpineRev, __smtx_apply_arg_nth_value, native_nateq,
        native_ite,
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg head a ys]

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ
    (head a : SmtValue) :
    ∀ (ys : List SmtValue) (j : Nat),
      __smtx_apply_arg_nth_value
          (mkDtSmtValueSpineRev (SmtValue.Apply head a) ys)
          (Nat.succ j) (ys.length + 1) =
        __smtx_apply_arg_nth_value
          (mkDtSmtValueSpineRev head ys) j ys.length
  | [], j => by
      simp [mkDtSmtValueSpineRev, __smtx_apply_arg_nth_value, native_nateq,
        native_ite]
  | y :: ys, j => by
      by_cases hj : j = ys.length
      · subst j
        simp [mkDtSmtValueSpineRev, __smtx_apply_arg_nth_value, native_nateq,
          native_ite]
      · simp [mkDtSmtValueSpineRev, __smtx_apply_arg_nth_value, native_nateq,
          native_ite, hj,
          vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ head a ys j]

private def listGetOptionSmt : List SmtTerm -> Nat -> Option SmtTerm
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOptionSmt xs n

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_smt_get?
    (M : SmtModel) (head : SmtValue) :
    ∀ (xs : List SmtTerm) (j : Nat) (ti : SmtTerm),
      listGetOptionSmt xs j = some ti ->
      __smtx_apply_arg_nth_value
          (mkDtSmtValueSpineRev head
            (xs.reverse.map (fun x => __smtx_model_eval M x)))
          j xs.length =
        __smtx_model_eval M ti
  | [], j, ti, h => by
      cases j <;> simp [listGetOptionSmt] at h
  | x :: xs, Nat.zero, ti, h => by
      simp [listGetOptionSmt] at h
      subst ti
      rw [List.reverse_cons, List.map_append]
      simp only [List.map, List.length_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [List.length_reverse] using
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg head
          (__smtx_model_eval M x)
          ((List.map (fun x => __smtx_model_eval M x) xs).reverse)
  | x :: xs, Nat.succ j, ti, h => by
      have hRec :=
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_smt_get? M head
          xs j ti (by simpa [listGetOptionSmt] using h)
      rw [List.map_reverse] at hRec
      let ys := (List.map (fun x => __smtx_model_eval M x) xs).reverse
      have hRecLen :
          __smtx_apply_arg_nth_value (mkDtSmtValueSpineRev head ys) j ys.length =
            __smtx_model_eval M ti := by
        simpa [ys, List.length_reverse] using hRec
      rw [List.reverse_cons, List.map_append]
      simp only [List.map, List.length_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [ys, List.length_reverse] using
        (vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ head
          (__smtx_model_eval M x) ys j).trans hRecLen

private theorem model_eval_apply_dtcons_of_arg_ne_notvalue
    (M : SmtModel) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat)
    (v : SmtValue) :
    v ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M (SmtValue.DtCons s d i) v =
      SmtValue.Apply (SmtValue.DtCons s d i) v := by
  intro hv
  cases v <;> simp [__smtx_model_eval_apply] at hv ⊢

private theorem model_eval_apply_smt_apply_of_arg_ne_notvalue
    (M : SmtModel) (f v a : SmtValue) :
    a ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M (SmtValue.Apply f v) a =
      SmtValue.Apply (SmtValue.Apply f v) a := by
  intro ha
  cases a <;> simp [__smtx_model_eval_apply] at ha ⊢

private theorem model_eval_apply_mkDtSmtValueSpineRev_dtcons_of_arg_ne_notvalue
    (M : SmtModel) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat)
    (xs : List SmtValue) (a : SmtValue) :
    a ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M
        (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) a =
      SmtValue.Apply (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) a := by
  intro ha
  cases xs with
  | nil =>
      simpa [mkDtSmtValueSpineRev] using
        model_eval_apply_dtcons_of_arg_ne_notvalue M s d i a ha
  | cons x xs =>
      simpa [mkDtSmtValueSpineRev] using
        model_eval_apply_smt_apply_of_arg_ne_notvalue M
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) x a ha

private theorem smtx_typeof_apply_mkDtSmtAppSpineRev_dtcons
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat)
    (xs : List SmtTerm) (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) x) =
      __smtx_typeof_apply
        (__smtx_typeof (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
        (__smtx_typeof x) := by
  cases xs with
  | nil =>
      simp [mkDtSmtAppSpineRev, __smtx_typeof]
  | cons y ys =>
      simp [mkDtSmtAppSpineRev, __smtx_typeof]

private theorem mkDtSmtAppSpineRev_args_non_none_of_non_none_type
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    ∀ xs : List SmtTerm,
      __smtx_typeof (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) ≠
        SmtType.None ->
      ∀ x ∈ xs, __smtx_typeof x ≠ SmtType.None
  | [], _hNN, x, hx => by
      simp at hx
  | x :: xs, hNN, y, hy => by
      have hApplyNN :
          __smtx_typeof_apply
              (__smtx_typeof
                (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
              (__smtx_typeof x) ≠ SmtType.None := by
        rw [← smtx_typeof_apply_mkDtSmtAppSpineRev_dtcons s d i xs x]
        simpa [mkDtSmtAppSpineRev] using hNN
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hF, hX, hA, _hB⟩
      have hxNN : __smtx_typeof x ≠ SmtType.None := by
        rw [hX]
        exact hA
      have hHeadNN :
          __smtx_typeof
              (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) ≠
            SmtType.None := by
        intro hNone
        rcases hF with hF | hF <;> rw [hNone] at hF <;> cases hF
      cases hy with
      | head =>
          exact hxNN
      | tail _ hyTail =>
          exact mkDtSmtAppSpineRev_args_non_none_of_non_none_type
            s d i xs hHeadNN y hyTail

private theorem smtx_model_eval_apply_mkDtSmtAppSpineRev_dtcons
    (M : SmtModel) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat)
    (xs : List SmtTerm) (x : SmtTerm) :
    __smtx_model_eval M
        (SmtTerm.Apply (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) x) =
      __smtx_model_eval_apply M
        (__smtx_model_eval M
          (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
        (__smtx_model_eval M x) := by
  cases xs with
  | nil =>
      simp [mkDtSmtAppSpineRev, __smtx_model_eval]
  | cons y ys =>
      simp [mkDtSmtAppSpineRev, __smtx_model_eval]

private theorem smtx_model_eval_mkDtSmtAppSpineRev_dtcons
    (M : SmtModel) (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    ∀ xs : List SmtTerm,
      (∀ x ∈ xs, __smtx_model_eval M x ≠ SmtValue.NotValue) ->
      __smtx_model_eval M
          (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) =
        mkDtSmtValueSpineRev (SmtValue.DtCons s d i)
          (xs.map (__smtx_model_eval M))
  | [], _hArgs => by
      simp [mkDtSmtAppSpineRev, mkDtSmtValueSpineRev, __smtx_model_eval]
  | x :: xs, hArgs => by
      have hx : __smtx_model_eval M x ≠ SmtValue.NotValue :=
        hArgs x (by simp)
      have hxs :
          ∀ y ∈ xs, __smtx_model_eval M y ≠ SmtValue.NotValue := by
        intro y hy
        exact hArgs y (List.mem_cons_of_mem x hy)
      have hRec :=
        smtx_model_eval_mkDtSmtAppSpineRev_dtcons M s d i xs hxs
      simp only [mkDtSmtAppSpineRev, mkDtSmtValueSpineRev, List.map]
      rw [smtx_model_eval_apply_mkDtSmtAppSpineRev_dtcons M s d i xs x]
      rw [hRec]
      exact model_eval_apply_mkDtSmtValueSpineRev_dtcons_of_arg_ne_notvalue
        M s d i (xs.map (__smtx_model_eval M)) (__smtx_model_eval M x) hx

private theorem smt_model_eval_not_notvalue_of_non_none
    (M : SmtModel) (hM : model_wf M) (x : SmtTerm)
    (hNN : __smtx_typeof x ≠ SmtType.None) :
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  have hPres :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM x hNN
  intro hNot
  apply hNN
  rw [← hPres, hNot]
  simp [__smtx_typeof_value]

private theorem smtx_model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b :=
  bool_value_canonical (typeof_value_model_eval_eq_value v1 v2)

private theorem vsm_apply_ext_aux :
    ∀ (n : Nat) (v w : SmtValue),
      vsm_num_apply_args v = n ->
      __smtx_apply_head_value v = __smtx_apply_head_value w ->
      vsm_num_apply_args v = vsm_num_apply_args w ->
      (∀ j, j < vsm_num_apply_args v ->
        __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) =
          __smtx_apply_arg_nth_value w j (vsm_num_apply_args w)) ->
      v = w := by
  intro n
  induction n with
  | zero =>
      intro v w hv hHead hCount _hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      all_goals
        cases w <;> simp [vsm_num_apply_args] at hCount
        simp [__smtx_apply_head_value] at hHead ⊢
        all_goals try exact hHead
  | succ n ih =>
      intro v w hv hHead hCount hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      case Apply f a =>
        cases w <;> simp [vsm_num_apply_args] at hCount
        case Apply g b =>
          have hCountFG : vsm_num_apply_args f = vsm_num_apply_args g := hCount
          have hLast :
              __smtx_apply_arg_nth_value (SmtValue.Apply f a) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply f a)) =
                __smtx_apply_arg_nth_value (SmtValue.Apply g b) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply g b)) :=
            hArgs (vsm_num_apply_args f) (by simp [vsm_num_apply_args])
          have hab : a = b := by
            simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, hCountFG, Smtm.native_nateq, native_ite] using hLast
          have hfg : f = g := by
            apply ih f g hv
            · simpa [__smtx_apply_head_value] using hHead
            · exact hCountFG
            · intro j hj
              have hjTop : j < vsm_num_apply_args (SmtValue.Apply f a) := by
                simp [vsm_num_apply_args]
                exact Nat.lt_succ_of_lt hj
              have hArg := hArgs j hjTop
              have hNeF : j ≠ vsm_num_apply_args f := by omega
              have hNeG : j ≠ vsm_num_apply_args g := by
                intro hEq
                apply hNeF
                rw [hCountFG, hEq]
              simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, hCountFG,
                Smtm.native_nateq, native_ite, hNeF, hNeG] using hArg
          subst hfg
          subst hab
          rfl

private theorem vsm_apply_ext
    (v w : SmtValue)
    (hHead : __smtx_apply_head_value v = __smtx_apply_head_value w)
    (hCount : vsm_num_apply_args v = vsm_num_apply_args w)
    (hArgs : ∀ j, j < vsm_num_apply_args v ->
      __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) =
        __smtx_apply_arg_nth_value w j (vsm_num_apply_args w)) :
    v = w :=
  vsm_apply_ext_aux (vsm_num_apply_args v) v w rfl hHead hCount hArgs

private def dtSelectorApps
    (s : native_String) (root : DatatypeDecl) (n : native_Nat) (X : SmtTerm) :
    Datatype -> native_Nat -> native_Nat -> List SmtTerm
  | Datatype.sum DatatypeCons.unit _d, 0, _ai => []
  | Datatype.sum (DatatypeCons.cons _ _c) d, 0, ai =>
      SmtTerm.Apply
        (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n ai) X ::
      dtSelectorApps s root n X (Datatype.sum _c d) 0 (ai + 1)
  | Datatype.sum _c d, Nat.succ ci, ai =>
      dtSelectorApps s root n X d ci ai
  | Datatype.null, _ci, _ai => []

private theorem dtSelectorApps_get_of_lt
    (s : native_String) (root : DatatypeDecl) (n : native_Nat) (X : SmtTerm) :
    ∀ (d : Datatype) (ci ai j : native_Nat),
      j < (dtSelectorApps s root n X d ci ai).length ->
      listGetOptionSmt (dtSelectorApps s root n X d ci ai) j =
        some
          (SmtTerm.Apply
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n (ai + j)) X)
  | Datatype.null, ci, ai, j, hj => by
      simp [dtSelectorApps] at hj
  | Datatype.sum DatatypeCons.unit d, 0, ai, j, hj => by
      simp [dtSelectorApps] at hj
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, 0, hj => by
      simp [dtSelectorApps, listGetOptionSmt]
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, Nat.succ j, hj => by
      have hjTail :
          j < (dtSelectorApps s root n X (Datatype.sum c d) 0 (ai + 1)).length := by
        have hj' :
            Nat.succ j <
              (dtSelectorApps s root n X (Datatype.sum c d) 0 (ai + 1)).length.succ := by
          simpa [dtSelectorApps] using hj
        exact Nat.succ_lt_succ_iff.mp hj'
      have hRec :=
        dtSelectorApps_get_of_lt s root n X (Datatype.sum c d) 0 (ai + 1) j hjTail
      simpa [dtSelectorApps, listGetOptionSmt, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hRec
  | Datatype.sum c d, Nat.succ ci, ai, j, hj => by
      simpa [dtSelectorApps] using
        dtSelectorApps_get_of_lt s root n X d ci ai j
          (by simpa [dtSelectorApps] using hj)

private theorem eo_to_smt_apply_dt_sel_unreserved
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (x : Term)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false) :
    __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
      SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
        (__eo_to_smt x) := by
  change
    SmtTerm.Apply
        (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
        (__eo_to_smt x) =
      SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
        (__eo_to_smt x)
  rw [hReserved]
  rfl

private theorem eo_to_smt_mk_dt_inst_rec_selectors
    (s : native_String) (root : DatatypeDecl) (n : native_Nat)
    (x acc : Term)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hx : x ≠ Term.Stuck)
    (hAcc : DtConsSpineRoot acc s root n) :
    ∀ (d : Datatype) (ci ai : native_Nat),
      __smtx_typeof
          (__eo_to_smt
            (__mk_dt_inst_rec
              (__eo_datatype_cons_selectors_rec s root n d ci ai) x acc)) ≠
        SmtType.None ->
      __eo_to_smt
          (__mk_dt_inst_rec
            (__eo_datatype_cons_selectors_rec s root n d ci ai) x acc) =
        mkDtSmtAppSpineRev (__eo_to_smt acc)
          (dtSelectorApps s root n (__eo_to_smt x) d ci ai).reverse
  | Datatype.null, ci, ai, hNN => by
      exfalso
      apply hNN
      have hAccNe := dtConsSpineRoot_ne_stuck hAcc
      simpa [__eo_datatype_cons_selectors_rec, __mk_dt_inst_rec, hx, hAccNe]
        using smtx_typeof_eo_to_smt_stuck_none
  | Datatype.sum DatatypeCons.unit d, 0, ai, _hNN => by
      have hAccNe := dtConsSpineRoot_ne_stuck hAcc
      simp [__eo_datatype_cons_selectors_rec, __mk_dt_inst_rec,
        dtSelectorApps, mkDtSmtAppSpineRev]
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, hNN => by
      let rest :=
        __eo_datatype_cons_selectors_rec s root n
          (Datatype.sum c d) 0 (ai + 1)
      by_cases hRest : rest = Term.Stuck
      · exfalso
        apply hNN
        have hAccNe := dtConsSpineRoot_ne_stuck hAcc
        simpa [__eo_datatype_cons_selectors_rec, __mk_dt_inst_rec,
          __eo_mk_apply, rest, hRest, hx, hAccNe]
          using smtx_typeof_eo_to_smt_stuck_none
      · have hList :
            __eo_datatype_cons_selectors_rec s root n
                (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
              Term.Apply
                (Term.Apply Term.__eo_List_cons (Term.DtSel s root n ai)) rest := by
          simp [__eo_datatype_cons_selectors_rec, __eo_mk_apply, rest]
        have hAccNe := dtConsSpineRoot_ne_stuck hAcc
        have hRecNN :
            __smtx_typeof
                (__eo_to_smt
                  (__mk_dt_inst_rec rest x
                    (Term.Apply acc (Term.Apply (Term.DtSel s root n ai) x)))) ≠
              SmtType.None := by
          simpa [hList, __mk_dt_inst_rec, hx, hAccNe, rest] using hNN
        have hRec :=
          eo_to_smt_mk_dt_inst_rec_selectors s root n x
            (Term.Apply acc (Term.Apply (Term.DtSel s root n ai) x))
            hReserved hx (DtConsSpineRoot.app
              (Term.Apply (Term.DtSel s root n ai) x) hAcc)
            (Datatype.sum c d) 0 (ai + 1) hRecNN
        rw [hList]
        simp [__mk_dt_inst_rec,rest] at hRec ⊢
        rw [hRec]
        rw [dtConsSpineRoot_apply_generic hAcc]
        rw [eo_to_smt_apply_dt_sel_unreserved s root n ai x hReserved]
        have hApps :
            dtSelectorApps s root n (__eo_to_smt x)
                (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
              SmtTerm.Apply
                  (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n ai)
                  (__eo_to_smt x) ::
                dtSelectorApps s root n (__eo_to_smt x)
                  (Datatype.sum c d) 0 (ai + 1) := by
          simp [dtSelectorApps]
        rw [hApps]
        change
          mkDtSmtAppSpineRev
              (SmtTerm.Apply (__eo_to_smt acc)
              (SmtTerm.Apply
                  (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n ai)
                  (__eo_to_smt x)))
              (dtSelectorApps s root n (__eo_to_smt x)
                (Datatype.sum c d) 0 (ai + 1)).reverse =
            mkDtSmtAppSpineRev (__eo_to_smt acc)
              ((SmtTerm.Apply
                  (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n ai)
                  (__eo_to_smt x)) ::
                dtSelectorApps s root n (__eo_to_smt x)
                  (Datatype.sum c d) 0 (ai + 1)).reverse
        rw [List.reverse_cons]
        exact (mkDtSmtAppSpineRev_append_singleton
          (__eo_to_smt acc)
          (SmtTerm.Apply
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n ai)
            (__eo_to_smt x))
          (dtSelectorApps s root n (__eo_to_smt x) (Datatype.sum c d) 0
            (ai + 1)).reverse).symm
  | Datatype.sum c d, Nat.succ ci, ai, hNN => by
      simpa [__eo_datatype_cons_selectors_rec, dtSelectorApps] using
        eo_to_smt_mk_dt_inst_rec_selectors s root n x acc
          hReserved hx hAcc d ci ai
          (by simpa [__eo_datatype_cons_selectors_rec] using hNN)

private theorem dt_inst_bare_dtcons_interprets
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hXTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d))
    (hNum :
      __smtx_dt_num_sels
          (__smtx_dd_lookup s (__eo_to_smt_datatype_decl d)) i =
        0)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.DtCons s d i)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.DtCons s d i))) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · let D := __eo_to_smt_datatype_decl d
    let X := __eo_to_smt x
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
                (Term.DtCons s d i))) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X (SmtTerm.DtCons s D i)) := by
      change
        SmtTerm.eq
          (SmtTerm.Apply
            (__eo_to_smt_tester
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtCons s D i))) X)
          (SmtTerm.eq X
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s D i))) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X (SmtTerm.DtCons s D i))
      rw [hReserved]
      rfl
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [show __smtx_typeof X =
          SmtType.Datatype s D by simpa [X, D] using hXTy]
      simp
    have hEvalTy :
        __smtx_typeof_value (__smtx_model_eval M X) = SmtType.Datatype s D := by
      rw [smt_model_eval_preserves_type_of_non_none M hM X hXNN]
      simpa [X, D] using hXTy
    rw [hTranslate]
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester]
    by_cases hHead :
        __smtx_apply_head_value (__smtx_model_eval M X) =
          SmtValue.DtCons s D i
    · have hCount :
          vsm_num_apply_args (__smtx_model_eval M X) = 0 := by
        have hCountSub :=
          vsm_num_apply_args_eq_dt_num_sels_of_datatype
            (v := __smtx_model_eval M X) hHead hEvalTy
        rw [dt_num_sels_resolve D (__smtx_dd_lookup s D) i] at hCountSub
        simpa [D] using hCountSub.trans hNum
      have hVal :
          __smtx_model_eval M X = SmtValue.DtCons s D i := by
        calc
          __smtx_model_eval M X =
              __smtx_apply_head_value (__smtx_model_eval M X) :=
            smt_value_eq_head_of_no_apply_args _ hCount
          _ = SmtValue.DtCons s D i := hHead
      simp [hVal, native_veq, __smtx_model_eval_eq]
      simp [__smtx_apply_head_value]
    · have hNe :
          __smtx_model_eval M X ≠ SmtValue.DtCons s D i := by
        intro hVal
        apply hHead
        rw [hVal]
        simp [__smtx_apply_head_value]
      simp [hHead, hNe, native_veq, __smtx_model_eval_eq]

private theorem dt_inst_dtcons_interprets
    (M : SmtModel) (hM : model_wf M)
    (x t : Term) (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hXTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d))
    (hXType : __eo_typeof x = Term.DatatypeType s d)
    (hCtorLt :
      i <
        smtDatatypeNumCtorsLocal
          (__eo_to_smt_datatype (__eo_dd_lookup s d)))
    (hMk : __mk_dt_inst (__eo_typeof x) (Term.DtCons s d i) x = t)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t)) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · let D := __eo_to_smt_datatype_decl d
    let DB := __smtx_dt_resolve (__smtx_dd_lookup s D) D
    let X := __eo_to_smt x
    let T := __eo_to_smt t
    let lhs := Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x
    let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t
    have hOuterTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs rhs
        (by simpa [lhs, rhs] using hBool)
    have hLeftTranslate :
        __eo_to_smt lhs =
          SmtTerm.Apply (SmtTerm.DtTester s D i) X := by
      change
        SmtTerm.Apply
            (__eo_to_smt_tester
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtCons s D i))) X =
          SmtTerm.Apply (SmtTerm.DtTester s D i) X
      rw [hReserved]
      rfl
    have hLeftNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s D i) X) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hOuterTypes.2
    have hLhsBool : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
      rw [hLeftTranslate]
      exact dt_tester_term_typeof_of_non_none hLeftNN
    have hRhsBool : RuleProofs.eo_has_bool_type rhs := by
      unfold RuleProofs.eo_has_bool_type
      rw [← hOuterTypes.1]
      exact hLhsBool
    have hXTTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x t
        (by simpa [rhs] using hRhsBool)
    have hTTy : __smtx_typeof T = SmtType.Datatype s D := by
      rw [show __smtx_typeof T = __smtx_typeof X by
        simpa [T, X] using hXTTypes.1.symm]
      simpa [X, D] using hXTy
    have hTNN : __smtx_typeof T ≠ SmtType.None := by
      rw [hTTy]
      simp
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [show __smtx_typeof X = SmtType.Datatype s D by
        simpa [X, D] using hXTy]
      simp
    have hEvalXTy :
        __smtx_typeof_value (__smtx_model_eval M X) =
          SmtType.Datatype s D := by
      rw [smt_model_eval_preserves_type_of_non_none M hM X hXNN]
      simpa [X, D] using hXTy
    have hEvalTTy :
        __smtx_typeof_value (__smtx_model_eval M T) =
          SmtType.Datatype s D := by
      rw [smt_model_eval_preserves_type_of_non_none M hM T hTNN]
      exact hTTy
    have hxNe : x ≠ Term.Stuck := by
      intro hx
      subst x
      change __smtx_typeof SmtTerm.None = SmtType.Datatype s D at hXTy
      simp [D] at hXTy
    have hCtorNth :
        __assoc_nil_nth Term.__eo_List_cons
          (__eo_dt_constructors (Term.DatatypeType s d))
          (__eo_list_find Term.__eo_List_cons
            (__dt_get_constructors (Term.DatatypeType s d))
            (Term.DtCons s d i)) =
          Term.DtCons s d i :=
      assoc_nil_nth_dt_constructors_find_self s d i hCtorLt
    have hMkRec :
        __mk_dt_inst (__eo_typeof x) (Term.DtCons s d i) x =
          __mk_dt_inst_rec (__eo_dt_selectors (Term.DtCons s d i)) x
            (Term.DtCons s d i) := by
      rw [hXType]
      cases x
      case Stuck =>
        exact False.elim (hxNe rfl)
      all_goals
        simp [__mk_dt_inst, __dt_get_selectors, hCtorNth]
    let args := dtSelectorApps s d i X (__eo_dd_resolve s d) i 0
    have hMkTrans :
        T =
          mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) args.reverse := by
      have hRecNN :
          __smtx_typeof
              (__eo_to_smt
                (__mk_dt_inst_rec (__eo_dt_selectors (Term.DtCons s d i)) x
                  (Term.DtCons s d i))) ≠
            SmtType.None := by
        rw [← hMkRec, hMk]
        simpa [T] using hTNN
      have hRecTrans :
          __eo_to_smt
              (__mk_dt_inst_rec (__eo_dt_selectors (Term.DtCons s d i)) x
                (Term.DtCons s d i)) =
            mkDtSmtAppSpineRev
              (__eo_to_smt (Term.DtCons s d i))
              args.reverse := by
        simpa [__eo_dt_selectors, args, X] using
          eo_to_smt_mk_dt_inst_rec_selectors s d i x
            (Term.DtCons s d i) hReserved hxNe
            (DtConsSpineRoot.root s d i) (__eo_dd_resolve s d) i 0
            (by simpa [__eo_dt_selectors] using hRecNN)
      change __eo_to_smt t =
        mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) args.reverse
      rw [← hMk]
      rw [hMkRec]
      rw [hRecTrans]
      change
        mkDtSmtAppSpineRev
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s D i))
            args.reverse =
          mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) args.reverse
      rw [hReserved]
      rfl
    have hSpineNN :
        __smtx_typeof
            (mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) args.reverse) ≠
          SmtType.None := by
      rw [← hMkTrans]
      exact hTNN
    have hArgsEvalNN :
        ∀ a ∈ args.reverse, __smtx_model_eval M a ≠ SmtValue.NotValue := by
      intro a ha
      exact smt_model_eval_not_notvalue_of_non_none M hM a
        (mkDtSmtAppSpineRev_args_non_none_of_non_none_type
          s D i args.reverse hSpineNN a ha)
    have hEvalTSpine :
        __smtx_model_eval M T =
          mkDtSmtValueSpineRev (SmtValue.DtCons s D i)
            (args.reverse.map (__smtx_model_eval M)) := by
      rw [hMkTrans]
      exact smtx_model_eval_mkDtSmtAppSpineRev_dtcons M s D i
        args.reverse hArgsEvalNN
    have hEvalTHead :
        __smtx_apply_head_value (__smtx_model_eval M T) =
          SmtValue.DtCons s D i := by
      rw [hEvalTSpine]
      simp [vsm_apply_head_mkDtSmtValueSpineRev_dtcons]
    have hCountT :
        vsm_num_apply_args (__smtx_model_eval M T) =
          __smtx_dt_num_sels DB i := by
      have hCountSub :=
        vsm_num_apply_args_eq_dt_num_sels_of_datatype
          (v := __smtx_model_eval M T) hEvalTHead hEvalTTy
      simpa [DB] using hCountSub
    have hArgsLen : args.length = __smtx_dt_num_sels DB i := by
      have hValsTy :
          __smtx_typeof_value
              (mkDtSmtValueSpineRev (SmtValue.DtCons s D i)
                (args.reverse.map (__smtx_model_eval M))) =
            SmtType.Datatype s D := by
        rw [← hEvalTSpine]
        exact hEvalTTy
      have hLen :=
        vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons s D i
          (args.reverse.map (__smtx_model_eval M))
      have hNum :
          (args.reverse.map (__smtx_model_eval M)).length =
            __smtx_dt_num_sels DB i := by
        rw [← hLen]
        rw [← hEvalTSpine]
        exact hCountT
      simpa [List.length_reverse] using hNum
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t)) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X T) := by
      change
        SmtTerm.eq
          (SmtTerm.Apply
            (__eo_to_smt_tester
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtCons s D i))) X)
          (SmtTerm.eq X T) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X T)
      rw [hReserved]
      rfl
    rw [hTranslate]
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester]
    by_cases hHead :
        __smtx_apply_head_value (__smtx_model_eval M X) =
          SmtValue.DtCons s D i
    · have hCountX :
          vsm_num_apply_args (__smtx_model_eval M X) =
            __smtx_dt_num_sels DB i := by
        have hCountSub :=
          vsm_num_apply_args_eq_dt_num_sels_of_datatype
            (v := __smtx_model_eval M X) hHead hEvalXTy
        simpa [DB] using hCountSub
      have hEvalEq : __smtx_model_eval M T = __smtx_model_eval M X := by
        apply vsm_apply_ext
        · rw [hEvalTHead]
          exact hHead.symm
        · rw [hCountT, hCountX]
        · intro j hj
          have hjNum : j < __smtx_dt_num_sels DB i := by
            simpa [hCountT] using hj
          have hjArgs : j < args.length := by
            simpa [hArgsLen] using hjNum
          have hGet :=
            dtSelectorApps_get_of_lt
              s d i X (__eo_dd_resolve s d) i 0 j hjArgs
          have hArgT :
                __smtx_apply_arg_nth_value (__smtx_model_eval M T) j
                  (vsm_num_apply_args (__smtx_model_eval M T)) =
                __smtx_model_eval M
                  (SmtTerm.Apply (SmtTerm.DtSel s D i j) X) := by
            rw [hEvalTSpine]
            rw [show vsm_num_apply_args
                (mkDtSmtValueSpineRev (SmtValue.DtCons s D i)
                  (args.reverse.map (__smtx_model_eval M))) =
                args.length by
              simpa [List.length_reverse] using
                vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons s D i
                  (args.reverse.map (__smtx_model_eval M))]
            simpa [D] using
              vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_smt_get?
                M (SmtValue.DtCons s D i) args j
                (SmtTerm.Apply (SmtTerm.DtSel s D i j) X)
                (by simpa [D] using hGet)
          have hSelEval :
              __smtx_model_eval M
                  (SmtTerm.Apply (SmtTerm.DtSel s D i j) X) =
                __smtx_apply_arg_nth_value (__smtx_model_eval M X) j
                  (__smtx_dt_num_sels (__smtx_dd_lookup s D) i) := by
            simp [__smtx_model_eval, __smtx_model_eval_dt_sel, hHead,
              native_veq, native_ite]
          rw [hCountX]
          rw [dt_num_sels_resolve D (__smtx_dd_lookup s D) i]
          rw [← hSelEval]
          exact hArgT
      simp [hHead, hEvalEq, native_veq]
      rw [RuleProofs.smtx_model_eval_eq_refl (__smtx_model_eval M X)]
      exact RuleProofs.smtx_model_eval_eq_refl (SmtValue.Boolean true)
    · have hNe :
          __smtx_model_eval M X ≠ __smtx_model_eval M T := by
        intro hEq
        apply hHead
        rw [hEq]
        exact hEvalTHead
      have hEqFalse :
          __smtx_model_eval_eq (__smtx_model_eval M X)
              (__smtx_model_eval M T) =
            SmtValue.Boolean false := by
        rcases smtx_model_eval_eq_is_boolean
            (__smtx_model_eval M X) (__smtx_model_eval M T) with
          ⟨b, hb⟩
        cases b
        · exact hb
        · exfalso
          have hRel : RuleProofs.smt_value_rel
              (__smtx_model_eval M X) (__smtx_model_eval M T) := by
            rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
            exact hb
          have hEqVal :
              __smtx_model_eval M X = __smtx_model_eval M T :=
            (RuleProofs.smt_value_rel_iff_eq_of_type_ne_reglan
              hEvalXTy hEvalTTy (by intro h; cases h)).mp hRel
          exact hNe hEqVal
      simp [hHead, hEqFalse, native_veq]
      exact RuleProofs.smtx_model_eval_eq_refl (SmtValue.Boolean false)

private theorem dt_inst_tuple_unit_interprets
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (hXTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)))
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.UOp UserOp.tuple_unit)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.UOp UserOp.tuple_unit))) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · let D :=
      __eo_to_smt_tuple_decl
        (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
    let X := __eo_to_smt x
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple_unit)) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
                (Term.UOp UserOp.tuple_unit))) =
          SmtTerm.eq
            (SmtTerm.Apply
              (SmtTerm.DtTester (native_string_lit "@Tuple") D native_nat_zero) X)
            (SmtTerm.eq X
              (SmtTerm.DtCons (native_string_lit "@Tuple") D native_nat_zero)) := by
      change
        SmtTerm.eq
          (SmtTerm.Apply
            (__eo_to_smt_tester
              (SmtTerm.DtCons (native_string_lit "@Tuple") D native_nat_zero)) X)
          (SmtTerm.eq X
            (SmtTerm.DtCons (native_string_lit "@Tuple") D native_nat_zero)) =
          SmtTerm.eq
            (SmtTerm.Apply
              (SmtTerm.DtTester (native_string_lit "@Tuple") D native_nat_zero) X)
            (SmtTerm.eq X
              (SmtTerm.DtCons (native_string_lit "@Tuple") D native_nat_zero))
      rfl
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [show __smtx_typeof X =
          SmtType.Datatype (native_string_lit "@Tuple") D by
        simpa [X, D] using hXTy]
      simp
    have hEvalTy :
        __smtx_typeof_value (__smtx_model_eval M X) =
          SmtType.Datatype (native_string_lit "@Tuple") D := by
      rw [smt_model_eval_preserves_type_of_non_none M hM X hXNN]
      simpa [X, D] using hXTy
    rw [hTranslate]
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester]
    by_cases hHead :
        __smtx_apply_head_value (__smtx_model_eval M X) =
          SmtValue.DtCons (native_string_lit "@Tuple") D native_nat_zero
    · have hCount :
          vsm_num_apply_args (__smtx_model_eval M X) = 0 := by
        have hCountSub :=
          vsm_num_apply_args_eq_dt_num_sels_of_datatype
            (v := __smtx_model_eval M X) hHead hEvalTy
        simpa [D, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
          __smtx_dt_resolve, __smtx_dtc_resolve, __smtx_dt_num_sels,
          __smtx_dtc_num_sels, native_streq, native_ite] using hCountSub
      have hVal :
          __smtx_model_eval M X =
            SmtValue.DtCons (native_string_lit "@Tuple") D native_nat_zero := by
        calc
          __smtx_model_eval M X =
              __smtx_apply_head_value (__smtx_model_eval M X) :=
            smt_value_eq_head_of_no_apply_args _ hCount
          _ = SmtValue.DtCons (native_string_lit "@Tuple") D native_nat_zero :=
            hHead
      simp [hVal, native_veq, __smtx_model_eval_eq]
      simp [__smtx_apply_head_value]
    · have hNe :
          __smtx_model_eval M X ≠
            SmtValue.DtCons (native_string_lit "@Tuple") D native_nat_zero := by
        intro hVal
        apply hHead
        rw [hVal]
        simp [__smtx_apply_head_value]
      simp [hHead, hNe, native_veq, __smtx_model_eval_eq]

private theorem facts___eo_prog_dt_inst_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    eo_interprets M (__eo_prog_dt_inst a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_inst a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_inst_ne_stuck a1 hProg with
    ⟨c, x, t, hA1Eq, hMk, hProgEq⟩
  rw [hProgEq, hA1Eq]
  have hFormulaTy :
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is c) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t)) =
        Term.Bool := by
    have hTy := hResultTy
    rw [hProgEq, hA1Eq] at hTy
    exact hTy
  have hFormulaBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is c) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t)) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _
      (by simpa [hA1Eq] using hA1Trans) hFormulaTy
  let lhs := Term.Apply (Term.UOp1 UserOp1.is c) x
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs rhs
      (by simpa [lhs, rhs] using hFormulaBool)
  rcases tester_ctor_translation_of_non_none c x hTypes.2 with
    ⟨cs, cd, ci, hCTrans⟩
  have hLeftTranslate :
      __eo_to_smt lhs =
        SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt x) := by
    change
      SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) (__eo_to_smt x) =
        SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt x)
    rw [hCTrans]
    simp [__eo_to_smt_tester]
  have hLeftNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hLeftTranslate]
    exact hTypes.2
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Datatype cs cd :=
    dt_tester_arg_datatype_of_non_none hLeftNN
  rcases TranslationProofs.eo_to_smt_eq_dt_cons_cases c cs cd ci hCTrans with
    hDt | hTupleUnit
  · rcases hDt with ⟨d0, hCd, hCEq, hReserved⟩
    subst c
    subst cd
    let D := __eo_to_smt_datatype_decl d0
    let DB := __smtx_dt_resolve (__smtx_dd_lookup cs D) D
    by_cases hNum :
        __smtx_dt_num_sels (__smtx_dd_lookup cs D) ci = 0
    · have hMkBare :
          t = Term.DtCons cs d0 ci := by
        have hCtorLtSub :
            ci < smtDatatypeNumCtorsLocal
                DB := by
          have hCtorNN :
              __smtx_typeof_dt_cons_rec
                  (SmtType.Datatype cs D) DB ci ≠
                SmtType.None :=
            dt_tester_ctor_type_non_none_of_non_none hLeftNN
          exact smt_typeof_dt_cons_rec_non_none_implies_lt
            (SmtType.Datatype cs D) hCtorNN
        have hCtorLt :
            ci <
              smtDatatypeNumCtorsLocal
                (__eo_to_smt_datatype (__eo_dd_lookup cs d0)) := by
          simpa [D, DB, smtDatatypeNumCtorsLocal_resolve,
            TranslationProofs.eo_to_smt_dd_lookup] using hCtorLtSub
        have hEoXTy :
            __eo_to_smt_type (__eo_typeof x) =
              SmtType.Datatype cs D := by
          exact TranslationProofs.eo_to_smt_type_typeof_of_smt_type x hXTy
            (by simp)
        have hNameNe : cs ≠ (native_string_lit "@Tuple") :=
          TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved
        rcases TranslationProofs.eo_to_smt_type_eq_datatype_non_tuple
            hNameNe hEoXTy with
          ⟨dx, hXType, hDx⟩
        have hDxEq : dx = d0 := by
          have hTypeEq :
              Term.DatatypeType cs dx = Term.DatatypeType cs d0 :=
            TranslationProofs.eo_to_smt_type_injective_of_wf
              (A := SmtType.Datatype cs D)
              (by
                simp [__eo_to_smt_type, native_ite, hReserved, D, hDx])
              (by
                simp [__eo_to_smt_type, native_ite, hReserved, D])
              (Smtm.smt_datatype_wf_of_non_none_type
                (__eo_to_smt x) cs D (by simpa [D] using hXTy))
          injection hTypeEq
        have hMk' :
            __mk_dt_inst (__eo_typeof x) (Term.DtCons cs d0 ci) x =
              Term.DtCons cs d0 ci := by
          subst dx
          rw [hXType]
          have hSelNil :
              __eo_dt_selectors (Term.DtCons cs d0 ci) =
                Term.__eo_List_nil :=
            dt_selectors_nil_of_num_sels_zero cs d0 ci hCtorLt
              (by
                simpa [D, TranslationProofs.eo_to_smt_dd_lookup] using hNum)
          have hCtorNth :
              __assoc_nil_nth Term.__eo_List_cons
                (__eo_dt_constructors (Term.DatatypeType cs d0))
                (__eo_list_find Term.__eo_List_cons
                  (__dt_get_constructors (Term.DatatypeType cs d0))
                  (Term.DtCons cs d0 ci)) =
                Term.DtCons cs d0 ci :=
            assoc_nil_nth_dt_constructors_find_self cs d0 ci hCtorLt
          have hxNe : x ≠ Term.Stuck := by
            intro hx
            subst x
            change __smtx_typeof SmtTerm.None =
              SmtType.Datatype cs (__eo_to_smt_datatype_decl d0) at hXTy
            simp at hXTy
          cases x
          case Stuck =>
            exact False.elim (hxNe rfl)
          all_goals
            simp [__mk_dt_inst, __dt_get_selectors, hSelNil, hCtorNth,
              __mk_dt_inst_rec]
        exact hMk.symm.trans hMk'
      rw [hMkBare]
      exact dt_inst_bare_dtcons_interprets M hM x cs d0 ci
        hReserved hXTy hNum (by simpa [lhs, rhs, hMkBare] using hFormulaBool)
    · have hCtorLtSub :
          ci < smtDatatypeNumCtorsLocal
              DB := by
        have hCtorNN :
            __smtx_typeof_dt_cons_rec
                (SmtType.Datatype cs D) DB ci ≠
              SmtType.None :=
          dt_tester_ctor_type_non_none_of_non_none hLeftNN
        exact smt_typeof_dt_cons_rec_non_none_implies_lt
          (SmtType.Datatype cs D) hCtorNN
      have hCtorLt :
          ci <
            smtDatatypeNumCtorsLocal
              (__eo_to_smt_datatype (__eo_dd_lookup cs d0)) := by
        simpa [D, DB, smtDatatypeNumCtorsLocal_resolve,
          TranslationProofs.eo_to_smt_dd_lookup] using hCtorLtSub
      have hEoXTy :
          __eo_to_smt_type (__eo_typeof x) =
            SmtType.Datatype cs D := by
        exact TranslationProofs.eo_to_smt_type_typeof_of_smt_type x hXTy
          (by simp)
      have hNameNe : cs ≠ (native_string_lit "@Tuple") :=
        TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved
      rcases TranslationProofs.eo_to_smt_type_eq_datatype_non_tuple
          hNameNe hEoXTy with
        ⟨dx, hXType, hDx⟩
      have hDxEq : dx = d0 := by
        have hTypeEq :
            Term.DatatypeType cs dx = Term.DatatypeType cs d0 :=
          TranslationProofs.eo_to_smt_type_injective_of_wf
            (A := SmtType.Datatype cs D)
            (by
              simp [__eo_to_smt_type, native_ite, hReserved, D, hDx])
            (by
              simp [__eo_to_smt_type, native_ite, hReserved, D])
            (Smtm.smt_datatype_wf_of_non_none_type
              (__eo_to_smt x) cs D (by simpa [D] using hXTy))
        injection hTypeEq
      subst dx
      exact dt_inst_dtcons_interprets M hM x t cs d0 ci
        hReserved hXTy hXType hCtorLt hMk
        (by simpa [lhs, rhs] using hFormulaBool)
  · rcases hTupleUnit with ⟨hCs, hCd, hCi, hCEq⟩
    subst c
    subst cs
    subst cd
    subst ci
    have hEoXTy :
        __eo_to_smt_type (__eo_typeof x) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) := by
      exact TranslationProofs.eo_to_smt_type_typeof_of_smt_type x hXTy (by simp)
    have hXTypeUnit :
        __eo_typeof x = Term.UOp UserOp.UnitTuple := by
      rcases TranslationProofs.eo_to_smt_type_eq_tuple_datatype hEoXTy with
        hUnit | hTuple
      · exact hUnit.1
      · rcases hTuple with ⟨y, z, cTuple, hType, _hTail, hD⟩
        simp [__eo_to_smt_tuple_decl] at hD
    have hMkUnit : t = Term.UOp UserOp.tuple_unit := by
      rw [hXTypeUnit] at hMk
      have hxNe : x ≠ Term.Stuck := by
        intro hx
        subst x
        change __smtx_typeof SmtTerm.None =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) at hXTy
        simp at hXTy
      cases x <;> simp [__mk_dt_inst] at hMk ⊢
      case Stuck =>
        exact False.elim (hxNe rfl)
      all_goals exact hMk.symm
    rw [hMkUnit]
    exact dt_inst_tuple_unit_interprets M hM x hXTy
      (by simpa [lhs, rhs, hMkUnit] using hFormulaBool)

public theorem cmd_step_dt_inst_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_inst args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_inst args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_inst args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_inst args premises ≠ Term.Stuck :=
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
              have hA1TransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_inst a1) true
                exact facts___eo_prog_dt_inst_impl M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_dt_inst a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_inst a1)
                  (typed___eo_prog_dt_inst_impl a1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
