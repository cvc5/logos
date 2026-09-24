module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
public import Cpc.Proofs.Translation.Full
import all Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

attribute [local simp] native_ite native_teq native_not native_and
set_option linter.unnecessarySimpa false

private theorem eo_requires_eq_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    T = U := by
  intro hReq
  by_cases hEq : T = U
  · exact hEq
  · exfalso
    apply hReq
    simp [__eo_requires, native_teq, hEq]

private theorem eo_requires_eq_result_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    __eo_requires T U V = V := by
  intro hReq
  have hEq : T = U := eo_requires_eq_of_ne_stuck_local T U V hReq
  subst U
  have hT : T ≠ Term.Stuck := by
    intro hStuck
    apply hReq
    simp [__eo_requires, native_teq, hStuck]
  simp [__eo_requires, native_teq, hT]

private theorem eo_requires_result_ne_stuck_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    V ≠ Term.Stuck := by
  intro hReq hV
  have hRes := eo_requires_eq_result_of_ne_stuck_local T U V hReq
  apply hReq
  rw [hRes, hV]

private theorem eq_args_of_prog_dt_updater_elim_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_updater_elim a1 ≠ Term.Stuck ->
  ∃ u t a c tu t2 t3,
    a1 =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply u t) a))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t2))
            tu)
          t3) ∧
    t2 = t ∧
    t3 = t ∧
    __mk_dt_updater_elim_rhs
      (Term.Apply (Term.Apply u t) a) c
      (__dt_get_selectors (__eo_typeof t) c) = tu ∧
    __eo_prog_dt_updater_elim a1 =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply u t) a))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t) := by
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
                  | Apply lhsF a =>
                      cases lhsF with
                      | Apply u t =>
                          cases rhs with
                          | Apply rhsF t3 =>
                              cases rhsF with
                              | Apply rhsG tu =>
                                  cases rhsG with
                                  | Apply rhsH cond =>
                                      cases rhsH with
                                      | UOp opIte =>
                                          cases opIte with
                                          | ite =>
                                              cases cond with
                                              | Apply condF t2 =>
                                                  cases condF with
                                                  | UOp1 opIs c =>
                                                      cases opIs with
                                                      | is =>
                                                          let upd :=
                                                            Term.Apply
                                                              (Term.Apply u t) a
                                                          let body :=
                                                            Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.eq)
                                                                upd)
                                                              (Term.Apply
                                                                (Term.Apply
                                                                  (Term.Apply
                                                                    (Term.UOp UserOp.ite)
                                                                    (Term.Apply
                                                                      (Term.UOp1 UserOp1.is c) t))
                                                                  tu)
                                                                t)
                                                          let inner :=
                                                            __eo_requires
                                                              (__mk_dt_updater_elim_rhs
                                                                upd c
                                                                (__dt_get_selectors
                                                                  (__eo_typeof t) c))
                                                              tu body
                                                          have hOuter :
                                                              __eo_requires
                                                                (__eo_and
                                                                  (__eo_eq t t2)
                                                                  (__eo_eq t t3))
                                                                (Term.Boolean true)
                                                                inner ≠
                                                                Term.Stuck := by
                                                            simpa [__eo_prog_dt_updater_elim,
                                                              upd, body, inner] using hProg
                                                          rcases
                                                              RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                                                t t t2 t3 inner hOuter with
                                                            ⟨hT2, hT3⟩
                                                          have hInnerNe :
                                                              inner ≠ Term.Stuck :=
                                                            eo_requires_result_ne_stuck_of_ne_stuck_local
                                                              (__eo_and
                                                                (__eo_eq t t2)
                                                                (__eo_eq t t3))
                                                              (Term.Boolean true)
                                                              inner hOuter
                                                          have hMk :
                                                              __mk_dt_updater_elim_rhs
                                                                upd c
                                                                (__dt_get_selectors
                                                                  (__eo_typeof t) c) =
                                                                tu :=
                                                            eo_requires_eq_of_ne_stuck_local
                                                              (__mk_dt_updater_elim_rhs
                                                                upd c
                                                                (__dt_get_selectors
                                                                  (__eo_typeof t) c))
                                                              tu body hInnerNe
                                                          have hInnerEq :
                                                              inner = body :=
                                                            eo_requires_eq_result_of_ne_stuck_local
                                                              (__mk_dt_updater_elim_rhs
                                                                upd c
                                                                (__dt_get_selectors
                                                                  (__eo_typeof t) c))
                                                              tu body hInnerNe
                                                          have hOuterEq :
                                                              __eo_requires
                                                                (__eo_and
                                                                  (__eo_eq t t2)
                                                                  (__eo_eq t t3))
                                                                (Term.Boolean true)
                                                                inner =
                                                                inner :=
                                                            eo_requires_eq_result_of_ne_stuck_local
                                                              (__eo_and
                                                                (__eo_eq t t2)
                                                                (__eo_eq t t3))
                                                              (Term.Boolean true)
                                                              inner hOuter
                                                          refine
                                                            ⟨u, t, a, c, tu, t2, t3,
                                                              rfl, hT2, hT3, hMk, ?_⟩
                                                          subst t2
                                                          subst t3
                                                          simpa [__eo_prog_dt_updater_elim,
                                                            upd, body, inner, hInnerEq]
                                                            using hOuterEq
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
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_updater_elim_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_updater_elim a1) = Term.Bool ->
  __eo_prog_dt_updater_elim a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_updater_elim a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_updater_elim_ne_stuck a1 hProg with
    ⟨u, t, a, c, tu, t2, t3, hA1Eq, hT2, hT3, _hMk, hProgEq⟩
  subst hA1Eq
  subst t2
  subst t3
  exact hProgEq

private theorem typed___eo_prog_dt_updater_elim_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_updater_elim a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_updater_elim a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_updater_elim a1 = a1 :=
    prog_dt_updater_elim_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem eq_rhs_ite_then_stuck_not_bool
    (lhs cond elseTerm : Term) :
    ¬ RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.ite) cond) Term.Stuck)
          elseTerm)) := by
  intro h
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      lhs
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) cond) Term.Stuck)
        elseTerm) h
  have hNone :
      __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.ite) cond) Term.Stuck)
            elseTerm)) =
        SmtType.None := by
    change
      __smtx_typeof
        (SmtTerm.ite (__eo_to_smt cond) SmtTerm.None
          (__eo_to_smt elseTerm)) =
      SmtType.None
    rw [typeof_ite_eq]
    cases hCond : __smtx_typeof (__eo_to_smt cond) <;>
      cases hElse : __smtx_typeof (__eo_to_smt elseTerm) <;>
      simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hNon := hTypes.2
  rw [hTypes.1] at hNon
  exact hNon hNone

private theorem eq_rhs_ite_bad_tester_not_bool
    (lhs c t tu : Term)
    (hTester : __eo_to_smt_tester (__eo_to_smt c) = SmtTerm.None) :
    ¬ RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t)) := by
  intro h
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      lhs
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.UOp1 UserOp1.is c) t))
          tu)
        t) h
  have hNone :
      __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.UOp1 UserOp1.is c) t)) =
        SmtType.None := by
    change
      __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c))
          (__eo_to_smt t)) =
      SmtType.None
    rw [hTester]
    simp [TranslationProofs.typeof_apply_none_eq]
  have hIteNone :
      __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.UOp1 UserOp1.is c) t))
              tu)
            t)) =
      SmtType.None := by
    have hCondNone :
        __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c))
            (__eo_to_smt t)) =
        SmtType.None := by
      exact hNone
    change
      __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c))
            (__eo_to_smt t))
          (__eo_to_smt tu) (__eo_to_smt t)) =
      SmtType.None
    rw [typeof_ite_eq]
    rw [hCondNone]
    cases hThen : __smtx_typeof (__eo_to_smt tu) <;>
      cases hElse : __smtx_typeof (__eo_to_smt t) <;>
      simp [__smtx_typeof_ite]
  have hNon := hTypes.2
  rw [hTypes.1] at hNon
  exact hNon hIteNone

private theorem eq_rhs_ite_stuck_subst_not_bool
    (lhs c t tu : Term)
    (hStuck : Term.Stuck = tu) :
    ¬ RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t)) := by
  intro hBool
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.UOp1 UserOp1.is c) t))
              Term.Stuck)
            t)) := by
    rw [← hStuck] at hBool
    simpa using hBool
  exact
    (eq_rhs_ite_then_stuck_not_bool lhs
      (Term.Apply (Term.UOp1 UserOp1.is c) t) t) hBool'

private theorem mk_dt_updater_elim_rhs_tuple_update_stuck_of_ne_tuple
    (idx t a c ss : Term) :
    c ≠ Term.UOp UserOp.tuple ->
    __mk_dt_updater_elim_rhs
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)
        c ss =
      Term.Stuck := by
  intro hNe
  cases c with
  | UOp op =>
      cases op <;> cases ss <;> simp [__mk_dt_updater_elim_rhs] at hNe ⊢
  | _ =>
      cases ss <;> simp [__mk_dt_updater_elim_rhs]

private theorem mk_dt_updater_elim_rhs_non_updater_stuck
    (u t a c ss : Term) :
    (∀ sel, u ≠ Term.UOp1 UserOp1.update sel) ->
    (∀ idx, u ≠ Term.UOp1 UserOp1.tuple_update idx) ->
    __mk_dt_updater_elim_rhs
        (Term.Apply (Term.Apply u t) a) c ss =
      Term.Stuck := by
  intro hNotUpdate hNotTupleUpdate
  cases u with
  | UOp1 op idx =>
      cases op with
      | update =>
          exact False.elim (hNotUpdate idx rfl)
      | tuple_update =>
          exact False.elim (hNotTupleUpdate idx rfl)
      | _ =>
          cases c <;> cases ss <;> simp [__mk_dt_updater_elim_rhs]
  | _ =>
      cases c <;> cases ss <;> simp [__mk_dt_updater_elim_rhs]

private theorem eo_to_smt_updater_typeof_none_of_not_dt_sel
    (sel t u : SmtTerm) :
    (∀ s d i j, sel ≠ SmtTerm.DtSel s d i j) ->
    __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None := by
  intro hSel
  cases sel <;> simp [__eo_to_smt_updater]
  case DtSel s d i j =>
    exact False.elim (hSel s d i j rfl)

private theorem smtx_ite_cond_non_none
    (c x y : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c x y) ≠ SmtType.None ->
    __smtx_typeof c ≠ SmtType.None := by
  intro hNN hC
  apply hNN
  cases hc : __smtx_typeof c <;>
    cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
    simp [__smtx_typeof, __smtx_typeof_ite,
      hc, hx, hy] at hC ⊢

private theorem smtx_ite_then_non_none
    (c x y : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c x y) ≠ SmtType.None ->
    __smtx_typeof x ≠ SmtType.None := by
  intro hNN hX
  apply hNN
  cases hc : __smtx_typeof c <;>
    cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
    simp [__smtx_typeof, __smtx_typeof_ite, native_ite, native_Teq,
      hc, hx, hy] at hX ⊢

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

private theorem smtx_typeof_eo_to_smt_stuck_none :
    __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
  native_decide

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

private def smtUpdaterArg
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) (q : native_Nat) : SmtTerm :=
  native_ite (native_nateq m q) u
    (SmtTerm.Apply (SmtTerm.DtSel s d i q) t)

private def smtUpdaterRecRange
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) : native_Nat -> native_Nat -> SmtTerm -> SmtTerm
  | ai, 0, acc => acc
  | ai, Nat.succ k, acc =>
      smtUpdaterRecRange s d i m t u (Nat.succ ai) k
        (SmtTerm.Apply acc (smtUpdaterArg s d i m t u ai))

private def smtUpdaterRecOffset
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) : native_Nat -> native_Nat -> SmtTerm -> SmtTerm
  | ai, 0, acc => acc
  | ai, Nat.succ k, acc =>
      SmtTerm.Apply
        (smtUpdaterRecOffset s d i m t u ai k acc)
        (smtUpdaterArg s d i m t u (ai + k))

private theorem smtUpdaterRecOffset_shift
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) :
    ∀ (ai k : native_Nat) (acc : SmtTerm),
      smtUpdaterRecOffset s d i m t u (Nat.succ ai) k
          (SmtTerm.Apply acc (smtUpdaterArg s d i m t u ai)) =
        smtUpdaterRecOffset s d i m t u ai (Nat.succ k) acc
  | ai, 0, acc => by
      simp [smtUpdaterRecOffset]
  | ai, Nat.succ k, acc => by
      simp [smtUpdaterRecOffset, smtUpdaterRecOffset_shift s d i m t u ai k acc,
        Nat.add_comm, Nat.add_left_comm]

private theorem smtUpdaterRecRange_eq_offset
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) :
    ∀ (ai k : native_Nat) (acc : SmtTerm),
      smtUpdaterRecRange s d i m t u ai k acc =
        smtUpdaterRecOffset s d i m t u ai k acc
  | ai, 0, acc => by
      simp [smtUpdaterRecRange, smtUpdaterRecOffset]
  | ai, Nat.succ k, acc => by
      simp [smtUpdaterRecRange]
      rw [smtUpdaterRecRange_eq_offset s d i m t u (Nat.succ ai) k]
      exact smtUpdaterRecOffset_shift s d i m t u ai k acc

private theorem smtUpdaterRecOffset_zero_eq_updater_rec
    (s : native_String) (d : SmtDatatypeDecl) (i m : native_Nat)
    (t u : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      smtUpdaterRecOffset s d i m t u 0 k acc =
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) k t u acc
  | 0, acc => by
      simp [smtUpdaterRecOffset, __eo_to_smt_updater_rec]
  | Nat.succ k, acc => by
      simp [smtUpdaterRecOffset, __eo_to_smt_updater_rec,
        smtUpdaterRecOffset_zero_eq_updater_rec s d i m t u k acc,
        smtUpdaterArg]

private def smtDtUpdaterElimRhsRec
    (s : native_String) (root : DatatypeDecl) (n m : native_Nat)
    (t u : SmtTerm) : Datatype -> native_Nat -> native_Nat -> SmtTerm -> SmtTerm
  | Datatype.null, _ci, _ai, acc => acc
  | Datatype.sum DatatypeCons.unit _d, 0, _ai, acc => acc
  | Datatype.sum (DatatypeCons.cons _ c) d, 0, ai, acc =>
      smtDtUpdaterElimRhsRec s root n m t u (Datatype.sum c d) 0 (Nat.succ ai)
        (SmtTerm.Apply acc
          (smtUpdaterArg s (__eo_to_smt_datatype_decl root) n m t u ai))
  | Datatype.sum _c d, Nat.succ ci, ai, acc =>
      smtDtUpdaterElimRhsRec s root n m t u d ci ai acc

private theorem smtDtUpdaterElimRhsRec_ctor_eq_range
    (s : native_String) (root : DatatypeDecl) (n m : native_Nat)
    (t u : SmtTerm) :
    ∀ (c : DatatypeCons) (rest : Datatype) (ai : native_Nat)
      (acc : SmtTerm),
      smtDtUpdaterElimRhsRec s root n m t u
          (Datatype.sum c rest) 0 ai acc =
        smtUpdaterRecRange s (__eo_to_smt_datatype_decl root) n m t u ai
          (__smtx_dtc_num_sels (__eo_to_smt_datatype_cons c)) acc
  | DatatypeCons.unit, rest, ai, acc => by
      simp [smtDtUpdaterElimRhsRec, smtUpdaterRecRange,
        __eo_to_smt_datatype_cons, __smtx_dtc_num_sels]
  | DatatypeCons.cons U c, rest, ai, acc => by
      simp [smtDtUpdaterElimRhsRec, smtUpdaterRecRange,
        __eo_to_smt_datatype_cons, __smtx_dtc_num_sels,
        smtDtUpdaterElimRhsRec_ctor_eq_range s root n m t u c rest
          (Nat.succ ai)
          (SmtTerm.Apply acc
            (smtUpdaterArg s (__eo_to_smt_datatype_decl root) n m t u ai))]

private theorem smtDtUpdaterElimRhsRec_eq_range
    (s : native_String) (root : DatatypeDecl) (n m : native_Nat)
    (t u : SmtTerm) :
    ∀ (current : Datatype) (ci ai : native_Nat) (acc : SmtTerm),
      smtDtUpdaterElimRhsRec s root n m t u current ci ai acc =
        smtUpdaterRecRange s (__eo_to_smt_datatype_decl root) n m t u ai
          (__smtx_dt_num_sels (__eo_to_smt_datatype current) ci) acc
  | Datatype.null, ci, ai, acc => by
      cases ci <;> simp [smtDtUpdaterElimRhsRec, smtUpdaterRecRange,
        __eo_to_smt_datatype, __smtx_dt_num_sels]
  | Datatype.sum c rest, 0, ai, acc => by
      simpa [__eo_to_smt_datatype, __smtx_dt_num_sels] using
        smtDtUpdaterElimRhsRec_ctor_eq_range s root n m t u c rest ai acc
  | Datatype.sum c rest, Nat.succ ci, ai, acc => by
      simpa [smtDtUpdaterElimRhsRec, __eo_to_smt_datatype,
        __smtx_dt_num_sels] using
        smtDtUpdaterElimRhsRec_eq_range s root n m t u rest ci ai acc

private theorem eoDtcNumSelsResolveLocal
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
          __smtx_dtc_num_sels, eoDtcNumSelsResolveLocal dd c]

private theorem eoDtNumSelsResolveLocal
    (dd : DatatypeDecl) :
    ∀ (d : Datatype) (i : Nat),
      __smtx_dt_num_sels
          (__eo_to_smt_datatype (__eo_dt_resolve d dd)) i =
        __smtx_dt_num_sels (__eo_to_smt_datatype d) i
  | Datatype.null, i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels]
  | Datatype.sum c d, 0 => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        eoDtcNumSelsResolveLocal dd c]
  | Datatype.sum c d, Nat.succ i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        eoDtNumSelsResolveLocal dd d i]

private theorem smtDtUpdaterElimRhsRec_self_eq_updater_rec
    (s : native_String) (root : DatatypeDecl) (n m : native_Nat)
    (t u acc : SmtTerm) :
    smtDtUpdaterElimRhsRec s root n m t u (__eo_dd_resolve s root) n 0 acc =
      __eo_to_smt_updater_rec
        (SmtTerm.DtSel s (__eo_to_smt_datatype_decl root) n m)
        (__smtx_dt_num_sels
          (__eo_to_smt_datatype (__eo_dd_lookup s root)) n) t u acc := by
  rw [smtDtUpdaterElimRhsRec_eq_range]
  rw [smtUpdaterRecRange_eq_offset]
  simpa [__eo_dd_resolve, eoDtNumSelsResolveLocal] using
    smtUpdaterRecOffset_zero_eq_updater_rec
      s (__eo_to_smt_datatype_decl root) n m t u
      (__smtx_dt_num_sels
        (__eo_to_smt_datatype (__eo_dd_resolve s root)) n) acc

private theorem eo_to_smt_dt_updater_elim_rhs_selectors
    (s : native_String) (root : DatatypeDecl) (n m : native_Nat)
    (t a acc : Term)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hAcc : DtConsSpineRoot acc s root n) :
    ∀ (d : Datatype) (ci ai : native_Nat),
      __smtx_typeof
          (__eo_to_smt
            (__dt_updater_elim_rhs
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.update
                  (Term.DtSel s root n m)) t) a)
              (__eo_datatype_cons_selectors_rec s root n d ci ai)
              acc)) ≠
        SmtType.None ->
      __eo_to_smt
          (__dt_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.update
                (Term.DtSel s root n m)) t) a)
            (__eo_datatype_cons_selectors_rec s root n d ci ai)
            acc) =
        smtDtUpdaterElimRhsRec s root n m (__eo_to_smt t) (__eo_to_smt a)
          d ci ai (__eo_to_smt acc)
  | Datatype.null, ci, ai, hNN => by
      exfalso
      apply hNN
      have hAccNe := dtConsSpineRoot_ne_stuck hAcc
      simpa [__eo_datatype_cons_selectors_rec, __dt_updater_elim_rhs,
        hAccNe] using smtx_typeof_eo_to_smt_stuck_none
  | Datatype.sum DatatypeCons.unit d, 0, ai, _hNN => by
      have hAccNe := dtConsSpineRoot_ne_stuck hAcc
      simp [__eo_datatype_cons_selectors_rec, __dt_updater_elim_rhs,
        __eo_l_1___dt_updater_elim_rhs, smtDtUpdaterElimRhsRec]
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, hNN => by
      let rest :=
        __eo_datatype_cons_selectors_rec s root n
          (Datatype.sum c d) 0 (Nat.succ ai)
      by_cases hRest : rest = Term.Stuck
      · exfalso
        apply hNN
        have hAccNe := dtConsSpineRoot_ne_stuck hAcc
        simpa [__eo_datatype_cons_selectors_rec, __eo_mk_apply, rest, hRest,
          __dt_updater_elim_rhs, hAccNe] using smtx_typeof_eo_to_smt_stuck_none
      · have hList :
            __eo_datatype_cons_selectors_rec s root n
                (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
              Term.Apply
                (Term.Apply Term.__eo_List_cons (Term.DtSel s root n ai))
                rest := by
          simp [__eo_datatype_cons_selectors_rec, __eo_mk_apply, rest]
        have hAccNe := dtConsSpineRoot_ne_stuck hAcc
        by_cases hEq : m = ai
        · subst ai
          have hRecNN :
              __smtx_typeof
                  (__eo_to_smt
                    (__dt_updater_elim_rhs
                      (Term.Apply
                        (Term.Apply (Term.UOp1 UserOp1.update
                          (Term.DtSel s root n m)) t) a)
                      rest (Term.Apply acc a))) ≠
                SmtType.None := by
            simpa [hList, __dt_updater_elim_rhs, __eo_eq, native_teq,
              native_nateq, hAccNe, rest] using hNN
          have hRec :=
            eo_to_smt_dt_updater_elim_rhs_selectors s root n m t a
              (Term.Apply acc a) hReserved
              (DtConsSpineRoot.app a hAcc) (Datatype.sum c d) 0
              (Nat.succ m) hRecNN
          rw [hList]
          simp [__dt_updater_elim_rhs, __eo_eq, native_teq,rest] at hRec ⊢
          rw [hRec]
          rw [dtConsSpineRoot_apply_generic hAcc a]
          simp [smtDtUpdaterElimRhsRec, smtUpdaterArg, native_nateq]
        · have hRecNN :
              __smtx_typeof
                  (__eo_to_smt
                    (__dt_updater_elim_rhs
                      (Term.Apply
                        (Term.Apply (Term.UOp1 UserOp1.update
                          (Term.DtSel s root n m)) t) a)
                      rest
                      (Term.Apply acc (Term.Apply (Term.DtSel s root n ai) t)))) ≠
                SmtType.None := by
            have hEq' : ai ≠ m := by
              intro h
              exact hEq h.symm
            simpa [hList, __dt_updater_elim_rhs,
              __eo_l_1___dt_updater_elim_rhs, __eo_eq, native_teq,
              native_nateq, hEq, hEq', hAccNe, rest] using hNN
          have hRec :=
            eo_to_smt_dt_updater_elim_rhs_selectors s root n m t a
              (Term.Apply acc (Term.Apply (Term.DtSel s root n ai) t))
              hReserved
              (DtConsSpineRoot.app (Term.Apply (Term.DtSel s root n ai) t) hAcc)
              (Datatype.sum c d) 0 (Nat.succ ai) hRecNN
          rw [hList]
          have hEq' : ai ≠ m := by
            intro h
            exact hEq h.symm
          simp [__dt_updater_elim_rhs, __eo_l_1___dt_updater_elim_rhs,
            __eo_eq, native_teq, hEq', rest] at hRec ⊢
          rw [hRec]
          rw [dtConsSpineRoot_apply_generic hAcc
            (Term.Apply (Term.DtSel s root n ai) t)]
          rw [eo_to_smt_apply_dt_sel_unreserved s root n ai t hReserved]
          simp [smtDtUpdaterElimRhsRec, smtUpdaterArg, native_nateq, hEq]
  | Datatype.sum c d, Nat.succ ci, ai, hNN => by
      simpa [__eo_datatype_cons_selectors_rec, smtDtUpdaterElimRhsRec] using
        eo_to_smt_dt_updater_elim_rhs_selectors s root n m t a acc
          hReserved hAcc d ci ai
          (by simpa [__eo_datatype_cons_selectors_rec] using hNN)

private theorem datatype_cons_selectors_find_rec_false_implies_dt_sel
    (s : native_String) (root : DatatypeDecl) (n : native_Nat)
    (target start : Term) :
    ∀ (d : Datatype) (ci ai : native_Nat),
      __eo_is_neg
          (__eo_list_find_rec
            (__eo_datatype_cons_selectors_rec s root n d ci ai)
            target start) =
        Term.Boolean false ->
      ∃ j, target = Term.DtSel s root n j
  | Datatype.null, ci, ai, h => by
      cases ci <;> cases target <;> cases start <;>
        simp [__eo_datatype_cons_selectors_rec,
          __eo_list_find_rec,__eo_is_neg
          ] at h
  | Datatype.sum DatatypeCons.unit d, 0, ai, h => by
      cases target <;> cases start <;>
        simp [__eo_datatype_cons_selectors_rec,
          __eo_list_find_rec,__eo_is_neg, native_zlt, SmtEval.native_zlt] at h
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, h => by
      let rest :=
        __eo_datatype_cons_selectors_rec s root n
          (Datatype.sum c d) 0 (Nat.succ ai)
      by_cases hRest : rest = Term.Stuck
      · simp [__eo_datatype_cons_selectors_rec, __eo_mk_apply, rest, hRest,
          __eo_list_find_rec, __eo_is_neg] at h
      · have hList :
            __eo_datatype_cons_selectors_rec s root n
                (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
              Term.Apply
                (Term.Apply Term.__eo_List_cons (Term.DtSel s root n ai))
                rest := by
          simp [__eo_datatype_cons_selectors_rec, __eo_mk_apply, rest]
        by_cases hHead : target = Term.DtSel s root n ai
        · exact ⟨ai, hHead⟩
        · have hTail :
              __eo_is_neg
                  (__eo_list_find_rec rest target
                    (__eo_add start (Term.Numeral 1))) =
                Term.Boolean false := by
            have hHead' : Term.DtSel s root n ai ≠ target := by
              intro hEq
              exact hHead hEq.symm
            have h' := h
            rw [hList] at h'
            cases target <;> cases start <;>
              simpa [__eo_list_find_rec, __eo_eq, __eo_ite, __eo_add,
                __eo_is_neg, native_teq, hHead, hHead', rest,
                native_zlt, SmtEval.native_zlt] using h'
          simpa [rest] using
            datatype_cons_selectors_find_rec_false_implies_dt_sel
              s root n target (__eo_add start (Term.Numeral 1))
              (Datatype.sum c d) 0 (Nat.succ ai) hTail
  | Datatype.sum c d, Nat.succ ci, ai, h => by
      exact
        datatype_cons_selectors_find_rec_false_implies_dt_sel
          s root n target start d ci ai
          (by simpa [__eo_datatype_cons_selectors_rec] using h)

private theorem datatype_cons_selectors_find_false_implies_dt_sel
    (s : native_String) (root : DatatypeDecl) (n : native_Nat)
    (target : Term) :
    ∀ (d : Datatype) (ci ai : native_Nat),
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (__eo_datatype_cons_selectors_rec s root n d ci ai) target) =
        Term.Boolean false ->
      ∃ j, target = Term.DtSel s root n j := by
  intro d ci ai h
  let selectors := __eo_datatype_cons_selectors_rec s root n d ci ai
  have hFindNe :
      __eo_list_find Term.__eo_List_cons selectors target ≠ Term.Stuck := by
    intro hFind
    rw [hFind] at h
    simp [__eo_is_neg] at h
  have hReqEq :=
    eo_requires_eq_result_of_ne_stuck_local
      (__eo_is_list Term.__eo_List_cons selectors) (Term.Boolean true)
      (__eo_list_find_rec selectors target (Term.Numeral 0)) hFindNe
  have hRecFalse :
      __eo_is_neg (__eo_list_find_rec selectors target (Term.Numeral 0)) =
        Term.Boolean false := by
    rw [← hReqEq]
    exact h
  exact
    datatype_cons_selectors_find_rec_false_implies_dt_sel
      s root n target (Term.Numeral 0) d ci ai
      (by simpa [selectors] using hRecFalse)

private theorem eo_dt_selectors_find_false_implies_matching
    (c target : Term) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons (__eo_dt_selectors c) target) =
      Term.Boolean false ->
    ∃ s d i j, target = Term.DtSel s d i j ∧ c = Term.DtCons s d i := by
  intro h
  cases c with
  | DtCons s d i =>
      rcases
        datatype_cons_selectors_find_false_implies_dt_sel
          s d i target (__eo_dd_resolve s d) i native_nat_zero
          (by simpa [__eo_dt_selectors] using h) with
        ⟨j, hTarget⟩
      exact ⟨s, d, i, j, hTarget, rfl⟩
  | _ =>
      exfalso
      simp [__eo_dt_selectors, __eo_dt_selectors_main, __eo_list_find,
        __eo_is_list,__eo_requires, __eo_is_neg,
        native_ite, native_teq] at h

private theorem dt_num_sels_pos_implies_lt_ctors :
    ∀ (d : SmtDatatype) (i : native_Nat),
      0 < __smtx_dt_num_sels d i ->
      i < smtDatatypeNumCtors d
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_dt_num_sels] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, h => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, h => by
      simp [smtDatatypeNumCtors]
  | SmtDatatype.sum c d, Nat.succ i, h => by
      have ih := dt_num_sels_pos_implies_lt_ctors d i
        (by simpa [__smtx_dt_num_sels] using h)
      simpa [smtDatatypeNumCtors] using Nat.succ_lt_succ ih

private theorem eo_mk_apply_of_ne_stuck_local
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem datatype_constructors_find_rec_self
    (s : native_String) (root : DatatypeDecl) :
    ∀ current start rel k,
      rel < smtDatatypeNumCtors (__eo_to_smt_datatype current) ->
      __eo_list_find_rec
        (__eo_datatype_constructors_rec s root current start)
        (Term.DtCons s root (start + rel)) (Term.Numeral k) =
        Term.Numeral (k + rel)
  | Datatype.null, start, rel, k, hlt => by
      simp [smtDatatypeNumCtors, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, k, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        eo_datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __eo_list_find_rec
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.DtCons s root (start + 0)) (Term.Numeral k) =
              Term.Numeral (k + 0)
          rw [eo_mk_apply_of_ne_stuck_local (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_eq, native_ite, native_teq]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtors (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtors, __eo_to_smt_datatype] using
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
          rw [eo_mk_apply_of_ne_stuck_local (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_add, __eo_eq, native_ite,
            native_teq, hIdxNe]
          simpa [native_zplus, Int.add_assoc, Int.add_comm, Int.add_left_comm]
            using ih

private theorem datatype_constructors_find_self
    (s : native_String) (root : DatatypeDecl) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtors (__eo_to_smt_datatype current)) :
    __eo_list_find Term.__eo_List_cons
      (__eo_datatype_constructors_rec s root current start)
      (Term.DtCons s root (start + rel)) =
      Term.Numeral rel := by
  have hList :
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start) =
        Term.Boolean true :=
    eo_is_list_datatype_constructors_rec s root current start
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
      rel < smtDatatypeNumCtors (__eo_to_smt_datatype current) ->
      __assoc_nil_nth Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start)
        (Term.Numeral rel) =
        Term.DtCons s root (start + rel)
  | Datatype.null, start, rel, hlt => by
      simp [smtDatatypeNumCtors, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        eo_datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __assoc_nil_nth Term.__eo_List_cons
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.Numeral 0) =
              Term.DtCons s root (start + 0)
          rw [eo_mk_apply_of_ne_stuck_local (by simp) hTailNe]
          simp [__assoc_nil_nth, __eo_eq, native_ite, native_teq]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtors (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtors, __eo_to_smt_datatype] using
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
          rw [eo_mk_apply_of_ne_stuck_local (by simp) hTailNe]
          rw [assoc_nil_nth_cons_succ (Term.DtCons s root start) tail rel]
          exact ih

private theorem assoc_nil_nth_datatype_constructors_find_self
    (s : native_String) (root : DatatypeDecl) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtors (__eo_to_smt_datatype current)) :
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
      i < smtDatatypeNumCtors
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

private theorem dt_updater_elim_update_rel
    (M : SmtModel) (hM : model_wf M)
    (sel t a c tu : Term) :
  __mk_dt_updater_elim_rhs
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a)
      c
      (__dt_get_selectors (__eo_typeof t) c) = tu ->
  RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t)) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a)))
    (__smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t))) := by
  intro hMk hBool
  let upd := Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a
  let rhs :=
    Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.UOp1 UserOp1.is c) t))
        tu)
      t
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type upd rhs
      (by simpa [upd, rhs] using hBool)
  have hLhsNN :
      __smtx_typeof (__eo_to_smt upd) ≠ SmtType.None :=
    hTypes.2
  have hRhsNN :
      __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
    rw [← hTypes.1]
    exact hTypes.2
  have hThenNN :
      __smtx_typeof (__eo_to_smt tu) ≠ SmtType.None := by
    change
      __smtx_typeof
        (SmtTerm.ite (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is c) t))
          (__eo_to_smt tu) (__eo_to_smt t)) ≠
        SmtType.None at hRhsNN
    exact smtx_ite_then_non_none _ _ _ hRhsNN
  have hTuNe : tu ≠ Term.Stuck := by
    intro hTu
    apply hThenNN
    rw [hTu]
    exact smtx_typeof_eo_to_smt_stuck_none
  by_cases hIsDtSel :
      ∃ s d i j, __eo_to_smt sel = SmtTerm.DtSel s d i j
  · rcases hIsDtSel with ⟨s, d, i, j, hSelSmt⟩
    have hUpdaterNN :
        __smtx_typeof
            (__eo_to_smt_updater (SmtTerm.DtSel s d i j)
              (__eo_to_smt t) (__eo_to_smt a)) ≠
          SmtType.None := by
      have h := hLhsNN
      change
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt sel)
              (__eo_to_smt t) (__eo_to_smt a)) ≠
          SmtType.None at h
      simpa [hSelSmt] using h
    have hIdx :
        native_zlt (native_nat_to_int j)
            (native_nat_to_int
              (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) =
          true :=
      TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
        s d i j (__eo_to_smt t) (__eo_to_smt a) hUpdaterNN
    rcases TranslationProofs.eo_to_smt_eq_dt_sel_cases
        sel s d i j hSelSmt with hDtSel | hPurify
    · rcases hDtSel with ⟨d0, hd, hSelEq, hReserved⟩
      subst sel
      subst d
      let D := __eo_to_smt_datatype_decl d0
      have hIdxProp :
          j <
            __smtx_dt_num_sels
              (__eo_to_smt_datatype (__eo_dd_lookup s d0)) i := by
        have hInt :
            (j : Int) <
              (__smtx_dt_num_sels
                (__eo_to_smt_datatype (__eo_dd_lookup s d0)) i : Int) := by
          apply of_decide_eq_true
          simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
            Smtm.native_nat_to_int, D,
            TranslationProofs.eo_to_smt_dd_lookup] using hIdx
        exact Int.ofNat_lt.mp hInt
      have hIteNN :
          term_has_non_none_type
            (SmtTerm.ite
              (SmtTerm.Apply
                (SmtTerm.DtTester s D i)
                (__eo_to_smt t))
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel s D i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s D) i)
                (__eo_to_smt t) (__eo_to_smt a)
                (SmtTerm.DtCons s D i))
              (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
      rcases ite_args_of_non_none hIteNN with
        ⟨_T, hCond, _hThen, _hElse, _hTNN⟩
      have hCondNN :
          term_has_non_none_type
            (SmtTerm.Apply
              (SmtTerm.DtTester s D i)
              (__eo_to_smt t)) := by
        unfold term_has_non_none_type
        rw [hCond]
        simp
      have hTType :
          __smtx_typeof (__eo_to_smt t) =
            SmtType.Datatype s D :=
        dt_tester_arg_datatype_of_non_none hCondNN
      have hTNN :
          __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
        rw [hTType]
        simp
      have hTypeSmt :
          __eo_to_smt_type (__eo_typeof t) =
            SmtType.Datatype s D := by
        exact (TranslationProofs.eo_to_smt_typeof_matches_translation t hTNN).symm.trans hTType
      rcases TranslationProofs.eo_to_smt_type_eq_datatype_non_tuple
          (TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved)
          hTypeSmt with
        ⟨dT, hType, hdT⟩
      have hdTEq : dT = d0 := by
        have hTypeEq :
            Term.DatatypeType s dT = Term.DatatypeType s d0 :=
          TranslationProofs.eo_to_smt_type_injective_of_wf
            (A := SmtType.Datatype s D)
            (by
              simp [__eo_to_smt_type, native_ite, hReserved, D, hdT])
            (by
              simp [__eo_to_smt_type, native_ite, hReserved, D])
            (Smtm.smt_datatype_wf_of_non_none_type
              (__eo_to_smt t) s D hTType)
        injection hTypeEq
      subst dT
      have hCondRhsNN :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is c) t)) ≠
            SmtType.None := by
        change
          __smtx_typeof
            (SmtTerm.ite (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is c) t))
              (__eo_to_smt tu) (__eo_to_smt t)) ≠
            SmtType.None at hRhsNN
        exact smtx_ite_cond_non_none _ _ _ hRhsNN
      rcases tester_ctor_translation_of_non_none c t hCondRhsNN with
        ⟨cs, cd, ci, hCTrans⟩
      rcases TranslationProofs.eo_to_smt_eq_dt_cons_cases
          c cs cd ci hCTrans with hDtCons | hTupleUnit
      · rcases hDtCons with ⟨dC, hdC, hCEq, _hCReserved⟩
        subst c
        subst cd
        let guard :=
          __eo_is_neg
            (__eo_list_find Term.__eo_List_cons
              (__eo_dt_selectors (Term.DtCons cs dC ci))
              (Term.DtSel s d0 i j))
        let bodyWithAssoc :=
          __dt_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.update
                (Term.DtSel s d0 i j)) t) a)
            (__eo_dt_selectors (Term.DtCons cs dC ci))
            (__assoc_nil_nth Term.__eo_List_cons
              (__eo_dt_constructors (Term.DatatypeType s d0))
              (__eo_list_find Term.__eo_List_cons
                (__dt_get_constructors (Term.DatatypeType s d0))
                (Term.DtCons cs dC ci)))
        have hSelectorsNe :
            __eo_dt_selectors (Term.DtCons cs dC ci) ≠ Term.Stuck := by
          intro hSelectors
          apply hTuNe
          rw [← hMk]
          simp [__mk_dt_updater_elim_rhs, __dt_get_selectors, hType,
            hSelectors]
        have hMkDefGuard :
            __mk_dt_updater_elim_rhs
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.update
                    (Term.DtSel s d0 i j)) t) a)
                (Term.DtCons cs dC ci)
                (__dt_get_selectors (__eo_typeof t)
                  (Term.DtCons cs dC ci)) =
              __eo_requires guard (Term.Boolean false) bodyWithAssoc := by
          simp [guard, bodyWithAssoc, __mk_dt_updater_elim_rhs,
            __dt_get_selectors, hType]
        have hReqNe :
            __eo_requires guard (Term.Boolean false) bodyWithAssoc ≠
              Term.Stuck := by
          rw [← hMkDefGuard, hMk]
          exact hTuNe
        have hGuard : guard = Term.Boolean false :=
          eo_requires_eq_of_ne_stuck_local guard (Term.Boolean false)
            bodyWithAssoc hReqNe
        rcases
            eo_dt_selectors_find_false_implies_matching
              (Term.DtCons cs dC ci) (Term.DtSel s d0 i j)
              (by simpa [guard] using hGuard) with
          ⟨ss, dd, ii, jj, hTarget, hCtor⟩
        cases hTarget
        cases hCtor
        have hCtorLt :
            i <
              smtDatatypeNumCtors
                (__eo_to_smt_datatype (__eo_dd_lookup s d0)) :=
          dt_num_sels_pos_implies_lt_ctors
            (__eo_to_smt_datatype (__eo_dd_lookup s d0)) i
              (Nat.zero_lt_of_lt hIdxProp)
        have hCtorAssoc :=
          assoc_nil_nth_dt_constructors_find_self s d0 i hCtorLt
        let selectors := __eo_dt_selectors (Term.DtCons s d0 i)
        let body :=
          __dt_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.update
                (Term.DtSel s d0 i j)) t) a)
            selectors (Term.DtCons s d0 i)
        have hMkDefMatching :
            __mk_dt_updater_elim_rhs
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.update
                    (Term.DtSel s d0 i j)) t) a)
                (Term.DtCons s d0 i)
                (__dt_get_selectors (__eo_typeof t)
                  (Term.DtCons s d0 i)) =
              __eo_requires
                (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons selectors
                    (Term.DtSel s d0 i j)))
                (Term.Boolean false) body := by
          simp [selectors, body, __mk_dt_updater_elim_rhs,
            __dt_get_selectors, hType, hCtorAssoc]
        have hReqNeMatching :
            __eo_requires
                (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons selectors
                    (Term.DtSel s d0 i j)))
                (Term.Boolean false) body ≠
              Term.Stuck := by
          rw [← hMkDefMatching, hMk]
          exact hTuNe
        have hBodyEq :
            __eo_requires
                (__eo_is_neg
                  (__eo_list_find Term.__eo_List_cons selectors
                    (Term.DtSel s d0 i j)))
                (Term.Boolean false) body =
              body :=
          eo_requires_eq_result_of_ne_stuck_local _ _ _ hReqNeMatching
        have hTuEq : tu = body := by
          rw [← hMk]
          rw [hMkDefMatching]
          exact hBodyEq
        have hBodyNN :
            __smtx_typeof (__eo_to_smt body) ≠ SmtType.None := by
          simpa [hTuEq] using hThenNN
        have hBodySmt :
            __eo_to_smt body =
              smtDtUpdaterElimRhsRec s d0 i j
                (__eo_to_smt t) (__eo_to_smt a)
                (__eo_dd_resolve s d0) i 0 (SmtTerm.DtCons s D i) := by
          have hRec :=
            eo_to_smt_dt_updater_elim_rhs_selectors s d0 i j t a
              (Term.DtCons s d0 i) hReserved
              (DtConsSpineRoot.root s d0 i)
              (__eo_dd_resolve s d0) i 0 hBodyNN
          simpa [body, selectors, __eo_dt_selectors, hReserved, D] using hRec
        have hTuSmt :
            __eo_to_smt tu =
              __eo_to_smt_updater_rec
                (SmtTerm.DtSel s D i j)
                (__smtx_dt_num_sels
                  (__eo_to_smt_datatype (__eo_dd_lookup s d0)) i)
                (__eo_to_smt t) (__eo_to_smt a)
                (SmtTerm.DtCons s D i) := by
          rw [hTuEq, hBodySmt]
          exact
            smtDtUpdaterElimRhsRec_self_eq_updater_rec
              s d0 i j (__eo_to_smt t) (__eo_to_smt a)
              (SmtTerm.DtCons s D i)
        have hSmtEq :
            __eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.update
                    (Term.DtSel s d0 i j)) t) a) =
              __eo_to_smt
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.ite)
                      (Term.Apply (Term.UOp1 UserOp1.is
                        (Term.DtCons s d0 i)) t))
                    tu)
                  t) := by
          change
            __eo_to_smt_updater
                (__eo_to_smt (Term.DtSel s d0 i j))
                (__eo_to_smt t) (__eo_to_smt a) =
              SmtTerm.ite
                (SmtTerm.Apply
                  (__eo_to_smt_tester
                    (__eo_to_smt (Term.DtCons s d0 i)))
                  (__eo_to_smt t))
                (__eo_to_smt tu) (__eo_to_smt t)
          rw [hSelSmt, hCTrans, hTuSmt]
          simp [__eo_to_smt_tester, __eo_to_smt_updater, native_ite, hIdx,
            D, TranslationProofs.eo_to_smt_dd_lookup]
        rw [hSmtEq]
        exact RuleProofs.smt_value_rel_refl _
      · rcases hTupleUnit with ⟨hcs, hcd, hci, hcEq⟩
        subst c
        subst cs
        subst cd
        subst ci
        have hTupleCondNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.DtTester (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
                  native_nat_zero)
                (__eo_to_smt t)) := by
          unfold term_has_non_none_type
          exact hCondRhsNN
        have hTupleTType :=
          dt_tester_arg_datatype_of_non_none hTupleCondNN
        rw [hTType] at hTupleTType
        have hsTuple : s = native_string_lit "@Tuple" := by
          injection hTupleTType
        exact False.elim
          ((TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved)
            hsTuple)
    · rcases hPurify with ⟨z0, hSelEq, _hz0⟩
      subst sel
      change SmtTerm._at_purify (__eo_to_smt z0) =
        SmtTerm.DtSel s d i j at hSelSmt
      cases hSelSmt
  · exfalso
    apply hLhsNN
    change
      __smtx_typeof
          (__eo_to_smt_updater (__eo_to_smt sel)
            (__eo_to_smt t) (__eo_to_smt a)) =
        SmtType.None
    exact
      eo_to_smt_updater_typeof_none_of_not_dt_sel
        (__eo_to_smt sel) (__eo_to_smt t) (__eo_to_smt a)
        (by
          intro s d i j hEq
          exact hIsDtSel ⟨s, d, i, j, hEq⟩)

private theorem dt_updater_elim_non_update_absurd
    (u t a c tu : Term) :
  (∀ sel, u ≠ Term.UOp1 UserOp1.update sel) ->
  __mk_dt_updater_elim_rhs
      (Term.Apply (Term.Apply u t) a)
      c
      (__dt_get_selectors (__eo_typeof t) c) = tu ->
  RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply u t) a))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.UOp1 UserOp1.is c) t))
            tu)
          t)) ->
  False := by
  intro hNotUpdate hMk hBool
  by_cases hTupleUpdate : ∃ idx, u = Term.UOp1 UserOp1.tuple_update idx
  · rcases hTupleUpdate with ⟨idx, hU⟩
    subst u
    by_cases hTupleCtor : c = Term.UOp UserOp.tuple
    · subst c
      exact
        (eq_rhs_ite_bad_tester_not_bool
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)
          (Term.UOp UserOp.tuple) t tu rfl) hBool
    · have hStuckRhs :
          __mk_dt_updater_elim_rhs
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)
              c (__dt_get_selectors (__eo_typeof t) c) =
            Term.Stuck :=
        mk_dt_updater_elim_rhs_tuple_update_stuck_of_ne_tuple
          idx t a c (__dt_get_selectors (__eo_typeof t) c) hTupleCtor
      rw [hStuckRhs] at hMk
      exact
        (eq_rhs_ite_stuck_subst_not_bool
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)
          c t tu hMk) hBool
  · have hStuckRhs :
        __mk_dt_updater_elim_rhs
            (Term.Apply (Term.Apply u t) a)
            c (__dt_get_selectors (__eo_typeof t) c) =
          Term.Stuck :=
      mk_dt_updater_elim_rhs_non_updater_stuck u t a c
        (__dt_get_selectors (__eo_typeof t) c)
        hNotUpdate
        (by
          intro idx hU
          exact hTupleUpdate ⟨idx, hU⟩)
    rw [hStuckRhs] at hMk
    exact
      (eq_rhs_ite_stuck_subst_not_bool
        (Term.Apply (Term.Apply u t) a) c t tu hMk) hBool

private theorem facts___eo_prog_dt_updater_elim_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_updater_elim a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_updater_elim a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_updater_elim a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_updater_elim_ne_stuck a1 hProg with
    ⟨u, t, a, c, tu, t2, t3, hA1Eq, hT2, hT3, hMk, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply u t) a))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.UOp1 UserOp1.is c) t))
              tu)
            t)) := by
    have hTy :
        __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply u t) a))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.UOp1 UserOp1.is c) t))
                tu)
              t)) =
          Term.Bool := by
      simpa [hProgEq] using hResultTy
    have hA1Trans' :
        RuleProofs.eo_has_smt_translation
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply u t) a))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.UOp1 UserOp1.is c) t))
                tu)
              t)) := by
      subst hA1Eq
      subst t2
      subst t3
      simpa using hA1Trans
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type _ hA1Trans' hTy
  rw [hProgEq]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · cases u with
    | UOp1 op sel =>
        cases op with
        | update =>
            exact dt_updater_elim_update_rel M hM sel t a c tu hMk hBool
        | _ =>
            exact False.elim
              (dt_updater_elim_non_update_absurd
                _ t a c tu
                (by intro sel' h; cases h)
                hMk hBool)
    | _ =>
        exact False.elim
          (dt_updater_elim_non_update_absurd _ t a c tu
            (by intro sel h; cases h)
            hMk hBool)

public theorem cmd_step_dt_updater_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_updater_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_updater_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_updater_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.dt_updater_elim args premises ≠
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
              have hA1TransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_updater_elim a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_updater_elim a1) true
                exact facts___eo_prog_dt_updater_elim_impl
                  M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_updater_elim a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_updater_elim a1)
                  (typed___eo_prog_dt_updater_elim_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
