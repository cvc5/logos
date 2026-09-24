module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
public import Cpc.Proofs.RuleSupport.DtCollapseSelectorSupport
import all Cpc.Proofs.RuleSupport.DtCollapseSelectorSupport
public import Cpc.Proofs.RuleSupport.DtCollapseTesterSupport
import all Cpc.Proofs.RuleSupport.DtCollapseTesterSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

attribute [local simp] native_ite native_teq native_not native_and native_zlt

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

private theorem eq_args_of_prog_dt_collapse_updater_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck ->
  ∃ t s,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s ∧
    __mk_dt_collapse_updater_rhs t = s ∧
    __eo_prog_dt_collapse_updater a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
                  have hReq :
                      __eo_requires (__mk_dt_collapse_updater_rhs lhs) rhs body ≠
                        Term.Stuck := by
                    simpa [__eo_prog_dt_collapse_updater, body] using hProg
                  have hGuard :
                      __mk_dt_collapse_updater_rhs lhs = rhs :=
                    eo_requires_eq_of_ne_stuck_local
                      (__mk_dt_collapse_updater_rhs lhs) rhs body hReq
                  have hProgEq :
                      __eo_prog_dt_collapse_updater body = body := by
                    simpa [__eo_prog_dt_collapse_updater, body] using
                      eo_requires_eq_result_of_ne_stuck_local
                        (__mk_dt_collapse_updater_rhs lhs) rhs body hReq
                  exact ⟨lhs, rhs, rfl, hGuard, hProgEq⟩
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

private theorem prog_dt_collapse_updater_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  __eo_prog_dt_collapse_updater a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_collapse_updater_ne_stuck a1 hProg with
    ⟨_t, _s, _hEq, _hGuard, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_collapse_updater_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_collapse_updater a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_collapse_updater a1 = a1 :=
    prog_dt_collapse_updater_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem eq_rhs_stuck_not_bool (lhs : Term) :
    ¬ RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) Term.Stuck) := by
  intro h
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      lhs Term.Stuck h
  have hNone : __smtx_typeof (__eo_to_smt lhs) = SmtType.None := by
    rw [hTypes.1]
    native_decide
  exact hTypes.2 hNone

private theorem eo_len_stuck_of_list_find_is_neg_bool
    (selectors sel : Term) (b : Bool) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons selectors sel) =
      Term.Boolean b ->
    __eo_len selectors = Term.Stuck := by
  intro h
  cases selectors <;>
    simp [__eo_list_find, __eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_requires, __eo_is_ok, __eo_is_neg, __eo_len, native_ite,
      native_teq, native_not, SmtEval.native_not] at h ⊢

private theorem dt_collapse_updater_rhs_index_stuck (t a : Term) :
    __dt_collapse_updater_rhs t a Term.Stuck = Term.Stuck := by
  cases t <;> cases a <;> simp [__dt_collapse_updater_rhs]

private theorem dt_collapse_updater_guard_true_of_rhs_non_stuck
    (sel t a rhs : Term) :
    (let selectors := __dt_get_selectors_of_app (__eo_typeof t) t
     let idx := __eo_list_find Term.__eo_List_cons selectors sel
     (if __eo_is_neg idx = Term.Boolean true then
        t
      else if __eo_is_neg idx = Term.Boolean false then
        __dt_collapse_updater_rhs t a
          (__eo_add (__eo_add (__eo_len selectors) idx)
            (Term.Numeral (-1 : native_Int)))
      else Term.Stuck) = rhs) ->
    rhs ≠ Term.Stuck ->
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__dt_get_selectors_of_app (__eo_typeof t) t) sel) =
      Term.Boolean true ∧ rhs = t := by
  intro hGuard hRhs
  let selectors := __dt_get_selectors_of_app (__eo_typeof t) t
  let idx := __eo_list_find Term.__eo_List_cons selectors sel
  cases hNeg : __eo_is_neg idx with
  | Boolean b =>
      cases b
      · exfalso
        have hLen : __eo_len selectors = Term.Stuck :=
          eo_len_stuck_of_list_find_is_neg_bool selectors sel false
            (by simpa [idx] using hNeg)
        have hCollapse :
            __dt_collapse_updater_rhs t a
                (__eo_add (__eo_add (__eo_len selectors) idx)
                  (Term.Numeral (-1 : native_Int))) =
              Term.Stuck := by
          rw [hLen]
          simp [__eo_add, dt_collapse_updater_rhs_index_stuck]
        apply hRhs
        simpa [selectors, idx, hNeg, hCollapse] using hGuard.symm
      · constructor
        · simp
        · simpa [selectors, idx, hNeg] using hGuard.symm
  | _ =>
      exfalso
      apply hRhs
      simpa [selectors, idx, hNeg] using hGuard.symm

private theorem smt_model_eval_ne_notvalue_of_non_none
    (M : SmtModel) (hM : model_wf M) (x : SmtTerm) :
    __smtx_typeof x ≠ SmtType.None ->
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  intro hNN hEval
  have hPres := smt_model_eval_preserves_type_of_non_none M hM x hNN
  have hNone : __smtx_typeof_value (__smtx_model_eval M x) = SmtType.None := by
    simp [hEval, __smtx_typeof_value]
  rw [hPres] at hNone
  exact hNN hNone

private theorem eo_to_smt_updater_typeof_none_of_not_dt_sel
    (sel t u : SmtTerm) :
    (∀ s d i j, sel ≠ SmtTerm.DtSel s d i j) ->
    __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None := by
  intro hSel
  cases sel <;> simp [__eo_to_smt_updater]
  case DtSel s d i j =>
    exact False.elim (hSel s d i j rfl)

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
            simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, hCountFG,
              Smtm.native_nateq] using hLast
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
                Smtm.native_nateq, hNeF, hNeG] using hArg
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

private theorem smtx_model_eval_apply_of_dt_chain
    (M : SmtModel) (v x : SmtValue)
    (hHead : ∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i)
    (hx : x ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M v x = SmtValue.Apply v x := by
  cases x <;> simp [__smtx_model_eval_apply] at hx ⊢
  all_goals
    cases v <;> simp [__smtx_apply_head_value] at hHead ⊢

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

private theorem smtx_apply_arg_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f with
    | DtSel s d i j =>
        exact False.elim (hSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hTester s d i rfl)
    | _ =>
        simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, _B, _hHead, hArg, hA, _hB⟩
  rw [hArg]
  exact hA

private theorem smtx_apply_head_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f with
    | DtSel s d i j =>
        exact False.elim (hSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hTester s d i rfl)
    | _ =>
        simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem eo_to_smt_updater_rec_ne_dt_sel_local
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat)
    (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 j0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtSel s0 d0 i0 j0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccSel s0 d0 i0 j0 h
  | succ _ =>
      cases h

private theorem eo_to_smt_updater_rec_ne_dt_tester_local
    (s : native_String) (d : SmtDatatypeDecl) (i j n : native_Nat)
    (t u acc : SmtTerm)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (s0 : native_String) (d0 : SmtDatatypeDecl) (i0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtTester s0 d0 i0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccTester s0 d0 i0 h
  | succ _ =>
      cases h

private theorem smtx_model_eval_apply_eq_apply_of_not_dt_ops
    (M : SmtModel) (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f with
  | DtSel s d i j => exact False.elim (hSel s d i j rfl)
  | DtTester s d i => exact False.elim (hTester s d i rfl)
  | _ => simp [__smtx_model_eval]

private theorem updater_rec_eval_components
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (d : SmtDatatypeDecl) (i m n : native_Nat)
    (t u : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
          (SmtTerm.DtCons s d i)) ≠
      SmtType.None ->
    __smtx_apply_head_value
        (__smtx_model_eval M
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
            (SmtTerm.DtCons s d i))) =
        SmtValue.DtCons s d i ∧
      vsm_num_apply_args
          (__smtx_model_eval M
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
              (SmtTerm.DtCons s d i))) =
        n ∧
      ∀ q, q < n ->
        __smtx_apply_arg_nth_value
            (__smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
                (SmtTerm.DtCons s d i)))
            q n =
          __smtx_model_eval M
            (native_ite (native_nateq m q) u
              (SmtTerm.Apply (SmtTerm.DtSel s d i q) t)) := by
  induction n with
  | zero =>
      intro _hNN
      constructor
      · simp [__eo_to_smt_updater_rec, __smtx_model_eval, __smtx_apply_head_value]
      constructor
      · simp [__eo_to_smt_updater_rec, __smtx_model_eval, vsm_num_apply_args]
      · intro q hq
        exact False.elim (Nat.not_lt_zero q hq)
  | succ k ih =>
      intro hNN
      let recTerm :=
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) k t u
          (SmtTerm.DtCons s d i)
      let argTerm :=
        native_ite (native_nateq m k) u
          (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)
      have hTermNN :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) ≠ SmtType.None := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hNN
      have hRecSel :
          ∀ s0 d0 i0 j0, recTerm ≠ SmtTerm.DtSel s0 d0 i0 j0 :=
        eo_to_smt_updater_rec_ne_dt_sel_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 j0 h; cases h)
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 :=
        eo_to_smt_updater_rec_ne_dt_tester_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 h; cases h)
      have hRecNN : __smtx_typeof recTerm ≠ SmtType.None :=
        smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      have hArgNN : __smtx_typeof argTerm ≠ SmtType.None :=
        smtx_apply_arg_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      rcases ih hRecNN with ⟨hHeadRec, hCountRec, hArgsRec⟩
      have hArgNot :
          __smtx_model_eval M argTerm ≠ SmtValue.NotValue :=
        smt_model_eval_ne_notvalue_of_non_none M hM argTerm hArgNN
      have hEvalApply :
          __smtx_model_eval M (SmtTerm.Apply recTerm argTerm) =
            SmtValue.Apply (__smtx_model_eval M recTerm)
              (__smtx_model_eval M argTerm) := by
        rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops
          M recTerm argTerm hRecSel hRecTester]
        rw [smtx_model_eval_apply_of_dt_chain M
          (__smtx_model_eval M recTerm) (__smtx_model_eval M argTerm)
          ⟨s, d, i, hHeadRec⟩ hArgNot]
      have hEval :
          __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) (Nat.succ k)
                t u (SmtTerm.DtCons s d i)) =
            SmtValue.Apply (__smtx_model_eval M recTerm)
              (__smtx_model_eval M argTerm) := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hEvalApply
      constructor
      · rw [hEval]
        simpa [__smtx_apply_head_value] using hHeadRec
      constructor
      · rw [hEval]
        simp [vsm_num_apply_args]
        simpa [recTerm] using hCountRec
      · intro q hq
        by_cases hLast : q = k
        · subst q
          have hEqBool : native_nateq k k = true := by
            simp [native_nateq, Smtm.native_nateq]
          rw [hEval]
          simp [__smtx_apply_arg_nth_value,hEqBool, argTerm]
        · have hqk : q < k := by
            exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hq) hLast
          have hNeBool : native_nateq q k = false := by
            simp [native_nateq, Smtm.native_nateq, hLast]
          rw [hEval]
          simp [__smtx_apply_arg_nth_value,hNeBool]
          exact hArgsRec q hqk

private theorem tuple_update_shape_of_non_none
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (n : native_Int),
      __smtx_typeof (__eo_to_smt t) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl d) ∧
        idx = Term.Numeral n ∧
        0 ≤ n ∧
        native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero := by
  intro hNN
  change
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
            (__eo_to_smt idx) (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None at hNN
  cases hTy : __smtx_typeof (__eo_to_smt t) with
  | Datatype s d =>
      cases hIdx : __eo_to_smt idx with
      | Numeral n =>
          by_cases hs : s = native_string_lit "@Tuple"
          · subst s
            have hDecl :
                ∃ body, d = __eo_to_smt_tuple_decl body := by
              cases d with
              | nil =>
                  exfalso
                  apply hNN
                  simp [__eo_to_smt_tuple_update, hTy, hIdx]
              | cons s2 body rest =>
                  cases rest with
                  | cons s3 body3 rest3 =>
                      exfalso
                      apply hNN
                      simp [__eo_to_smt_tuple_update, hTy, hIdx]
                  | nil =>
                      by_cases hs2 : s2 = native_string_lit "@Tuple"
                      · subst s2
                        exact ⟨body, rfl⟩
                      · exfalso
                        apply hNN
                        simp [__eo_to_smt_tuple_update, hTy, hIdx, hs2,
                          native_streq, native_and, native_ite]
            rcases hDecl with ⟨body, rfl⟩
            have hGe : native_zleq 0 n = true := by
              cases hTest : native_zleq 0 n
              · simp [__eo_to_smt_tuple_update, hTy, hIdx, hTest,
                  __eo_to_smt_tuple_decl, native_streq, native_and,
                  native_ite] at hNN
              · rfl
            have hUpdaterNN :
                __smtx_typeof
                    (__eo_to_smt_updater
                      (SmtTerm.DtSel (native_string_lit "@Tuple")
                        (__eo_to_smt_tuple_decl body)
                        native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt t) (__eo_to_smt a)) ≠
                  SmtType.None := by
              simpa [__eo_to_smt_tuple_update, hTy, hIdx, hGe,
                __eo_to_smt_tuple_decl, native_streq, native_and,
                native_ite] using hNN
            have hIdxBoundBool :
                native_zlt
                    (native_nat_to_int (native_int_to_nat n))
                    (native_nat_to_int
                      (__smtx_dt_num_sels body native_nat_zero)) =
                  true :=
              TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
                (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl body) native_nat_zero
                (native_int_to_nat n) (__eo_to_smt t) (__eo_to_smt a)
                hUpdaterNN
            have hIdxEq : idx = Term.Numeral n :=
              TranslationProofs.eo_to_smt_eq_numeral idx n hIdx
            have hNonneg : 0 ≤ n := by
              simpa [native_zleq, SmtEval.native_zleq] using hGe
            have hLt : native_int_to_nat n <
                __smtx_dt_num_sels body native_nat_zero := by
              have hInt :
                  (native_int_to_nat n : Int) <
                    (__smtx_dt_num_sels body native_nat_zero : Int) := by
                apply of_decide_eq_true
                simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
                  Smtm.native_nat_to_int] using hIdxBoundBool
              exact Int.ofNat_lt.mp hInt
            exact ⟨body, n, rfl, hIdxEq, hNonneg, hLt⟩
          · exfalso
            apply hNN
            cases d with
            | nil =>
                simp [__eo_to_smt_tuple_update, hTy, hIdx]
            | cons s2 body rest =>
                cases rest <;>
                  simp [__eo_to_smt_tuple_update, hTy, hIdx, hs,
                    native_streq, native_and, native_ite]
      | _ =>
          exfalso
          apply hNN
          simp [__eo_to_smt_tuple_update, hTy, hIdx]
  | _ =>
      exfalso
      apply hNN
      simp [__eo_to_smt_tuple_update, hTy]

private theorem tuple_update_rec_non_none_of_shape
    (idx t a : Term) (d : SmtDatatype) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl d) native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
          (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl d) native_nat_zero)) ≠
      SmtType.None := by
  intro hT hIdx hNonneg hLt hNN
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels d native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hUpdaterNN :
      __smtx_typeof
          (__eo_to_smt_updater
            (SmtTerm.DtSel (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl d) native_nat_zero
              (native_int_to_nat n))
            (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None := by
    change
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
              (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) ≠
          SmtType.None at hNN
    simpa [__eo_to_smt_tuple_update, hT, hGe, native_streq,
      native_and, native_ite, __eo_to_smt_tuple_decl] using hNN
  have hIteNN :
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.Apply
              (SmtTerm.DtTester (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl d) native_nat_zero)
              (__eo_to_smt t))
            (__eo_to_smt_updater_rec
              (SmtTerm.DtSel (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl d) native_nat_zero
                (native_int_to_nat n))
              (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
              (__eo_to_smt a)
              (SmtTerm.DtCons (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl d) native_nat_zero))
            (__eo_to_smt t)) ≠
        SmtType.None := by
    simpa [__eo_to_smt_updater, native_ite, hIdxBool, native_zlt,
      SmtEval.native_zlt, native_nat_to_int, Smtm.native_nat_to_int,
      hIdxProp, __eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
      SmtEval.native_streq] using hUpdaterNN
  exact smtx_ite_then_non_none _ _ _ hIteNN

private theorem tuple_value_count_of_type_local
    {v : SmtValue} {c : SmtDatatypeCons}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)))
    (hHead :
      __smtx_apply_head_value v =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero) :
    vsm_num_apply_args v =
      __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero := by
  have hCount :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  simpa [__eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
    SmtEval.native_streq, native_ite, dt_num_sels_resolve] using hCount

private theorem tuple_update_eval_eq_rec_of_tuple_type
    (M : SmtModel) (hM : model_wf M)
    (idx t a : Term) (c : SmtDatatypeCons) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n <
      __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_model_eval M
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)
          (__eo_to_smt t) (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero)) := by
  intro hT hIdx hNonneg hLt
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int
            (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hIdxLt :
      native_nat_to_int (native_int_to_nat n) <
        native_nat_to_int
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero) := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hIdxProp
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hT]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hTNN,
      hT]
  have hHead :
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero :=
    tuple_datatype_value_head_zero hEvalTy
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
          (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) =
      __smtx_model_eval M
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)
          (__eo_to_smt t) (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero))
  rw [hT]
  simp [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
    native_and, hGe,hIdxLt, native_streq, __smtx_model_eval,
    __smtx_model_eval_dt_tester, hHead, native_veq,
    __smtx_model_eval_ite, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
    SmtEval.native_streq]

private theorem tuple_update_type_eq_tuple_type_of_shape
    (idx t a : Term) (d : SmtDatatype) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) := by
  intro hT hIdx hNonneg hLt hNN
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels d native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hIdxLt :
      native_nat_to_int (native_int_to_nat n) <
        native_nat_to_int (__smtx_dt_num_sels d native_nat_zero) := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hIdxProp
  have hRecNN :=
    tuple_update_rec_non_none_of_shape (Term.Numeral n) t a d n
      hT rfl hNonneg hLt hNN
  let recTerm :=
    __eo_to_smt_updater_rec
      (SmtTerm.DtSel (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) native_nat_zero
        (native_int_to_nat n))
      (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
      (__eo_to_smt a)
      (SmtTerm.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) native_nat_zero)
  have hRecTyRaw :
      __smtx_typeof recTerm =
        dt_cons_applied_type_rec (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d)
          (__smtx_dt_resolve d (__eo_to_smt_tuple_decl d))
          native_nat_zero (__smtx_dt_num_sels d native_nat_zero) := by
    have hsimpa :=
      TranslationProofs.eo_to_smt_updater_rec_type_of_non_none
        (native_string_lit "@Tuple") (__eo_to_smt_tuple_decl d)
        native_nat_zero (native_int_to_nat n)
        (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t) (__eo_to_smt a)
        hRecNN
    try simp [recTerm] at hsimpa ⊢
    exact hsimpa
  have hNumResolve :
      __smtx_dt_num_sels
          (__smtx_dt_resolve d (__eo_to_smt_tuple_decl d))
          native_nat_zero =
        __smtx_dt_num_sels d native_nat_zero :=
    dt_num_sels_resolve (__eo_to_smt_tuple_decl d) d native_nat_zero
  have hFullNN :
      dt_cons_applied_type_rec (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d)
          (__smtx_dt_resolve d (__eo_to_smt_tuple_decl d))
          native_nat_zero
          (__smtx_dt_num_sels
            (__smtx_dt_resolve d (__eo_to_smt_tuple_decl d))
            native_nat_zero) ≠
        SmtType.None := by
    rw [hNumResolve]
    rw [← hRecTyRaw]
    exact hRecNN
  have hRecTy :
      __smtx_typeof recTerm =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) := by
    rw [hRecTyRaw]
    rw [← hNumResolve]
    exact
      dt_cons_applied_type_rec_full_arity (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d)
        (__smtx_dt_resolve d (__eo_to_smt_tuple_decl d))
        native_nat_zero hFullNN
  let cond :=
    SmtTerm.Apply
      (SmtTerm.DtTester (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d) native_nat_zero)
      (__eo_to_smt t)
  have hIteNN :
      __smtx_typeof (SmtTerm.ite cond recTerm (__eo_to_smt t)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
            (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None at hNN
    rw [hT] at hNN
    simpa [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
      native_and, hGe, hIdxBool, hIdxLt, native_streq, cond, recTerm,
      __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      SmtEval.native_streq] using hNN
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hTNN⟩
  have hTEq : T = SmtType.Datatype (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl d) := by
    exact hElse.symm.trans hT
  have hIteTy :
      __smtx_typeof (SmtTerm.ite cond recTerm (__eo_to_smt t)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) := by
    rw [typeof_ite_eq, hCond, hThen, hElse, hTEq]
    simp [__smtx_typeof_ite, native_Teq]
  change
    __smtx_typeof
        (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
          (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl d)
  rw [hT]
  simpa [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
    native_and, hGe, hIdxLt, native_streq, cond, recTerm,
    __eo_to_smt_tuple_decl, __smtx_dd_lookup,
    SmtEval.native_streq] using hIteTy

private theorem tuple_collapse_updater_rhs_ne_stuck_shape
    (t a idx : Term) :
    __tuple_collapse_updater_rhs t a idx ≠ Term.Stuck ->
    t = Term.UOp UserOp.tuple_unit ∨
      ∃ head tail,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail := by
  intro h
  have hA : a ≠ Term.Stuck := by
    intro hStuck
    apply h
    simp [__tuple_collapse_updater_rhs, hStuck]
  have hIdx : idx ≠ Term.Stuck := by
    intro hStuck
    apply h
    simp [__tuple_collapse_updater_rhs, hStuck]
  cases t with
  | UOp op =>
      cases op with
      | tuple_unit =>
          left
          rfl
      | _ =>
          exfalso
          apply h
          simp [__tuple_collapse_updater_rhs]
  | Apply f tail =>
      cases f with
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op with
              | tuple =>
                  right
                  exact ⟨head, tail, rfl⟩
              | _ =>
                  exfalso
                  apply h
                  simp [__tuple_collapse_updater_rhs]
          | _ =>
              exfalso
              apply h
              simp [__tuple_collapse_updater_rhs]
      | _ =>
          exfalso
          apply h
          simp [__tuple_collapse_updater_rhs]
  | _ =>
      exfalso
      apply h
      simp [__tuple_collapse_updater_rhs]

private theorem tuple_collapse_updater_rhs_tuple_nonzero_eq_mk_apply
    (head tail a : Term) (n : native_Int) :
    n ≠ 0 ->
    a ≠ Term.Stuck ->
    __tuple_collapse_updater_rhs
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail) a
        (Term.Numeral n) =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) head)
        (__tuple_collapse_updater_rhs tail a
          (Term.Numeral (native_zplus n (-1 : native_Int)))) := by
  intro hn0 hANe
  have hNumNe : Term.Numeral n ≠ Term.Numeral 0 := by
    intro h
    injection h with hn
    exact hn0 hn
  cases a <;>
    simp [__tuple_collapse_updater_rhs, __eo_add, native_zplus,
      SmtEval.native_zplus] at hANe ⊢

private theorem eo_mk_apply_tuple_head_eq_apply_of_arg_ne_stuck
    (head arg : Term) :
    arg ≠ Term.Stuck ->
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) head) arg =
      Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) arg := by
  intro hArg
  cases arg
  case Stuck => exact False.elim (hArg rfl)
  all_goals simp [__eo_mk_apply]

private theorem native_zplus_pred_nonneg_of_nonneg_ne_zero
    (n : native_Int) :
    0 ≤ n ->
    n ≠ 0 ->
    0 ≤ native_zplus n (-1 : native_Int) := by
  intro hNonneg hn0
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact False.elim (hn0 rfl)
      | succ k =>
          change (0 : Int) ≤ (k : Int) + 1 + -1
          omega
  | negSucc k =>
      simp at hNonneg

private theorem native_int_to_nat_eq_succ_pred_of_nonneg_ne_zero
    (n : native_Int) :
    0 ≤ n ->
    n ≠ 0 ->
    native_int_to_nat n =
      Nat.succ (native_int_to_nat (native_zplus n (-1 : native_Int))) := by
  intro hNonneg hn0
  cases n with
  | ofNat k =>
      cases k with
      | zero => exact False.elim (hn0 rfl)
      | succ k =>
          change Nat.succ k =
            Nat.succ (Int.toNat ((k : Int) + 1 + -1))
          congr
          omega
  | negSucc k =>
      simp at hNonneg

private theorem tuple_collapse_updater_rhs_projection
    (M : SmtModel) (hM : model_wf M)
    (idx t a : Term) (d : SmtDatatype) (n : native_Int)
    (k : native_Nat) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) ->
    k < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_apply_arg_nth_value
        (__smtx_model_eval M
          (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)))
        k (__smtx_dt_num_sels d native_nat_zero) =
      __smtx_model_eval M
        (native_ite (native_nateq (native_int_to_nat n) k)
          (__eo_to_smt a)
          (SmtTerm.Apply
            (SmtTerm.DtSel (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl d) native_nat_zero k)
            (__eo_to_smt t))) := by
  intro hT hIdx hNonneg hLt hRhsTy hk
  subst idx
  have hRhsNN :
      __smtx_typeof
          (__eo_to_smt
            (__tuple_collapse_updater_rhs t a (Term.Numeral n))) ≠
        SmtType.None := by
    rw [hRhsTy]
    simp
  have hRhsTermNN :
      __tuple_collapse_updater_rhs t a (Term.Numeral n) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation
      (__tuple_collapse_updater_rhs t a (Term.Numeral n)) hRhsNN
  rcases tuple_collapse_updater_rhs_ne_stuck_shape t a (Term.Numeral n)
      hRhsTermNN with hUnit | hTuple
  · subst t
    change
      __smtx_typeof
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl d) at hT
    unfold __eo_to_smt_tuple_decl at hT
    rw [TranslationProofs.smtx_typeof_tuple_unit_translation] at hT
    injection hT with _ hD
    have hDBody :
        SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null = d := by
      simpa [__eo_to_smt_tuple_decl] using hD
    subst d
    simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hLt
  · rcases hTuple with ⟨head, tail, hTupleEq⟩
    subst t
    let tupleTerm := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail
    let headSmt := __eo_to_smt head
    let tailSmt := __eo_to_smt tail
    let aSmt := __eo_to_smt a
    let headTy := __smtx_typeof headSmt
    have hTupleNN : __smtx_typeof (__eo_to_smt tupleTerm) ≠ SmtType.None := by
      rw [hT]
      simp
    rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
        tail head hTupleNN with
      ⟨c, hTailTy⟩
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let fullC := SmtDatatypeCons.cons headTy c
    let fullD := SmtDatatype.sum fullC SmtDatatype.null
    have hTupleTyFull :
        __smtx_typeof (__eo_to_smt tupleTerm) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) := by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD)
      exact
        TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
          tailSmt headSmt headTy c
          (by simpa [tailSmt, tailD] using hTailTy)
          (by
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                SmtType.None
            have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
    have hD : d = fullD := by
      rw [hT] at hTupleTyFull
      injection hTupleTyFull with _ hD'
      simpa [__eo_to_smt_tuple_decl] using hD'
    subst d
    by_cases hn0 : n = 0
    · subst n
      have hANe : a ≠ Term.Stuck := by
        intro hA
        apply hRhsTermNN
        simp [__tuple_collapse_updater_rhs, hA]
      have hRhsEq :
          __tuple_collapse_updater_rhs tupleTerm a (Term.Numeral 0) =
            Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail := by
        cases a <;> simp [tupleTerm, __tuple_collapse_updater_rhs] at hANe ⊢
      have hRhsBaseNN :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) ≠
            SmtType.None := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hRhsNN
      have hRhsPrependTyBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum
                  (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                  SmtDatatype.null)) := by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt) tailSmt) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum
                  (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                  SmtDatatype.null))
        exact
          TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
            tailSmt aSmt (__smtx_typeof aSmt) c
            (by simpa [tailSmt, tailD] using hTailTy)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                      tailSmt) ≠ SmtType.None
              have hsimpa := hRhsBaseNN; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
      have hFullArgEq :
          SmtDatatype.sum (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
              SmtDatatype.null =
            fullD := by
        have hRhsTyBase :
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
              SmtType.Datatype (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl fullD) := by
          rw [← hRhsEq]
          simpa [tupleTerm] using hRhsTy
        have h := hRhsPrependTyBase.symm.trans hRhsTyBase
        injection h with _ hD'
        simpa [__eo_to_smt_tuple_decl] using hD'
      rw [hRhsEq]
      cases k with
      | zero =>
          have hProj :=
            tuple_prepend_zero_projection M hM aSmt tailSmt
              (__smtx_typeof aSmt) c
              (by simpa [tailSmt, tailD] using hTailTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                        tailSmt) ≠ SmtType.None
                have hsimpa := hRhsBaseNN; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
          have hsimpa := hProj
          try simp [fullD, fullC, aSmt, native_nateq, Smtm.native_nateq] at hsimpa ⊢
          exact hsimpa
      | succ j =>
          have hjTail :
              j < __smtx_dt_num_sels tailD native_nat_zero := by
            simpa [fullD, fullC, tailD, __smtx_dt_num_sels,
              __smtx_dtc_num_sels] using hk
          have hRhsSucc :=
            tuple_prepend_succ_projection M hM aSmt tailSmt
              (__smtx_typeof aSmt) c j
              (by simpa [tailSmt, tailD] using hTailTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                        tailSmt) ≠ SmtType.None
                have hsimpa := hRhsBaseNN; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
              (by simpa [tailD] using hjTail)
          have hSelEval :
              __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl fullD)
                      native_nat_zero (Nat.succ j))
                    (__eo_to_smt tupleTerm)) =
                __smtx_apply_arg_nth_value
                  (__smtx_model_eval M (__eo_to_smt tupleTerm))
                  (Nat.succ j)
                  (__smtx_dt_num_sels fullD native_nat_zero) := by
            simpa [fullD, tupleTerm] using
              smt_tuple_dt_sel_eval_uses_constructor M hM
                (__eo_to_smt tupleTerm) fullC (Nat.succ j)
                (by simpa [fullD] using hTupleTyFull)
          have hOrigSucc :=
            tuple_prepend_succ_projection M hM headSmt tailSmt headTy c j
              (by simpa [tailSmt, tailD] using hTailTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                    SmtType.None
                have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
              (by simpa [tailD] using hjTail)
          have hRhsSucc' :
              __smtx_apply_arg_nth_value
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a)
                        tail)))
                  (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                __smtx_apply_arg_nth_value (__smtx_model_eval M tailSmt) j
                  (__smtx_dt_num_sels tailD native_nat_zero) := by
            have hsimpa := hRhsSucc
            try simp [aSmt, tailSmt, tailD, hFullArgEq] at hsimpa ⊢
            exact hsimpa
          rw [hRhsSucc']
          have hsimpa :=
            (hSelEval.trans hOrigSucc).symm
          try simp [fullD, fullC, native_nateq, Smtm.native_nateq] at hsimpa ⊢
          exact hsimpa
    · let pred := native_zplus n (-1 : native_Int)
      let tailRhs := __tuple_collapse_updater_rhs tail a (Term.Numeral pred)
      have hPredNonneg : 0 ≤ pred :=
        native_zplus_pred_nonneg_of_nonneg_ne_zero n hNonneg hn0
      have hNatSucc :
          native_int_to_nat n = Nat.succ (native_int_to_nat pred) :=
        native_int_to_nat_eq_succ_pred_of_nonneg_ne_zero n hNonneg hn0
      have hPredLt :
          native_int_to_nat pred <
            __smtx_dt_num_sels tailD native_nat_zero := by
        have hSuccLt :
            Nat.succ (native_int_to_nat pred) <
              Nat.succ (__smtx_dt_num_sels tailD native_nat_zero) := by
          simpa [hNatSucc, fullD, fullC, tailD, __smtx_dt_num_sels,
            __smtx_dtc_num_sels] using hLt
        exact Nat.lt_of_succ_lt_succ hSuccLt
      have hANe : a ≠ Term.Stuck := by
        intro hA
        apply hRhsTermNN
        simp [__tuple_collapse_updater_rhs, hA]
      have hStep :
          __tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n) =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) head) tailRhs := by
        simpa [pred, tailRhs] using
          tuple_collapse_updater_rhs_tuple_nonzero_eq_mk_apply
            head tail a n hn0 hANe
      have hTailRhsTermNN : tailRhs ≠ Term.Stuck := by
        intro hTail
        apply hRhsTermNN
        rw [hStep]
        simp [__eo_mk_apply, hTail]
      have hRhsEq :
          __tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n) =
            Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tailRhs := by
        rw [hStep]
        exact eo_mk_apply_tuple_head_eq_apply_of_arg_ne_stuck head tailRhs
          hTailRhsTermNN
      have hRhsPrependNN :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head)
                  tailRhs)) ≠
            SmtType.None := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hRhsNN
      rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
          tailRhs head hRhsPrependNN with
        ⟨cRhs, hTailRhsTyRaw⟩
      let tailRhsD := SmtDatatype.sum cRhs SmtDatatype.null
      have hRhsTyBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head)
                  tailRhs)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hRhsTy
      have hRhsPrependTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head)
                  tailRhs)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum (SmtDatatypeCons.cons headTy cRhs)
                  SmtDatatype.null)) := by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_prepend headSmt headTy (__eo_to_smt tailRhs)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum (SmtDatatypeCons.cons headTy cRhs)
                  SmtDatatype.null))
        exact
          TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
            (__eo_to_smt tailRhs) headSmt headTy cRhs
            (by simpa [tailRhsD] using hTailRhsTyRaw)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_prepend headSmt headTy
                      (__eo_to_smt tailRhs)) ≠ SmtType.None
              have hsimpa := hRhsPrependNN; (try simp [headSmt] at hsimpa ⊢); exact hsimpa)
      have hCRhs : cRhs = c := by
        have h := hRhsPrependTy.symm.trans hRhsTyBase
        injection h with _ hD'
        simp [fullD, fullC, __eo_to_smt_tuple_decl] at hD'
        exact hD'
      subst cRhs
      have hTailRhsTy :
          __smtx_typeof (__eo_to_smt tailRhs) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl tailD) := by
        simpa [tailD] using hTailRhsTyRaw
      rw [hRhsEq]
      cases k with
      | zero =>
          have hRhsZero :=
            tuple_prepend_zero_projection M hM headSmt (__eo_to_smt tailRhs)
              headTy c
              (by simpa [tailD] using hTailRhsTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend headSmt headTy
                        (__eo_to_smt tailRhs)) ≠ SmtType.None
                have hsimpa := hRhsPrependNN; (try simp [headSmt] at hsimpa ⊢); exact hsimpa)
          have hSelEval :
              __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl fullD)
                      native_nat_zero native_nat_zero)
                    (__eo_to_smt tupleTerm)) =
                __smtx_apply_arg_nth_value
                  (__smtx_model_eval M (__eo_to_smt tupleTerm))
                  native_nat_zero
                  (__smtx_dt_num_sels fullD native_nat_zero) := by
            simpa [fullD, tupleTerm] using
              smt_tuple_dt_sel_eval_uses_constructor M hM
                (__eo_to_smt tupleTerm) fullC native_nat_zero
                (by simpa [fullD] using hTupleTyFull)
          have hOrigZero :=
            tuple_prepend_zero_projection M hM headSmt tailSmt headTy c
              (by simpa [tailSmt, tailD] using hTailTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                    SmtType.None
                have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
          have hRhsZero' :
              __smtx_apply_arg_nth_value
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head)
                        tailRhs)))
                  native_nat_zero
                  (__smtx_dt_num_sels fullD native_nat_zero) =
                __smtx_model_eval M headSmt := by
            have hsimpa := hRhsZero
            try simp [headSmt, fullD, fullC] at hsimpa ⊢
            exact hsimpa
          rw [hRhsZero']
          simpa [fullD, fullC, hNatSucc, native_nateq,
            Smtm.native_nateq] using
            (hSelEval.trans hOrigZero).symm
      | succ j =>
          have hjTail :
              j < __smtx_dt_num_sels tailD native_nat_zero := by
            simpa [fullD, fullC, tailD, __smtx_dt_num_sels,
              __smtx_dtc_num_sels] using hk
          have hRhsSucc :=
            tuple_prepend_succ_projection M hM headSmt (__eo_to_smt tailRhs)
              headTy c j
              (by simpa [tailD] using hTailRhsTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend headSmt headTy
                        (__eo_to_smt tailRhs)) ≠ SmtType.None
                have hsimpa := hRhsPrependNN; (try simp [headSmt] at hsimpa ⊢); exact hsimpa)
              (by simpa [tailD] using hjTail)
          have hRecProj :=
            tuple_collapse_updater_rhs_projection M hM
              (Term.Numeral pred) tail a tailD pred j
              (by simpa [tailSmt, tailD] using hTailTy)
              rfl hPredNonneg hPredLt
              (by simpa [tailRhs, tailD] using hTailRhsTy)
              (by simpa [tailD] using hjTail)
          have hFullSelEval :
              __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl fullD)
                      native_nat_zero (Nat.succ j))
                    (__eo_to_smt tupleTerm)) =
                __smtx_apply_arg_nth_value
                  (__smtx_model_eval M (__eo_to_smt tupleTerm))
                  (Nat.succ j)
                  (__smtx_dt_num_sels fullD native_nat_zero) := by
            simpa [fullD, tupleTerm] using
              smt_tuple_dt_sel_eval_uses_constructor M hM
                (__eo_to_smt tupleTerm) fullC (Nat.succ j)
                (by simpa [fullD] using hTupleTyFull)
          have hOrigSucc :=
            tuple_prepend_succ_projection M hM headSmt tailSmt headTy c j
              (by simpa [tailSmt, tailD] using hTailTy)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                    SmtType.None
                have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
              (by simpa [tailD] using hjTail)
          have hTailSelEval :
              __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl tailD)
                      native_nat_zero j)
                    tailSmt) =
                __smtx_apply_arg_nth_value
                  (__smtx_model_eval M tailSmt) j
                  (__smtx_dt_num_sels tailD native_nat_zero) := by
            simpa [tailSmt, tailD] using
              smt_tuple_dt_sel_eval_uses_constructor M hM tailSmt c j
                (by simpa [tailSmt, tailD] using hTailTy)
          have hSelShift :
              __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl fullD)
                      native_nat_zero (Nat.succ j))
                    (__eo_to_smt tupleTerm)) =
                __smtx_model_eval M
                  (SmtTerm.Apply
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl tailD)
                      native_nat_zero j)
                    tailSmt) :=
            hFullSelEval.trans (hOrigSucc.trans hTailSelEval.symm)
          have hNatEq :
              native_nateq (native_int_to_nat n) (Nat.succ j) =
                native_nateq (native_int_to_nat pred) j := by
            rw [hNatSucc]
            simp [native_nateq, Smtm.native_nateq]
          have hRhsSucc' :
              __smtx_apply_arg_nth_value
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head)
                        tailRhs)))
                  (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                __smtx_apply_arg_nth_value (__smtx_model_eval M (__eo_to_smt tailRhs))
                  j (__smtx_dt_num_sels tailD native_nat_zero) := by
            have hsimpa := hRhsSucc
            try simp [headSmt, tailD, fullD, fullC] at hsimpa ⊢
            exact hsimpa
          rw [hRhsSucc']
          rw [hRecProj]
          cases hEq : native_nateq (native_int_to_nat pred) j
          · simpa [native_ite, hNatEq, hEq] using hSelShift.symm
          · simp [native_ite, hNatEq, hEq]
termination_by sizeOf t
decreasing_by
  simp_wf
  subst t
  simp
  omega

private theorem tuple_collapse_updater_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ≠
      SmtType.None ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      (__smtx_model_eval M
        (__eo_to_smt (__tuple_collapse_updater_rhs t a idx))) := by
  intro hTypeEq hLhsNN hRhsNN
  have hRhsTermNN :
      __tuple_collapse_updater_rhs t a idx ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation
      (__tuple_collapse_updater_rhs t a idx) hRhsNN
  rcases tuple_collapse_updater_rhs_ne_stuck_shape t a idx hRhsTermNN with
    hUnit | hTuple
  · subst t
    rcases tuple_update_shape_of_non_none idx (Term.UOp UserOp.tuple_unit) a
        hLhsNN with
      ⟨d, n, hT, hIdx, _hNonneg, hLt⟩
    subst idx
    have hD :
        d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
      change
        __smtx_typeof
            (SmtTerm.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl d) at hT
      unfold __eo_to_smt_tuple_decl at hT
      rw [TranslationProofs.smtx_typeof_tuple_unit_translation] at hT
      injection hT with _ hD'
      simpa [__eo_to_smt_tuple_decl] using hD'.symm
    subst d
    simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hLt
  · rcases hTuple with ⟨head, tail, hTupleEq⟩
    subst t
    let tupleTerm := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail
    let headSmt := __eo_to_smt head
    let tailSmt := __eo_to_smt tail
    let aSmt := __eo_to_smt a
    let headTy := __smtx_typeof headSmt
    rcases tuple_update_shape_of_non_none idx tupleTerm a hLhsNN with
      ⟨d, n, hT, hIdx, hNonneg, hLt⟩
    subst idx
    have hTupleNN : __smtx_typeof (__eo_to_smt tupleTerm) ≠ SmtType.None := by
      rw [hT]
      simp
    rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
        tail head hTupleNN with
      ⟨c, hTailTy⟩
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let fullC := SmtDatatypeCons.cons headTy c
    let fullD := SmtDatatype.sum fullC SmtDatatype.null
    have hTupleTyFull :
        __smtx_typeof (__eo_to_smt tupleTerm) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) := by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD)
      exact
        TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
          tailSmt headSmt headTy c
          (by simpa [tailSmt, tailD] using hTailTy)
          (by
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                SmtType.None
            have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
    have hD : d = fullD := by
      rw [hT] at hTupleTyFull
      injection hTupleTyFull with _ hD'
      simpa [__eo_to_smt_tuple_decl] using hD'
    subst d
    by_cases hn0 : n = 0
    · subst n
      have hNonneg0 : (0 : native_Int) ≤ 0 := by decide
      have hLhsEval :=
        tuple_update_eval_eq_rec_of_tuple_type M hM (Term.Numeral 0)
          tupleTerm a fullC 0 hTupleTyFull rfl hNonneg0 hLt
      have hRecNN :=
        tuple_update_rec_non_none_of_shape (Term.Numeral 0) tupleTerm a
          fullD 0 hTupleTyFull rfl hNonneg0 hLt hLhsNN
      have hComp :=
        updater_rec_eval_components M hM (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl fullD)
          native_nat_zero native_nat_zero
          (__smtx_dt_num_sels fullD native_nat_zero)
          (__eo_to_smt tupleTerm) aSmt hRecNN
      have hCompHead := hComp.1
      have hCompCount := hComp.2.1
      have hCompArgs := hComp.2.2
      have hLhsEval' :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            __smtx_model_eval M
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD)
                  native_nat_zero native_nat_zero)
                (__smtx_dt_num_sels fullD native_nat_zero)
                (__eo_to_smt tupleTerm) aSmt
                (SmtTerm.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD)
                  native_nat_zero)) := by
        have hsimpa := hLhsEval
        try simp [fullD, aSmt] at hsimpa ⊢
        exact hsimpa
      have hANe : a ≠ Term.Stuck := by
        intro hA
        apply hRhsTermNN
        simp [__tuple_collapse_updater_rhs, hA]
      have hRhsEq :
          __tuple_collapse_updater_rhs tupleTerm a (Term.Numeral 0) =
            Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail := by
        cases a <;> simp [tupleTerm, __tuple_collapse_updater_rhs] at hANe ⊢
      have hRhsNNBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) ≠
            SmtType.None := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hRhsNN
      have hLhsTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) :=
        tuple_update_type_eq_tuple_type_of_shape (Term.Numeral 0) tupleTerm a
          fullD 0 hTupleTyFull rfl hNonneg0 hLt hLhsNN
      have hTypeEqBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hTypeEq
      have hRhsTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) := by
        rw [← hTypeEqBase]
        exact hLhsTy
      have hRhsPrependTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum
                  (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                  SmtDatatype.null)) := by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt) tailSmt) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum
                  (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                  SmtDatatype.null))
        exact
          TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
            tailSmt aSmt (__smtx_typeof aSmt) c
            (by simpa [tailSmt, tailD] using hTailTy)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                      tailSmt) ≠ SmtType.None
              have hsimpa := hRhsNNBase; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
      have hFullArgEq :
          SmtDatatype.sum (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
              SmtDatatype.null =
            fullD := by
        have h := hRhsPrependTy.symm.trans hRhsTy
        injection h with _ hD'
        simpa [__eo_to_smt_tuple_decl] using hD'
      have hRhsEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) := by
        rw [smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))
          hRhsNNBase, hRhsTy]
      have hRhsHead :
          __smtx_apply_head_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            SmtValue.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) native_nat_zero :=
        tuple_datatype_value_head_zero (by simpa [fullD] using hRhsEvalTy)
      have hRhsCount :
          vsm_num_apply_args
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            __smtx_dt_num_sels fullD native_nat_zero :=
        tuple_value_count_of_type_local (by simpa [fullD] using hRhsEvalTy)
          (by simpa [fullD] using hRhsHead)
      rw [hLhsEval']
      rw [hRhsEq]
      apply vsm_apply_ext
      · rw [hCompHead, hRhsHead]
      · rw [hCompCount, hRhsCount]
      · intro q hq
        have hqFull : q < __smtx_dt_num_sels fullD native_nat_zero := by
          simpa [hCompCount] using hq
        cases q with
        | zero =>
            have hLhsArg := hCompArgs native_nat_zero hqFull
            have hRhsArg :=
              tuple_prepend_zero_projection M hM aSmt tailSmt
                (__smtx_typeof aSmt) c
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                          tailSmt) ≠ SmtType.None
                  have hsimpa := hRhsNNBase; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
            have hsimpa := hLhsArg.trans hRhsArg.symm
            try simp [hCompCount, hRhsCount, hFullArgEq, aSmt] at hsimpa ⊢
            exact hsimpa
        | succ j =>
            have hjTail :
                j < __smtx_dt_num_sels tailD native_nat_zero := by
              simpa [fullD, fullC, tailD, __smtx_dt_num_sels,
                __smtx_dtc_num_sels] using hqFull
            have hLhsArg := hCompArgs (Nat.succ j) hqFull
            have hSelEval :
                __smtx_model_eval M
                    (SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple")
                        (__eo_to_smt_tuple_decl fullD)
                        native_nat_zero (Nat.succ j))
                      (__eo_to_smt tupleTerm)) =
                  __smtx_apply_arg_nth_value
                    (__smtx_model_eval M (__eo_to_smt tupleTerm))
                    (Nat.succ j)
                    (__smtx_dt_num_sels fullD native_nat_zero) := by
              simpa [fullD, tupleTerm] using
                smt_tuple_dt_sel_eval_uses_constructor M hM
                  (__eo_to_smt tupleTerm) fullC (Nat.succ j)
                  (by simpa [fullD] using hTupleTyFull)
            have hOrigSucc :=
              tuple_prepend_succ_projection M hM headSmt tailSmt headTy c j
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                      SmtType.None
                  have hsimpa := hTupleNN; (try simp [tupleTerm, headSmt, tailSmt, headTy] at hsimpa ⊢); exact hsimpa)
                (by simpa [tailD] using hjTail)
            have hRhsSucc :=
              tuple_prepend_succ_projection M hM aSmt tailSmt
                (__smtx_typeof aSmt) c j
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                          tailSmt) ≠ SmtType.None
                  have hsimpa := hRhsNNBase; (try simp [aSmt, tailSmt] at hsimpa ⊢); exact hsimpa)
                (by simpa [tailD] using hjTail)
            have hLhsArg' :
                __smtx_apply_arg_nth_value
                    (__smtx_model_eval M
                      (__eo_to_smt_updater_rec
                        (SmtTerm.DtSel (native_string_lit "@Tuple")
                          (__eo_to_smt_tuple_decl fullD)
                          native_nat_zero native_nat_zero)
                        (__smtx_dt_num_sels fullD native_nat_zero)
                        (__eo_to_smt tupleTerm) aSmt
                        (SmtTerm.DtCons (native_string_lit "@Tuple")
                          (__eo_to_smt_tuple_decl fullD)
                          native_nat_zero)))
                    (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                  __smtx_apply_arg_nth_value
                    (__smtx_model_eval M tailSmt) j
                    (__smtx_dt_num_sels tailD native_nat_zero) := by
              have hNe : native_nateq native_nat_zero (Nat.succ j) = false := by
                simp [native_nateq, Smtm.native_nateq]
              have hLhsSel :
                  __smtx_apply_arg_nth_value
                      (__smtx_model_eval M
                        (__eo_to_smt_updater_rec
                          (SmtTerm.DtSel (native_string_lit "@Tuple")
                            (__eo_to_smt_tuple_decl fullD)
                            native_nat_zero native_nat_zero)
                          (__smtx_dt_num_sels fullD native_nat_zero)
                          (__eo_to_smt tupleTerm) aSmt
                          (SmtTerm.DtCons (native_string_lit "@Tuple")
                            (__eo_to_smt_tuple_decl fullD)
                            native_nat_zero)))
                      (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                    __smtx_model_eval M
                      (SmtTerm.Apply
                        (SmtTerm.DtSel (native_string_lit "@Tuple")
                          (__eo_to_smt_tuple_decl fullD)
                          native_nat_zero (Nat.succ j))
                        (__eo_to_smt tupleTerm)) := by
                simpa [hNe, tupleTerm] using hLhsArg
              exact hLhsSel.trans (hSelEval.trans hOrigSucc)
            have hsimpa :=
              hRhsSucc.symm
            try simp [hCompCount, hRhsCount, hFullArgEq, hLhsArg', tailD] at hsimpa ⊢
            exact hsimpa
    · have hLhsEval :=
        tuple_update_eval_eq_rec_of_tuple_type M hM (Term.Numeral n)
          tupleTerm a fullC n
          (by simpa [fullD] using hTupleTyFull) rfl hNonneg
          (by simpa [fullD] using hLt)
      have hRecNN :=
        tuple_update_rec_non_none_of_shape (Term.Numeral n) tupleTerm a
          fullD n hTupleTyFull rfl hNonneg hLt hLhsNN
      have hComp :=
        updater_rec_eval_components M hM (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl fullD)
          native_nat_zero (native_int_to_nat n)
          (__smtx_dt_num_sels fullD native_nat_zero)
          (__eo_to_smt tupleTerm) aSmt hRecNN
      have hCompHead := hComp.1
      have hCompCount := hComp.2.1
      have hCompArgs := hComp.2.2
      have hLhsEval' :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral n))
                    tupleTerm) a)) =
            __smtx_model_eval M
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD)
                  native_nat_zero (native_int_to_nat n))
                (__smtx_dt_num_sels fullD native_nat_zero)
                (__eo_to_smt tupleTerm) aSmt
                (SmtTerm.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD)
                  native_nat_zero)) := by
        simpa [fullD, aSmt] using hLhsEval
      have hLhsTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral n))
                    tupleTerm) a)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) :=
        tuple_update_type_eq_tuple_type_of_shape (Term.Numeral n) tupleTerm a
          fullD n hTupleTyFull rfl hNonneg hLt hLhsNN
      have hTypeEq' :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral n))
                    tupleTerm) a)) =
            __smtx_typeof
              (__eo_to_smt
                (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n))) := by
        simpa [tupleTerm] using hTypeEq
      have hRhsTy :
          __smtx_typeof
              (__eo_to_smt
                (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n))) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) := by
        rw [← hTypeEq']
        exact hLhsTy
      have hRhsEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n)))) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) := by
        rw [smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt
            (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n)))
          (by have hsimpa := hRhsNN; (try simp [tupleTerm] at hsimpa ⊢); exact hsimpa), hRhsTy]
      have hRhsHead :
          __smtx_apply_head_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n)))) =
            SmtValue.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) native_nat_zero :=
        tuple_datatype_value_head_zero (by simpa [fullD] using hRhsEvalTy)
      have hRhsCount :
          vsm_num_apply_args
              (__smtx_model_eval M
                (__eo_to_smt
                  (__tuple_collapse_updater_rhs tupleTerm a (Term.Numeral n)))) =
            __smtx_dt_num_sels fullD native_nat_zero :=
        tuple_value_count_of_type_local (by simpa [fullD] using hRhsEvalTy)
          (by simpa [fullD] using hRhsHead)
      rw [hLhsEval']
      apply vsm_apply_ext
      · rw [hCompHead, hRhsHead]
      · rw [hCompCount, hRhsCount]
      · intro q hq
        have hqFull : q < __smtx_dt_num_sels fullD native_nat_zero := by
          simpa [hCompCount] using hq
        have hLhsArg := hCompArgs q hqFull
        have hRhsArg :=
          tuple_collapse_updater_rhs_projection M hM (Term.Numeral n)
            tupleTerm a fullD n q hTupleTyFull rfl hNonneg hLt hRhsTy hqFull
        simpa [hCompCount, hRhsCount, tupleTerm] using
          hLhsArg.trans hRhsArg.symm

private theorem tuple_collapse_updater_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ≠
      SmtType.None ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)))
      (__smtx_model_eval M
        (__eo_to_smt (__tuple_collapse_updater_rhs t a idx))) := by
  intro hTypeEq hLhsNN hRhsNN
  rw [tuple_collapse_updater_eval_eq M hM idx t a hTypeEq hLhsNN hRhsNN]
  exact RuleProofs.smt_value_rel_refl _

private theorem facts___eo_prog_dt_collapse_updater_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_collapse_updater a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_collapse_updater_ne_stuck a1 hProg with
    ⟨lhs, rhs, hA1Eq, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
    subst hA1Eq
    have hA1Ty :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
          Term.Bool := by
      simpa [hProgEq] using hResultTy
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs)
      hA1Trans hA1Ty
  rw [hProgEq]
  rw [hA1Eq]
  apply RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool
  cases lhs with
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp1 op sel =>
              cases op with
              | update =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  have hTypes :=
                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                      (((Term.UOp1 UserOp1.update sel).Apply t).Apply a)
                      rhs hBool
                  have hRhsTrans : RuleProofs.eo_has_smt_translation rhs := by
                    unfold RuleProofs.eo_has_smt_translation
                    rw [← hTypes.1]
                    exact hTypes.2
                  have hRhsNe : rhs ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation rhs
                      hRhsTrans
                  rcases dt_collapse_updater_guard_true_of_rhs_non_stuck
                      sel t a rhs hGuard hRhsNe with
                    ⟨hFindNeg, hRhsEq⟩
                  rw [hRhsEq]
                  change RuleProofs.smt_value_rel
                    (__smtx_model_eval M
                      (__eo_to_smt_updater (__eo_to_smt sel)
                        (__eo_to_smt t) (__eo_to_smt a)))
                    (__smtx_model_eval M (__eo_to_smt t))
                  by_cases hIsDtSel :
                      ∃ s d i j, __eo_to_smt sel = SmtTerm.DtSel s d i j
                  · rcases hIsDtSel with ⟨s, d, i, j, hSelSmt⟩
                    have hUpdaterNN :
                        __smtx_typeof
                            (__eo_to_smt_updater (SmtTerm.DtSel s d i j)
                              (__eo_to_smt t) (__eo_to_smt a)) ≠
                          SmtType.None := by
                      have h := hTypes.2
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
                        sel s d i j hSelSmt with hDt | hPurify
                    · rcases hDt with ⟨d0, hd, hSelEq, hReserved⟩
                      subst sel
                      subst d
                      have hDtEqFalse :
                          __dt_eq_cons (Term.DtCons s d0 i) t =
                            Term.Boolean false :=
                        dt_eq_cons_false_of_find_neg_dt_sel_of_updater_non_none
                          s d0 i j t a hReserved hUpdaterNN
                          (by simpa using hFindNeg)
                      have hIdxProp :
                          native_nat_to_int j <
                            native_nat_to_int
                              (__smtx_dt_num_sels
                                (__smtx_dd_lookup s
                                  (__eo_to_smt_datatype_decl d0)) i) := by
                        apply of_decide_eq_true
                        simpa [native_zlt, SmtEval.native_zlt] using hIdx
                      have hIteNN :
                          term_has_non_none_type
                            (SmtTerm.ite
                              (SmtTerm.Apply
                                (SmtTerm.DtTester s
                                  (__eo_to_smt_datatype_decl d0) i)
                                (__eo_to_smt t))
                              (__eo_to_smt_updater_rec
                                (SmtTerm.DtSel s
                                  (__eo_to_smt_datatype_decl d0) i j)
                                (__smtx_dt_num_sels
                                  (__smtx_dd_lookup s
                                    (__eo_to_smt_datatype_decl d0)) i)
                                (__eo_to_smt t) (__eo_to_smt a)
                                (SmtTerm.DtCons s
                                  (__eo_to_smt_datatype_decl d0) i))
                              (__eo_to_smt t)) := by
                        unfold term_has_non_none_type
                        simpa [__eo_to_smt_updater, native_ite, hIdxProp] using
                          hUpdaterNN
                      rcases ite_args_of_non_none hIteNN with
                        ⟨_T, hCond, _hThen, _hElse, _hTNN⟩
                      have hTesterNN :
                          term_has_non_none_type
                            (SmtTerm.Apply
                              (SmtTerm.DtTester s
                                (__eo_to_smt_datatype_decl d0) i)
                              (__eo_to_smt t)) := by
                        unfold term_has_non_none_type
                        rw [hCond]
                        simp
                      have hTesterFalse :=
                        dt_tester_eval_false_of_dt_eq_cons_dtcons_false
                          M hM s d0 i t hReserved hTesterNN hDtEqFalse
                      let cond :=
                        SmtTerm.Apply
                          (SmtTerm.DtTester s
                            (__eo_to_smt_datatype_decl d0) i)
                          (__eo_to_smt t)
                      let recTerm :=
                        __eo_to_smt_updater_rec
                          (SmtTerm.DtSel s
                            (__eo_to_smt_datatype_decl d0) i j)
                          (__smtx_dt_num_sels
                            (__smtx_dd_lookup s
                              (__eo_to_smt_datatype_decl d0)) i)
                          (__eo_to_smt t) (__eo_to_smt a)
                          (SmtTerm.DtCons s
                            (__eo_to_smt_datatype_decl d0) i)
                      have hUpdaterEq :
                          __eo_to_smt_updater
                              (SmtTerm.DtSel s
                                (__eo_to_smt_datatype_decl d0) i j)
                              (__eo_to_smt t) (__eo_to_smt a) =
                            SmtTerm.ite cond recTerm (__eo_to_smt t) := by
                        simp [cond, recTerm, __eo_to_smt_updater, native_ite,
                          hIdxProp]
                      have hEvalIte :
                          __smtx_model_eval M
                              (SmtTerm.ite cond recTerm (__eo_to_smt t)) =
                            __smtx_model_eval M (__eo_to_smt t) := by
                        rw [smtx_eval_ite_term_eq]
                        rw [show __smtx_model_eval M cond =
                            SmtValue.Boolean false by
                          simpa [cond] using hTesterFalse]
                        simp [__smtx_model_eval_ite]
                      rw [hSelSmt]
                      rw [hUpdaterEq]
                      rw [hEvalIte]
                      exact RuleProofs.smt_value_rel_refl _
                    · rcases hPurify with ⟨z0, hSelEq, _hz0⟩
                      subst sel
                      change SmtTerm._at_purify (__eo_to_smt z0) =
                        SmtTerm.DtSel s d i j at hSelSmt
                      cases hSelSmt
                  · exfalso
                    apply hTypes.2
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
              | tuple_update =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  subst rhs
                  have hTypes :=
                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                      (((Term.UOp1 UserOp1.tuple_update sel).Apply t).Apply a)
                      (__tuple_collapse_updater_rhs t a sel) hBool
                  exact tuple_collapse_updater_eval_rel M hM sel t a
                    hTypes.1
                    hTypes.2
                    (by
                      rw [← hTypes.1]
                      exact hTypes.2)
              | _ =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  subst rhs
                  exact False.elim (eq_rhs_stuck_not_bool _ hBool)
          | _ =>
              simp [__mk_dt_collapse_updater_rhs] at hGuard
              subst rhs
              exact False.elim (eq_rhs_stuck_not_bool _ hBool)
      | _ =>
          simp [__mk_dt_collapse_updater_rhs] at hGuard
          subst rhs
          exact False.elim (eq_rhs_stuck_not_bool _ hBool)
  | _ =>
      simp [__mk_dt_collapse_updater_rhs] at hGuard
      subst rhs
      exact False.elim (eq_rhs_stuck_not_bool _ hBool)

public theorem cmd_step_dt_collapse_updater_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_updater args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_collapse_updater args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_updater args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.dt_collapse_updater args premises ≠
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
              change __eo_typeof (__eo_prog_dt_collapse_updater a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_collapse_updater a1) true
                exact facts___eo_prog_dt_collapse_updater_impl
                  M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_collapse_updater a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_collapse_updater a1)
                  (typed___eo_prog_dt_collapse_updater_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
