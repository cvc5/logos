module

public import Cpc.Proofs.RuleSupport.DtConsEqSupport
import all Cpc.Proofs.RuleSupport.DtConsEqSupport
public import Cpc.Proofs.RuleSupport.DtCollapseSelectorSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

attribute [local simp] native_ite native_teq native_not native_and native_zlt

/-!
Support for rules whose conclusion builds an explicit tuple
`(tuple h0 (tuple h1 ... tuple.unit))`, namely the tuple cases of
`dt-inst` and `dt-updater-elim`.
-/

/-- `r` is an explicit tuple whose components are `hs`. -/
inductive TupleSpine : Term -> List Term -> Prop
  | unit : TupleSpine (Term.UOp UserOp.tuple_unit) []
  | cons (h tail : Term) (hs : List Term) :
      TupleSpine tail hs ->
      TupleSpine (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) h) tail) (h :: hs)

private theorem tsp_smt_model_eval_ne_notvalue_of_non_none
    (M : SmtModel) (hM : model_wf M) (x : SmtTerm) :
    __smtx_typeof x ≠ SmtType.None ->
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  intro hNN hEval
  have hPres := smt_model_eval_preserves_type_of_non_none M hM x hNN
  have hNone : __smtx_typeof_value (__smtx_model_eval M x) = SmtType.None := by
    simp [hEval, __smtx_typeof_value]
  rw [hPres] at hNone
  exact hNN hNone

private theorem tsp_smtx_model_eval_apply_of_dt_chain
    (M : SmtModel) (v x : SmtValue)
    (hHead : ∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i)
    (hx : x ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M v x = SmtValue.Apply v x := by
  cases x <;> simp [__smtx_model_eval_apply] at hx ⊢
  all_goals
    cases v <;> simp [__smtx_apply_head_value] at hHead ⊢

private theorem tsp_smtx_ite_then_non_none
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

private theorem tsp_smtx_apply_arg_non_none_of_non_none
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

private theorem tsp_smtx_apply_head_non_none_of_non_none
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

private theorem tsp_eo_to_smt_updater_rec_ne_dt_sel_local
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

private theorem tsp_eo_to_smt_updater_rec_ne_dt_tester_local
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

private theorem tsp_smtx_model_eval_apply_eq_apply_of_not_dt_ops
    (M : SmtModel) (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f with
  | DtSel s d i j => exact False.elim (hSel s d i j rfl)
  | DtTester s d i => exact False.elim (hTester s d i rfl)
  | _ => simp [__smtx_model_eval]

private theorem tsp_updater_rec_eval_components
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
        tsp_eo_to_smt_updater_rec_ne_dt_sel_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 j0 h; cases h)
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 :=
        tsp_eo_to_smt_updater_rec_ne_dt_tester_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 h; cases h)
      have hRecNN : __smtx_typeof recTerm ≠ SmtType.None :=
        tsp_smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      have hArgNN : __smtx_typeof argTerm ≠ SmtType.None :=
        tsp_smtx_apply_arg_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      rcases ih hRecNN with ⟨hHeadRec, hCountRec, hArgsRec⟩
      have hArgNot :
          __smtx_model_eval M argTerm ≠ SmtValue.NotValue :=
        tsp_smt_model_eval_ne_notvalue_of_non_none M hM argTerm hArgNN
      have hEvalApply :
          __smtx_model_eval M (SmtTerm.Apply recTerm argTerm) =
            SmtValue.Apply (__smtx_model_eval M recTerm)
              (__smtx_model_eval M argTerm) := by
        rw [tsp_smtx_model_eval_apply_eq_apply_of_not_dt_ops
          M recTerm argTerm hRecSel hRecTester]
        rw [tsp_smtx_model_eval_apply_of_dt_chain M
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
            simp [native_nateq, SmtEval.native_nateq]
          rw [hEval]
          simp [__smtx_apply_arg_nth_value,hEqBool, argTerm]
        · have hqk : q < k := by
            exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hq) hLast
          have hNeBool : native_nateq q k = false := by
            simp [native_nateq, SmtEval.native_nateq, hLast]
          rw [hEval]
          simp [__smtx_apply_arg_nth_value,hNeBool]
          exact hArgsRec q hqk

private theorem tsp_tuple_update_shape_of_non_none
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
                  SmtEval.native_nat_to_int] using hIdxBoundBool
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

private theorem tsp_tuple_update_rec_non_none_of_shape
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
      SmtEval.native_zlt, native_nat_to_int, SmtEval.native_nat_to_int,
      hIdxProp, __eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
      SmtEval.native_streq] using hUpdaterNN
  exact tsp_smtx_ite_then_non_none _ _ _ hIteNN

private theorem tsp_tuple_value_count_of_type_local
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

private theorem tsp_tuple_update_eval_eq_rec_of_tuple_type
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
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hIdxProp
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
    tuple_value_head_zero_of_type hEvalTy
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

private theorem tsp_tuple_update_type_eq_tuple_type_of_shape
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
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hIdxProp
  have hRecNN :=
    tsp_tuple_update_rec_non_none_of_shape (Term.Numeral n) t a d n
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


private theorem tsp_prepend_components
    (tailD : SmtDatatype) (tv : SmtValue) (s : native_String)
    (d : SmtDatatypeDecl) (i : native_Nat) (hv : SmtValue) :
    ∀ k,
      vsm_num_apply_args
          (tuplePrependValueRec tailD tv k
            (SmtValue.Apply (SmtValue.DtCons s d i) hv)) = k + 1 ∧
      __smtx_apply_arg_nth_value
          (tuplePrependValueRec tailD tv k
            (SmtValue.Apply (SmtValue.DtCons s d i) hv)) 0 (k + 1) = hv ∧
      ∀ j, j < k ->
        __smtx_apply_arg_nth_value
            (tuplePrependValueRec tailD tv k
              (SmtValue.Apply (SmtValue.DtCons s d i) hv)) (j + 1) (k + 1) =
          __smtx_apply_arg_nth_value tv j
            (__smtx_dt_num_sels tailD native_nat_zero)
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · simp [tuplePrependValueRec, vsm_num_apply_args]
      · simp [tuplePrependValueRec, __smtx_apply_arg_nth_value,
          SmtEval.native_nateq]
      · intro j hj
        omega
  | Nat.succ k => by
      rcases tsp_prepend_components tailD tv s d i hv k with ⟨hC, h0, hA⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [tuplePrependValueRec, vsm_num_apply_args, hC]
      · have hNe : (0 : Nat) ≠ k + 1 := by omega
        simpa [tuplePrependValueRec, __smtx_apply_arg_nth_value,
          SmtEval.native_nateq, hNe] using h0
      · intro j hj
        by_cases hjk : j = k
        · subst hjk
          simp [tuplePrependValueRec, __smtx_apply_arg_nth_value,
            SmtEval.native_nateq]
        · have hj' : j < k := by omega
          have hNe : j + 1 ≠ k + 1 := by omega
          simpa [tuplePrependValueRec, __smtx_apply_arg_nth_value,
            SmtEval.native_nateq, hNe, hjk] using hA j hj'

private theorem tsp_tuple_unit_typeof :
    __smtx_typeof (__eo_to_smt (Term.UOp UserOp.tuple_unit)) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) := by
  change __smtx_typeof
      (SmtTerm.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) = _
  simpa [__eo_to_smt_tuple_decl] using
    TranslationProofs.smtx_typeof_tuple_unit_translation

theorem tupleSpine_eval_components
    (M : SmtModel) (hM : model_wf M) {r : Term} {hs : List Term}
    (hSp : TupleSpine r hs) :
    __smtx_typeof (__eo_to_smt r) ≠ SmtType.None ->
    (∃ c,
      __smtx_typeof (__eo_to_smt r) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))) ∧
    vsm_num_apply_args (__smtx_model_eval M (__eo_to_smt r)) = hs.length ∧
    ∀ (j : Nat) (h : Term), hs[j]? = some h ->
      __smtx_apply_arg_nth_value (__smtx_model_eval M (__eo_to_smt r)) j
          hs.length =
        __smtx_model_eval M (__eo_to_smt h) := by
  induction hSp with
  | unit =>
      intro _hNN
      refine ⟨⟨SmtDatatypeCons.unit, tsp_tuple_unit_typeof⟩, ?_, ?_⟩
      · change
          vsm_num_apply_args
              (__smtx_model_eval M
                (SmtTerm.DtCons (native_string_lit "@Tuple")
                  (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
                    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
                    SmtDatatypeDecl.nil) native_nat_zero)) = 0
        simp [__smtx_model_eval, vsm_num_apply_args]
      · intro j h hj
        simp at hj
  | cons h tail hs hSp ih =>
      intro hNN
      have hNN' :
          __smtx_typeof
              (__eo_to_smt_tuple_prepend (__eo_to_smt h)
                (__smtx_typeof (__eo_to_smt h)) (__eo_to_smt tail)) ≠
            SmtType.None := hNN
      have hEo :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) h) tail) =
            __eo_to_smt_tuple_prepend (__eo_to_smt h)
              (__smtx_typeof (__eo_to_smt h)) (__eo_to_smt tail) := rfl
      rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
          tail h hNN with ⟨c, hTailTy⟩
      have hTailNN : __smtx_typeof (__eo_to_smt tail) ≠ SmtType.None := by
        rw [hTailTy]
        simp
      rcases ih hTailNN with ⟨_hTailShape, hCount, hArgs⟩
      have hEval :=
        tuple_prepend_eval_eq_value_rec M hM (__eo_to_smt h) (__eo_to_smt tail)
          (__smtx_typeof (__eo_to_smt h)) c rfl hTailTy hNN'
      dsimp only at hEval
      have hTailEvalTy :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt tail)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
        rw [smt_model_eval_preserves_type_of_non_none M hM _ hTailNN, hTailTy]
      have hTailHead := tuple_value_head_zero_of_type hTailEvalTy
      have hTailCount := tuple_value_count_of_type hTailEvalTy hTailHead
      have hm :
          __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero = hs.length :=
        hTailCount.symm.trans hCount
      rcases tsp_prepend_components (SmtDatatype.sum c SmtDatatype.null)
          (__smtx_model_eval M (__eo_to_smt tail)) (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum
              (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt h)) c)
              SmtDatatype.null))
          native_nat_zero (__smtx_model_eval M (__eo_to_smt h))
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero) with
        ⟨hC, h0, hA⟩
      rw [hm] at hC h0 hA
      refine ⟨⟨SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt h)) c, ?_⟩, ?_, ?_⟩
      · rw [hEo]
        exact TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
          _ _ _ c hTailTy hNN'
      · rw [hEo, hEval]
        rw [hm]
        simpa using hC
      · intro j x hx
        rw [hEo, hEval]
        try rw [hm]
        simp only [List.length_cons]
        cases j with
        | zero =>
            simp at hx
            subst hx
            exact h0
        | succ j =>
            simp at hx
            have hjlt : j < hs.length := (List.getElem?_eq_some_iff.mp hx).1
            rw [hA j hjlt, hArgs j x hx]

theorem tupleSpine_eval_eq
    (M : SmtModel) (hM : model_wf M) {r : Term} {hs : List Term}
    (hSp : TupleSpine r hs)
    (hRNN : __smtx_typeof (__eo_to_smt r) ≠ SmtType.None)
    (V : SmtValue)
    (hVTy : __smtx_typeof_value V = __smtx_typeof (__eo_to_smt r))
    (hArgs : ∀ (j : Nat) (h : Term), hs[j]? = some h ->
      __smtx_model_eval M (__eo_to_smt h) =
        __smtx_apply_arg_nth_value V j (vsm_num_apply_args V)) :
    __smtx_model_eval M (__eo_to_smt r) = V := by
  rcases tupleSpine_eval_components M hM hSp hRNN with
    ⟨⟨c, hRTy⟩, hCount, hRArgs⟩
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM _ hRNN, hRTy]
  have hVTy' := hVTy.trans hRTy
  have hRHead := tuple_value_head_zero_of_type hREvalTy
  have hVHead := tuple_value_head_zero_of_type hVTy'
  have hRCount := tuple_value_count_of_type hREvalTy hRHead
  have hVCount := tuple_value_count_of_type hVTy' hVHead
  have hLen : hs.length = vsm_num_apply_args V := by
    rw [← hCount, hRCount, hVCount]
  apply vsm_apply_ext
  · rw [hRHead, hVHead]
  · rw [hCount, hLen]
  · intro j hj
    rw [hCount] at hj ⊢
    have hget : hs[j]? = some hs[j] := List.getElem?_eq_getElem hj
    rw [hRArgs j _ hget, hArgs j _ hget]

theorem tuple_select_numeral_eval
    (M : SmtModel) (hM : model_wf M) (x : Term) (c : SmtDatatypeCons)
    (j : Nat)
    (hXTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) x)) =
      __smtx_apply_arg_nth_value (__smtx_model_eval M (__eo_to_smt x)) j
        (vsm_num_apply_args (__smtx_model_eval M (__eo_to_smt x))) := by
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hXTy]
    simp
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM _ hXNN, hXTy]
  have hHead := tuple_value_head_zero_of_type hXEvalTy
  have hCount := tuple_value_count_of_type hXEvalTy hHead
  have hTrans :
      __eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) x) =
        SmtTerm.Apply
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
            native_nat_zero j)
          (__eo_to_smt x) := by
    change
      __eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt x))
          (__eo_to_smt (Term.Numeral (j : Int))) (__eo_to_smt x) = _
    rw [hXTy]
    simp [__eo_to_smt_tuple_select, __eo_to_smt_tuple_decl, __eo_to_smt,
      native_streq, SmtEval.native_streq, native_zleq, SmtEval.native_zleq,
      native_int_to_nat, SmtEval.native_int_to_nat]
  rw [hTrans, tuple_selector_eval_eq_arg M (SmtDatatype.sum c SmtDatatype.null)
    (__eo_to_smt x) j hHead, hCount]

/-! ### `dt-inst` for tuples -/

private theorem tsp_mk_apply_of_ne' {x y : Term}
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  unfold __eo_mk_apply
  split <;> simp_all

private theorem mk_dt_inst_tuple_rec_shape (T x n : Term) :
    __mk_dt_inst_tuple_rec T x n ≠ Term.Stuck ->
    T = Term.UOp UserOp.UnitTuple ∨
      ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 := by
  intro hNe
  unfold __mk_dt_inst_tuple_rec at hNe
  split at hNe <;>
    first
    | exact absurd rfl hNe
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl⟩

private theorem mk_dt_inst_tuple_rec_unit (x n : Term)
    (hx : x ≠ Term.Stuck) (hn : n ≠ Term.Stuck) :
    __mk_dt_inst_tuple_rec (Term.UOp UserOp.UnitTuple) x n =
      Term.UOp UserOp.tuple_unit := by
  rw [__mk_dt_inst_tuple_rec.eq_def]
  split <;> simp_all

private theorem mk_dt_inst_tuple_rec_tuple (T1 T2 x : Term) (n : Int)
    (hx : x ≠ Term.Stuck) :
    __mk_dt_inst_tuple_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2) x
        (Term.Numeral n) =
      __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.tuple)
          (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral n)) x))
        (__mk_dt_inst_tuple_rec T2 x (Term.Numeral (n + 1))) := by
  rw [__mk_dt_inst_tuple_rec.eq_def]
  split <;> simp_all [__eo_add, native_zplus, SmtEval.native_zplus]

private theorem mk_dt_inst_tuple_rec_spine_aux (x : Term) (hx : x ≠ Term.Stuck)
    (k : Nat) : ∀ (T : Term) (n : Int), sizeOf T < k ->
    __mk_dt_inst_tuple_rec T x (Term.Numeral n) ≠ Term.Stuck ->
      ∃ hs : List Term, TupleSpine (__mk_dt_inst_tuple_rec T x (Term.Numeral n)) hs ∧
        ∀ (j : Nat) (h : Term), hs[j]? = some h ->
          h = Term.Apply
            (Term.UOp1 UserOp1.tuple_select (Term.Numeral (n + (j : Int)))) x := by
  induction k with
  | zero => intro T n hk; omega
  | succ k ih =>
  intro T n hk hNe
  rcases mk_dt_inst_tuple_rec_shape T x (Term.Numeral n) hNe with
    rfl | ⟨T1, T2, rfl⟩
  · rw [mk_dt_inst_tuple_rec_unit x _ hx (by simp)]
    exact ⟨[], TupleSpine.unit, by intro j h hj; simp at hj⟩
  · rw [mk_dt_inst_tuple_rec_tuple T1 T2 x n hx] at hNe ⊢
    have hRecNe :
        __mk_dt_inst_tuple_rec T2 x (Term.Numeral (n + 1)) ≠ Term.Stuck := by
      intro hStuck
      apply hNe
      rw [hStuck]
      simp [__eo_mk_apply]
    rw [tsp_mk_apply_of_ne' (by simp) hRecNe]
    rcases ih T2 (n + 1) (by simp at hk; omega) hRecNe with ⟨hs, hSp, hSel⟩
    refine ⟨_ :: hs, TupleSpine.cons _ _ hs hSp, ?_⟩
    intro j h hj
    cases j with
    | zero =>
        simp at hj
        subst hj
        simp
    | succ j =>
        simp at hj
        have hShift : n + 1 + (j : Int) = n + ((j + 1 : Nat) : Int) := by
          push_cast
          omega
        rw [hSel j h hj, hShift]

theorem mk_dt_inst_tuple_rec_spine (x : Term) (hx : x ≠ Term.Stuck)
    (T : Term) (n : Int)
    (hNe : __mk_dt_inst_tuple_rec T x (Term.Numeral n) ≠ Term.Stuck) :
      ∃ hs : List Term, TupleSpine (__mk_dt_inst_tuple_rec T x (Term.Numeral n)) hs ∧
        ∀ (j : Nat) (h : Term), hs[j]? = some h ->
          h = Term.Apply
            (Term.UOp1 UserOp1.tuple_select (Term.Numeral (n + (j : Int)))) x :=
  mk_dt_inst_tuple_rec_spine_aux x hx (sizeOf T + 1) T n (by omega) hNe

private theorem mk_dt_inst_tuple_shape (T x : Term) (hx : x ≠ Term.Stuck) :
    __mk_dt_inst_tuple T x ≠ Term.Stuck ->
    (T = Term.UOp UserOp.UnitTuple ∧
        __mk_dt_inst_tuple T x = Term.UOp UserOp.tuple_unit) ∨
      ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 ∧
        __mk_dt_inst_tuple T x = __mk_dt_inst_tuple_rec T x (Term.Numeral 0) := by
  intro hNe
  have hNe' := hNe
  unfold __mk_dt_inst_tuple at hNe'
  split at hNe'
  · exact absurd rfl hNe'
  · right
    exact ⟨_, _, rfl, by rw [__mk_dt_inst_tuple.eq_def]; split <;> simp_all⟩
  · left
    exact ⟨rfl, by rw [__mk_dt_inst_tuple.eq_def]; split <;> simp_all⟩
  · exact absurd rfl hNe'

theorem mk_dt_inst_tuple_spine (x : Term) (hx : x ≠ Term.Stuck) :
    __mk_dt_inst_tuple (__eo_typeof x) x ≠ Term.Stuck ->
    ∃ hs : List Term, TupleSpine (__mk_dt_inst_tuple (__eo_typeof x) x) hs ∧
      ∀ (j : Nat) (h : Term), hs[j]? = some h ->
        h = Term.Apply
          (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) x := by
  intro hNe
  rcases mk_dt_inst_tuple_shape (__eo_typeof x) x hx hNe with
    ⟨_hT, hEq⟩ | ⟨T1, T2, hT, hEq⟩
  · rw [hEq]
    exact ⟨[], TupleSpine.unit, by intro j h hj; simp at hj⟩
  · rw [hEq] at hNe ⊢
    rcases mk_dt_inst_tuple_rec_spine x hx _ 0 hNe with ⟨hs, hSp, hSel⟩
    exact ⟨hs, hSp, by intro j h hj; simpa using hSel j h hj⟩

/-- Semantic core of the tuple case of `dt-inst`. -/
theorem tuple_inst_eval_eq
    (M : SmtModel) (hM : model_wf M) (x r : Term) (hs : List Term)
    (hSp : TupleSpine r hs)
    (hSel : ∀ (j : Nat) (h : Term), hs[j]? = some h ->
      h = Term.Apply
        (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) x)
    (hTy : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt r))
    (hRNN : __smtx_typeof (__eo_to_smt r) ≠ SmtType.None) :
    __smtx_model_eval M (__eo_to_smt r) = __smtx_model_eval M (__eo_to_smt x) := by
  rcases tupleSpine_eval_components M hM hSp hRNN with ⟨⟨c, hRTy⟩, _, _⟩
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hTy]
    exact hRNN
  apply tupleSpine_eval_eq M hM hSp hRNN
  · rw [smt_model_eval_preserves_type_of_non_none M hM _ hXNN, hTy]
  · intro j h hj
    rw [hSel j h hj]
    exact tuple_select_numeral_eval M hM x c j (hTy.trans hRTy)

/-! ### `dt-updater-elim` for tuples -/

private theorem tsp_requires_eq (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck -> T = U := by
  intro hReq
  by_cases hEq : T = U
  · exact hEq
  · exfalso
    apply hReq
    simp [__eo_requires, hEq]

private theorem tsp_mk_apply_of_ne {x y : Term}
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  unfold __eo_mk_apply
  split <;> simp_all

private theorem tsp_get_selectors_rec_shape (T n : Term) :
    __tuple_get_selectors_rec T n ≠ Term.Stuck ->
    T = Term.UOp UserOp.UnitTuple ∨
      ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 := by
  intro hNe
  unfold __tuple_get_selectors_rec at hNe
  split at hNe <;>
    first
    | exact absurd rfl hNe
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, rfl⟩

private theorem tuple_updater_elim_rhs_spine_aux (nn : Int) (t a : Term)
    (k : Nat) : ∀ (T : Term) (b : Int), sizeOf T < k ->
    __tuple_updater_elim_rhs
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
          (__tuple_get_selectors_rec T (Term.Numeral b)) ≠ Term.Stuck ->
      ∃ hs : List Term,
        TupleSpine
          (__tuple_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
            (__tuple_get_selectors_rec T (Term.Numeral b))) hs ∧
        ∀ (j : Nat) (h : Term), hs[j]? = some h ->
          (nn = b + (j : Int) ∧ h = a) ∨
          (nn ≠ b + (j : Int) ∧
            h = Term.Apply
              (Term.UOp1 UserOp1.tuple_select (Term.Numeral (b + (j : Int)))) t) := by
  induction k with
  | zero => intro T b hk; omega
  | succ k ih =>
  intro T b hk hNe
  have hSelsNe : __tuple_get_selectors_rec T (Term.Numeral b) ≠ Term.Stuck := by
    intro hStuck
    apply hNe
    rw [hStuck]
    simp [__tuple_updater_elim_rhs]
  rcases tsp_get_selectors_rec_shape T (Term.Numeral b) hSelsNe with
    rfl | ⟨T1, T2, rfl⟩
  · have hEq :
        __tuple_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
            (__tuple_get_selectors_rec (Term.UOp UserOp.UnitTuple)
              (Term.Numeral b)) =
          Term.UOp UserOp.tuple_unit := by
      simp [__tuple_updater_elim_rhs, __tuple_get_selectors_rec,
        __eo_l_1___tuple_updater_elim_rhs]
    rw [hEq]
    exact ⟨[], TupleSpine.unit, by intro j h hj; simp at hj⟩
  · 
      let U :=
        Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a
      let ss' := __tuple_get_selectors_rec T2 (Term.Numeral (b + 1))
      have hSels :
          __tuple_get_selectors_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
              (Term.Numeral b) =
            __eo_mk_apply
              (Term.Apply Term.__eo_List_cons
                (Term.UOp1 UserOp1.tuple_select (Term.Numeral b))) ss' := by
        simp [__tuple_get_selectors_rec, __eo_add, native_zplus,
          SmtEval.native_zplus, ss']
      have hSsNe : ss' ≠ Term.Stuck := by
        intro hStuck
        apply hNe
        rw [hSels, hStuck]
        simp [__eo_mk_apply, __tuple_updater_elim_rhs]
      have hSels' :
          __tuple_get_selectors_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
              (Term.Numeral b) =
            Term.Apply
              (Term.Apply Term.__eo_List_cons
                (Term.UOp1 UserOp1.tuple_select (Term.Numeral b))) ss' := by
        rw [hSels]
        exact tsp_mk_apply_of_ne (by simp) hSsNe
      let R' := __tuple_updater_elim_rhs U ss'
      have hRhs :
          __tuple_updater_elim_rhs U
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.UOp1 UserOp1.tuple_select (Term.Numeral b))) ss') =
            __eo_ite (__eo_eq (Term.Numeral nn) (Term.Numeral b))
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) a) R')
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.tuple)
                  (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral b)) t))
                R') := by
        simp [__tuple_updater_elim_rhs, __eo_l_1___tuple_updater_elim_rhs, U, R']
      change __tuple_updater_elim_rhs U _ ≠ Term.Stuck at hNe
      change ∃ hs : List Term, TupleSpine (__tuple_updater_elim_rhs U _) hs ∧ _
      rw [hSels', hRhs] at *
      have hR'Ne : R' ≠ Term.Stuck := by
        intro hStuck
        apply hNe
        rw [hStuck]
        simp [__eo_mk_apply]
      rcases ih T2 (b + 1) (by simp at hk; omega) hR'Ne with ⟨hs, hSp, hComp⟩
      have hShift : ∀ j : Nat, b + 1 + (j : Int) = b + ((j + 1 : Nat) : Int) := by
        intro j
        push_cast
        omega
      by_cases hnb : nn = b
      · subst hnb
        have hIte :
            __eo_ite (__eo_eq (Term.Numeral nn) (Term.Numeral nn))
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) a) R')
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.tuple)
                    (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral nn)) t))
                  R') =
              Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) R' := by
          simp [__eo_eq]
          exact tsp_mk_apply_of_ne (by simp) hR'Ne
        rw [hIte]
        refine ⟨a :: hs, TupleSpine.cons _ _ hs hSp, ?_⟩
        intro j h hj
        cases j with
        | zero =>
            simp at hj
            subst hj
            left
            simp
        | succ j =>
            simp at hj
            rcases hComp j h hj with ⟨hEq, hH⟩ | ⟨hEq, hH⟩
            · left
              exact ⟨by rw [← hShift j]; exact hEq, hH⟩
            · right
              exact ⟨by rw [← hShift j]; exact hEq, by rw [hH, hShift j]⟩
      · have hIte :
            __eo_ite (__eo_eq (Term.Numeral nn) (Term.Numeral b))
                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) a) R')
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.tuple)
                    (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral b)) t))
                  R') =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.tuple)
                  (Term.Apply (Term.UOp1 UserOp1.tuple_select (Term.Numeral b)) t))
                R' := by
          have hbn : b ≠ nn := fun h => hnb h.symm
          simp [__eo_eq, hbn]
          exact tsp_mk_apply_of_ne (by simp) hR'Ne
        rw [hIte]
        refine ⟨_ :: hs, TupleSpine.cons _ _ hs hSp, ?_⟩
        intro j h hj
        cases j with
        | zero =>
            simp at hj
            subst hj
            right
            simp [hnb]
        | succ j =>
            simp at hj
            rcases hComp j h hj with ⟨hEq, hH⟩ | ⟨hEq, hH⟩
            · left
              exact ⟨by rw [← hShift j]; exact hEq, hH⟩
            · right
              exact ⟨by rw [← hShift j]; exact hEq, by rw [hH, hShift j]⟩

theorem tuple_updater_elim_rhs_spine (nn : Int) (t a : Term)
    (T : Term) (b : Int)
    (hNe : __tuple_updater_elim_rhs
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
          (__tuple_get_selectors_rec T (Term.Numeral b)) ≠ Term.Stuck) :
      ∃ hs : List Term,
        TupleSpine
          (__tuple_updater_elim_rhs
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
            (__tuple_get_selectors_rec T (Term.Numeral b))) hs ∧
        ∀ (j : Nat) (h : Term), hs[j]? = some h ->
          (nn = b + (j : Int) ∧ h = a) ∨
          (nn ≠ b + (j : Int) ∧
            h = Term.Apply
              (Term.UOp1 UserOp1.tuple_select (Term.Numeral (b + (j : Int)))) t) :=
  tuple_updater_elim_rhs_spine_aux nn t a (sizeOf T + 1) T b (by omega) hNe

private theorem tsp_dt_get_selectors_tuple_shape (T : Term) :
    __dt_get_selectors T (Term.UOp UserOp.tuple) ≠ Term.Stuck ->
    ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 := by
  intro hNe
  unfold __dt_get_selectors at hNe
  split at hNe <;>
    first
    | exact absurd rfl hNe
    | exact ⟨_, _, rfl⟩
    | (exfalso; simp_all [__eo_dt_selectors, __eo_dt_selectors_main])

theorem mk_dt_updater_elim_conc_tuple_spine (nn : Int) (t a rhs : Term) :
    __mk_dt_updater_elim_conc
        (Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)
        rhs = Term.Boolean true ->
    ∃ hs : List Term, TupleSpine rhs hs ∧
      ∀ (j : Nat) (h : Term), hs[j]? = some h ->
        (nn = (j : Int) ∧ h = a) ∨
        (nn ≠ (j : Int) ∧
          h = Term.Apply
            (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) t) := by
  intro hConc
  let U :=
    Term.Apply
      (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a
  have hRhsNe : rhs ≠ Term.Stuck := by
    intro hStuck
    subst hStuck
    simp [__mk_dt_updater_elim_conc] at hConc
  have hReq :
      __eo_requires
          (__mk_dt_updater_elim_rhs U (Term.UOp UserOp.tuple)
            (__dt_get_selectors (__eo_typeof t) (Term.UOp UserOp.tuple)))
          rhs (Term.Boolean true) = Term.Boolean true := by
    simpa [__mk_dt_updater_elim_conc, U, hRhsNe] using hConc
  have hReqNe :
      __eo_requires
          (__mk_dt_updater_elim_rhs U (Term.UOp UserOp.tuple)
            (__dt_get_selectors (__eo_typeof t) (Term.UOp UserOp.tuple)))
          rhs (Term.Boolean true) ≠ Term.Stuck := by
    rw [hReq]
    simp
  have hMk :
      __mk_dt_updater_elim_rhs U (Term.UOp UserOp.tuple)
          (__dt_get_selectors (__eo_typeof t) (Term.UOp UserOp.tuple)) = rhs :=
    tsp_requires_eq _ _ _ hReqNe
  have hSsNe :
      __dt_get_selectors (__eo_typeof t) (Term.UOp UserOp.tuple) ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hMk
    apply hRhsNe
    rw [← hMk]
    simp [__mk_dt_updater_elim_rhs]
  have hMk' :
      __tuple_updater_elim_rhs U
          (__dt_get_selectors (__eo_typeof t) (Term.UOp UserOp.tuple)) = rhs := by
    rw [← hMk]
    unfold __mk_dt_updater_elim_rhs
    split <;> simp_all [U]
  have hShape :
      ∃ T1 T2, __eo_typeof t =
        Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 :=
    tsp_dt_get_selectors_tuple_shape _ hSsNe
  rcases hShape with ⟨T1, T2, hT⟩
  rw [hT] at hMk'
  have hMk'' :
      __tuple_updater_elim_rhs U
          (__tuple_get_selectors_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
            (Term.Numeral 0)) = rhs := by
    simpa [__dt_get_selectors] using hMk'
  rcases tuple_updater_elim_rhs_spine nn t a _ 0
      (by rw [hMk'']; exact hRhsNe) with ⟨hs, hSp, hComp⟩
  rw [hMk''] at hSp
  exact ⟨hs, hSp, by intro j h hj; simpa using hComp j h hj⟩

/-- Semantic core of the tuple case of `dt-updater-elim`. -/
theorem tuple_updater_elim_eval_eq
    (M : SmtModel) (hM : model_wf M) (nn : Int) (t a r : Term)
    (hs : List Term) (hSp : TupleSpine r hs)
    (hComp : ∀ (j : Nat) (h : Term), hs[j]? = some h ->
      (nn = (j : Int) ∧ h = a) ∨
      (nn ≠ (j : Int) ∧
        h = Term.Apply
          (Term.UOp1 UserOp1.tuple_select (Term.Numeral (j : Int))) t))
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)) =
        __smtx_typeof (__eo_to_smt r))
    (hRNN : __smtx_typeof (__eo_to_smt r) ≠ SmtType.None) :
    __smtx_model_eval M (__eo_to_smt r) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)) := by
  have hUNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral nn)) t) a)) ≠
        SmtType.None := by
    rw [hTy]
    exact hRNN
  rcases tsp_tuple_update_shape_of_non_none (Term.Numeral nn) t a hUNN with
    ⟨d, n', hTTy, hIdx, hNonneg, hLt⟩
  cases hIdx
  rcases tupleSpine_eval_components M hM hSp hRNN with ⟨⟨c, hRTy⟩, hCount, _⟩
  have hUTy :=
    tsp_tuple_update_type_eq_tuple_type_of_shape (Term.Numeral nn) t a d nn
      hTTy rfl hNonneg hLt hUNN
  have hd : d = SmtDatatype.sum c SmtDatatype.null := by
    have h := hUTy.symm.trans (hTy.trans hRTy)
    simpa [__eo_to_smt_tuple_decl] using h
  subst hd
  have hUEval :=
    tsp_tuple_update_eval_eq_rec_of_tuple_type M hM (Term.Numeral nn) t a c nn
      hTTy rfl hNonneg hLt
  have hRecNN :=
    tsp_tuple_update_rec_non_none_of_shape (Term.Numeral nn) t a
      (SmtDatatype.sum c SmtDatatype.null) nn hTTy rfl hNonneg hLt hUNN
  rcases tsp_updater_rec_eval_components M hM (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
      native_nat_zero (native_int_to_nat nn)
      (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)
      (__eo_to_smt t) (__eo_to_smt a) hRecNN with
    ⟨_hUHead, hUCount, hUArgs⟩
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM _ hRNN, hRTy]
  have hLen :
      hs.length =
        __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) native_nat_zero := by
    rw [← hCount]
    exact tuple_value_count_of_type hREvalTy (tuple_value_head_zero_of_type hREvalTy)
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hTTy]
    simp
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM _ hTNN, hTTy]
  have hTHead := tuple_value_head_zero_of_type hTEvalTy
  have hTCount := tuple_value_count_of_type hTEvalTy hTHead
  apply tupleSpine_eval_eq M hM hSp hRNN
  · rw [smt_model_eval_preserves_type_of_non_none M hM _ hUNN, hTy]
  · intro j h hj
    have hjlt : j < hs.length := (List.getElem?_eq_some_iff.mp hj).1
    rw [hUEval, hUCount, hUArgs j (by rw [← hLen]; exact hjlt)]
    rcases hComp j h hj with ⟨hnj, hH⟩ | ⟨hnj, hH⟩
    · subst hH
      have hEqNat : native_nateq (native_int_to_nat nn) j = true := by
        simp [native_nateq, SmtEval.native_nateq, native_int_to_nat,
          SmtEval.native_int_to_nat, hnj]
      simp [hEqNat]
    · subst hH
      have hNeToNat : Int.toNat nn ≠ j := by
        intro h'
        apply hnj
        rw [← h']
        exact (Int.toNat_of_nonneg hNonneg).symm
      have hNeNat : native_nateq (native_int_to_nat nn) j = false := by
        simp [native_nateq, SmtEval.native_nateq, native_int_to_nat,
          SmtEval.native_int_to_nat, hNeToNat]
      simp [hNeNat]
      rw [tuple_select_numeral_eval M hM t c j hTTy,
        tuple_selector_eval_eq_arg M (SmtDatatype.sum c SmtDatatype.null)
          (__eo_to_smt t) j hTHead, hTCount]

theorem tuple_update_idx_numeral_of_non_none (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    ∃ nn : Int, idx = Term.Numeral nn := by
  intro hNN
  rcases tsp_tuple_update_shape_of_non_none idx t a hNN with
    ⟨_d, n, _hT, hIdx, _hNonneg, _hLt⟩
  exact ⟨n, hIdx⟩
