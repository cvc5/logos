module

public import Cpc.Proofs.TypePreservation.Common
import all Cpc.Proofs.TypePreservation.Common
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.SmtModel

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Rewrites the typing equation for `DtCons`. -/
theorem typeof_dt_cons_eq
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __smtx_typeof (SmtTerm.DtCons s d i) =
      __smtx_typeof_guard_wf (SmtType.Datatype s d)
        (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) := by
  simp [__smtx_typeof]

/-- Rewrites the typing equation for `DtSel` application. -/
theorem typeof_dt_sel_apply_eq
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i j : native_Nat)
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
      __smtx_typeof_guard_wf (__smtx_ret_typeof_sel s d i j)
        (__smtx_typeof_apply
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
          (__smtx_typeof x)) := by
  simp [__smtx_typeof]

/-- Rewrites the typing equation for `DtTester` application. -/
theorem typeof_dt_tester_apply_eq
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i : native_Nat)
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
      __smtx_typeof_guard
        (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i)
        (__smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) SmtType.Bool)
          (__smtx_typeof x)) := by
  simp [__smtx_typeof]

/-- Establishes an equality relating `typeof_dt_cons_value_rec` and `typeof_dt_cons_rec_zero`. -/
theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero
    (T : SmtType) :
    ∀ c d,
      __smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero =
        __smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec,
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d]

/-- Establishes an equality relating `typeof_dt_cons_value_rec` and `typeof_dt_cons_rec`. -/
theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
    (T : SmtType) :
    ∀ d n,
      __smtx_typeof_dt_cons_value_rec T d n =
        __smtx_typeof_dt_cons_rec T d n
  | SmtDatatype.null, n => by
      cases n <;> simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, native_nat_zero =>
      typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d
  | SmtDatatype.sum c d, native_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec] using
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec T d n

/-- If a constructor-value chain returns a datatype, it returns its own base datatype. -/
theorem typeof_dt_cons_value_rec_eq_base_datatype
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i s' d',
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i =
        SmtType.Datatype s' d' ->
      s = s' ∧ d0 = d'
  | SmtDatatype.null, i, s', d', h => by
      cases i <;> simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, s', d', h => by
      have h' : SmtType.Datatype s d0 = SmtType.Datatype s' d' := by
        simpa [__smtx_typeof_dt_cons_value_rec] using h
      injection h' with hs hd
      exact ⟨hs, hd⟩
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, s', d', h => by
      simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum c d, Nat.succ i, s', d', h => by
      have h' :
          __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i =
            SmtType.Datatype s' d' := by
        simpa [__smtx_typeof_dt_cons_value_rec] using h
      exact typeof_dt_cons_value_rec_eq_base_datatype s d0 d i s' d' h'

/-- Shows that evaluating `dt_cons` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_cons
    (M : SmtModel)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i : native_Nat)
    (ht : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s d i) := by
  simp [__smtx_model_eval]
  rw [typeof_dt_cons_eq]
  unfold term_has_non_none_type at ht
  rw [typeof_dt_cons_eq] at ht
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Datatype s d)
          (__smtx_typeof_dt_cons_rec
            (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) =
        __smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i :=
    smtx_typeof_guard_wf_of_non_none
      (SmtType.Datatype s d)
      (__smtx_typeof_dt_cons_rec
        (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i) ht
  rw [hGuard]
  simp [__smtx_typeof_value, typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]

/-- Definition used in the proof development for `dt_cons_type_num_args`. -/
def dt_cons_type_num_args : SmtType -> Nat
  | SmtType.FunType _ U => Nat.succ (dt_cons_type_num_args U)
  | SmtType.DtcAppType _ U => Nat.succ (dt_cons_type_num_args U)
  | _ => 0

/-- A completed datatype constructor type has no remaining arguments. -/
theorem dt_cons_type_num_args_datatype
    (s : native_String) (d : SmtDatatypeDecl) :
    dt_cons_type_num_args (SmtType.Datatype s d) = 0 := by
  rfl

/-- A function constructor type has one more argument than its result. -/
theorem dt_cons_type_num_args_fun_type
    (T U : SmtType) :
    dt_cons_type_num_args (SmtType.FunType T U) =
      Nat.succ (dt_cons_type_num_args U) := by
  rfl

/-- A datatype-constructor application type has one more argument than its result. -/
theorem dt_cons_type_num_args_dtc_app_type
    (T U : SmtType) :
    dt_cons_type_num_args (SmtType.DtcAppType T U) =
      Nat.succ (dt_cons_type_num_args U) := by
  rfl

/-- Definition used in the proof development for `dt_cons_applied_type_rec`. -/
def dt_cons_applied_type_rec
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    SmtDatatype -> Nat -> Nat -> SmtType
  | d, i, 0 => __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i
  | SmtDatatype.sum (SmtDatatypeCons.cons _ c) d, 0, Nat.succ n =>
      dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
  | SmtDatatype.sum c d, Nat.succ i, n =>
      dt_cons_applied_type_rec s d0 d i n
  | _, _, _ => SmtType.None

/-- Applying no constructor arguments leaves the original constructor-value type. -/
theorem dt_cons_applied_type_rec_zero
    (s : native_String) (d0 : SmtDatatypeDecl) (d : SmtDatatype) (i : Nat) :
    dt_cons_applied_type_rec s d0 d i 0 =
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i := by
  cases d <;> cases i <;>
    simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]

/-- Applying one argument consumes the leading field of a constructor. -/
theorem dt_cons_applied_type_rec_cons_succ
    (s : native_String) (d0 : SmtDatatypeDecl) (T : SmtType)
    (c : SmtDatatypeCons) (d : SmtDatatype) (n : Nat) :
    dt_cons_applied_type_rec s d0
        (SmtDatatype.sum (SmtDatatypeCons.cons T c) d) 0 (Nat.succ n) =
      dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n := by
  simp [dt_cons_applied_type_rec]

/-- Constructor lookup in an empty datatype always fails. -/
theorem dt_cons_applied_type_rec_null
    (s : native_String) (d0 : SmtDatatypeDecl) (i n : Nat) :
    dt_cons_applied_type_rec s d0 SmtDatatype.null i n = SmtType.None := by
  cases i <;> cases n <;>
    simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]

/-- Rewrites constructor-type lookup past an outer constructor when the index is positive. -/
theorem dt_cons_applied_type_rec_succ
    (s : native_String)
    (d0 : SmtDatatypeDecl)
    (c : SmtDatatypeCons)
    (d : SmtDatatype)
    (i n : Nat) :
    dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) (Nat.succ i) n =
      dt_cons_applied_type_rec s d0 d i n := by
  cases n <;> simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec]

/-- `dt_cons_applied_type_rec_succ` in the `i + 1` normal form Lean often chooses. -/
theorem dt_cons_applied_type_rec_add_one
    (s : native_String)
    (d0 : SmtDatatypeDecl)
    (c : SmtDatatypeCons)
    (d : SmtDatatype)
    (i n : Nat) :
    dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) (i + 1) n =
      dt_cons_applied_type_rec s d0 d i n := by
  simpa [Nat.succ_eq_add_one] using
    dt_cons_applied_type_rec_succ s d0 c d i n

/-- Lemma about `dt_cons_type_num_args_typeof_dt_cons_value_rec`. -/
theorem dt_cons_type_num_args_typeof_dt_cons_value_rec
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i,
      dt_cons_type_num_args (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i) =
        __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;>
        simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0 => by
      simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0 => by
      simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        __smtx_dtc_num_sels,
        dt_cons_type_num_args_typeof_dt_cons_value_rec s d0 (SmtDatatype.sum c d) 0]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        dt_cons_type_num_args_typeof_dt_cons_value_rec s d0 d i]

/-- Lemma about `dt_cons_type_num_args_dt_cons_applied_type_rec`. -/
theorem dt_cons_type_num_args_dt_cons_applied_type_rec
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i n,
      dt_cons_type_num_args (dt_cons_applied_type_rec s d0 d i n) = __smtx_dt_num_sels d i - n
  | d, i, 0 => by
      simp [dt_cons_applied_type_rec, dt_cons_type_num_args_typeof_dt_cons_value_rec]
  | SmtDatatype.null, i, Nat.succ n => by
      cases i <;>
        simp [dt_cons_applied_type_rec, dt_cons_type_num_args, __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n => by
      simp [dt_cons_applied_type_rec, dt_cons_type_num_args, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n => by
      have ih := dt_cons_type_num_args_dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
      simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_dtc_num_sels] using ih
  | SmtDatatype.sum c d, Nat.succ i, n => by
      cases n with
      | zero =>
          simp [dt_cons_applied_type_rec, dt_cons_type_num_args_typeof_dt_cons_value_rec,
            __smtx_dt_num_sels]
      | succ n =>
          have ih := dt_cons_type_num_args_dt_cons_applied_type_rec s d0 d i (Nat.succ n)
          simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels] using ih

/-- Lemma about `dt_cons_applied_type_rec_step`. -/
theorem dt_cons_applied_type_rec_step
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i n,
      n < __smtx_dt_num_sels d i ->
      dt_cons_applied_type_rec s d0 d i n =
        SmtType.DtcAppType (__smtx_ret_typeof_sel_rec d i n) (dt_cons_applied_type_rec s d0 d i (Nat.succ n))
  | SmtDatatype.null, i, n, hlt => by
      cases i <;> simp [__smtx_dt_num_sels] at hlt
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, n, hlt => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hlt
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, 0, hlt => by
      simp [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, hlt => by
      have hlt' : n < __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := by
        simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using hlt
      simpa [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec] using
        dt_cons_applied_type_rec_step s d0 (SmtDatatype.sum c d) 0 n hlt'
  | SmtDatatype.sum c d, Nat.succ i, n, hlt => by
      have hlt' : n < __smtx_dt_num_sels d i := by
        simpa [__smtx_dt_num_sels] using hlt
      cases n with
      | zero =>
          simpa [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec,
            __smtx_ret_typeof_sel_rec] using
            dt_cons_applied_type_rec_step s d0 d i 0 hlt'
      | succ n =>
          simpa [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec] using
            dt_cons_applied_type_rec_step s d0 d i (Nat.succ n) hlt'

/-- Shows that `dt_cons_applied_type_rec_non_none` implies `le`. -/
theorem dt_cons_applied_type_rec_non_none_implies_le
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i n,
      dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None ->
      n ≤ __smtx_dt_num_sels d i
  | d, i, 0, h => by
      simp
  | SmtDatatype.null, i, Nat.succ n, h => by
      cases i <;> simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n, h => by
      simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, h => by
      have ih := dt_cons_applied_type_rec_non_none_implies_le s d0 (SmtDatatype.sum c d) 0 n
      have h' : dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n ≠ SmtType.None := by
        simpa [dt_cons_applied_type_rec] using h
      have hle : n ≤ __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := ih h'
      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using Nat.succ_le_succ hle
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      cases n with
      | zero =>
          simp [__smtx_dt_num_sels]
      | succ n =>
          have ih := dt_cons_applied_type_rec_non_none_implies_le s d0 d i (Nat.succ n)
          have h' : dt_cons_applied_type_rec s d0 d i (Nat.succ n) ≠ SmtType.None := by
            simpa [dt_cons_applied_type_rec] using h
          have hle : Nat.succ n ≤ __smtx_dt_num_sels d i := ih h'
          simpa [__smtx_dt_num_sels] using hle

/-- Fully applying a well-typed datatype constructor chain yields its base datatype. -/
theorem dt_cons_applied_type_rec_full_arity
    (s : native_String)
    (d0 : SmtDatatypeDecl) :
    ∀ d i,
      dt_cons_applied_type_rec s d0 d i (__smtx_dt_num_sels d i) ≠ SmtType.None ->
      dt_cons_applied_type_rec s d0 d i (__smtx_dt_num_sels d i) = SmtType.Datatype s d0
  | SmtDatatype.null, i, h => by
      cases i <;>
        simp [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_typeof_dt_cons_value_rec] at h ⊢
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, h => by
      simp [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_dtc_num_sels,
        __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, h => by
      have h' :
          dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0
              (__smtx_dt_num_sels (SmtDatatype.sum c d) 0) ≠
            SmtType.None := by
        simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_dtc_num_sels] using h
      simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_dtc_num_sels] using
        dt_cons_applied_type_rec_full_arity s d0 (SmtDatatype.sum c d) 0 h'
  | SmtDatatype.sum c d, Nat.succ i, h => by
      have h1 := h
      rw [show __smtx_dt_num_sels (SmtDatatype.sum c d) (Nat.succ i) = __smtx_dt_num_sels d i by
        rfl] at h1
      have h' : dt_cons_applied_type_rec s d0 d i (__smtx_dt_num_sels d i) ≠ SmtType.None := by
        rw [dt_cons_applied_type_rec_add_one s d0 c d i (__smtx_dt_num_sels d i)] at h1
        exact h1
      rw [show __smtx_dt_num_sels (SmtDatatype.sum c d) (Nat.succ i) = __smtx_dt_num_sels d i by
        rfl]
      rw [dt_cons_applied_type_rec_add_one s d0 c d i (__smtx_dt_num_sels d i)]
      exact dt_cons_applied_type_rec_full_arity s d0 d i h'

/-- Shows that `dt_cons_applied_type_rec_eq_bare_type` implies `zero`. -/
theorem dt_cons_applied_type_rec_eq_bare_type_implies_zero
    {s : native_String}
    {d0 : SmtDatatypeDecl}
    {i n : Nat}
    (hEq :
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) (__smtx_dt_resolve (__smtx_dd_lookup s d0) d0) i =
        dt_cons_applied_type_rec s d0 (__smtx_dt_resolve (__smtx_dd_lookup s d0) d0) i n)
    (hNN : dt_cons_applied_type_rec s d0 (__smtx_dt_resolve (__smtx_dd_lookup s d0) d0) i n ≠ SmtType.None) :
    n = 0 := by
  have hArgs := congrArg dt_cons_type_num_args hEq
  rw [dt_cons_type_num_args_typeof_dt_cons_value_rec,
    dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
  have hle :
      n ≤ __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d0) d0) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d0 (__smtx_dt_resolve (__smtx_dd_lookup s d0) d0) i n hNN
  omega

/-- Definition used in the proof development for `vsm_num_apply_args`. -/
def vsm_num_apply_args : SmtValue -> Nat
  | SmtValue.Apply f _ => Nat.succ (vsm_num_apply_args f)
  | _ => 0

/-- A bare datatype constructor value has no applied arguments. -/
theorem vsm_num_apply_args_dt_cons
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    vsm_num_apply_args (SmtValue.DtCons s d i) = 0 := by
  rfl

/-- An application value has one more applied argument than its head. -/
theorem vsm_num_apply_args_apply (f x : SmtValue) :
    vsm_num_apply_args (SmtValue.Apply f x) =
      Nat.succ (vsm_num_apply_args f) := by
  rfl

/-- Resolving constructor fields preserves the selector count. -/
theorem dtc_num_sels_resolve
    (dd : SmtDatatypeDecl) :
    ∀ c, __smtx_dtc_num_sels (__smtx_dtc_resolve c dd) = __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_resolve, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      cases T <;>
        simp [__smtx_dtc_resolve, __smtx_dtc_num_sels,
          dtc_num_sels_resolve dd c]

/-- Resolving a datatype preserves selector counts. -/
theorem dt_num_sels_resolve
    (dd : SmtDatatypeDecl) :
    ∀ d i, __smtx_dt_num_sels (__smtx_dt_resolve d dd) i = __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_dt_resolve, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, 0 => by
      simp [__smtx_dt_resolve, __smtx_dt_num_sels, dtc_num_sels_resolve]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_dt_resolve, __smtx_dt_num_sels, dt_num_sels_resolve dd d i]

/-- Shows that `ret_typeof_sel_rec_non_none` implies `lt`. -/
theorem ret_typeof_sel_rec_non_none_implies_lt :
    ∀ d i j,
      __smtx_ret_typeof_sel_rec d i j ≠ SmtType.None ->
      j < __smtx_dt_num_sels d i
  | SmtDatatype.null, i, j, h => by
      cases i <;> cases j <;> simp [__smtx_ret_typeof_sel_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, j, h => by
      cases j <;> simp [__smtx_ret_typeof_sel_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, 0, 0, h => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, 0, Nat.succ j, h => by
      have h' : __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) 0 j ≠ SmtType.None := by
        simpa [__smtx_ret_typeof_sel_rec] using h
      have ih := ret_typeof_sel_rec_non_none_implies_lt (SmtDatatype.sum c d) 0 j h'
      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using Nat.succ_lt_succ ih
  | SmtDatatype.sum c d, Nat.succ i, j, h => by
      have h' : __smtx_ret_typeof_sel_rec d i j ≠ SmtType.None := by
        simpa [__smtx_ret_typeof_sel_rec] using h
      have ih := ret_typeof_sel_rec_non_none_implies_lt d i j h'
      simpa [__smtx_dt_num_sels] using ih

/-- Enumerates the cases for `typeof_apply_value_non_none`. -/
theorem typeof_apply_value_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply_value F X ≠ SmtType.None) :
    ∃ A B,
      F = SmtType.DtcAppType A B ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | DtcAppType A B =>
      cases X <;>
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, rfl, h.2.1.symm, h.1, h.2.2⟩
  | _ =>
      simp [__smtx_typeof_apply_value] at h

/-- Derives `dt_cons_chain_type` from `non_none`. -/
theorem dt_cons_chain_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat},
      __smtx_apply_head_value v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      __smtx_typeof_value v =
        dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args v)
  | SmtValue.NotValue, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean b, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral n, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational q, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary w n, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map m, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq ss, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char c, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue k e, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan r, s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, hHead, hNN => by
      simp [__smtx_apply_head_value] at hHead
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      cases hWf : __smtx_type_wf (SmtType.Datatype s' d') <;>
        simp [__smtx_typeof_value, dt_cons_applied_type_rec, vsm_num_apply_args] at hNN ⊢
  | SmtValue.Apply f a, s, d, i, hHead, hNN => by
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons s d i := by
        simpa [__smtx_apply_head_value] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone, __smtx_typeof_apply_value]
      have ihEq := dt_cons_chain_type_of_non_none hHeadF hFunNN
      have hApplyNN :
          __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) ≠ SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone]
      rcases typeof_apply_value_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have hFunEq :
          dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f) =
            SmtType.DtcAppType A B := by
        simpa [ihEq] using hF
      have hArgs :
          Nat.succ (dt_cons_type_num_args B) =
            __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i - vsm_num_apply_args f := by
        have hArgs := congrArg dt_cons_type_num_args hFunEq
        rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
        simpa [dt_cons_type_num_args] using hArgs.symm
      have hlt :
          vsm_num_apply_args f < __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
        omega
      have hStep := dt_cons_applied_type_rec_step s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
        (vsm_num_apply_args f) hlt
      have hB' :
          B =
            dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f)) := by
        have hCmp :
            SmtType.DtcAppType A B =
              SmtType.DtcAppType
                (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                (dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f))) := by
          calc
            SmtType.DtcAppType A B =
                dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f) := hFunEq.symm
            _ =
                SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f))) := hStep
        injection hCmp with _ hB''
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq,
        __smtx_typeof_value, hF, hX, hA, vsm_num_apply_args, hB']

/-- Derives `vsm_num_apply_args_eq_dt_num_sels` from `datatype`. -/
theorem vsm_num_apply_args_eq_dt_num_sels_of_datatype
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    (hHead : __smtx_apply_head_value v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by simp [hTy])
  have hEq :
      dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args v) =
        SmtType.Datatype s d := by
    calc
      dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args v) =
          __smtx_typeof_value v := by symm; exact hChain
      _ = SmtType.Datatype s d := hTy
  have hArgs := congrArg dt_cons_type_num_args hEq
  rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
  simp [dt_cons_type_num_args] at hArgs
  have hle :
      vsm_num_apply_args v ≤ __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      (vsm_num_apply_args v) (by rw [hEq]; simp)
  omega

/-- Empty datatypes have no semantic values. -/
theorem no_value_of_empty_datatype
    (s : native_String) {dd : SmtDatatypeDecl}
    (hLk : __smtx_dd_lookup s dd = SmtDatatype.null) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.Datatype s dd := by
  intro h
  rcases h with ⟨v, hv⟩
  cases v with
  | NotValue =>
      simp [__smtx_typeof_value] at hv
  | Boolean _ =>
      simp [__smtx_typeof_value] at hv
  | Numeral _ =>
      simp [__smtx_typeof_value] at hv
  | Rational _ =>
      simp [__smtx_typeof_value] at hv
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at hv
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hv
  | Fun fid A B =>
      simp [__smtx_typeof_value] at hv
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hv
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hv
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at hv
  | UValue _ _ =>
      simp [__smtx_typeof_value] at hv
  | RegLan _ =>
      simp [__smtx_typeof_value] at hv
  | DtCons s' d i =>
      have hBase :
          s' = s ∧ d = dd :=
        typeof_dt_cons_value_rec_eq_base_datatype s' d
          (__smtx_dt_resolve (__smtx_dd_lookup s' d) d) i
          s dd (by simpa [__smtx_typeof_value] using hv)
      rcases hBase with ⟨hs, hd⟩
      subst hs
      subst hd
      simp [__smtx_typeof_value, hLk, __smtx_dt_resolve,
        __smtx_typeof_dt_cons_value_rec] at hv
  | Apply f x =>
      have hNN : __smtx_typeof_value (SmtValue.Apply f x) ≠ SmtType.None := by
        intro hNone
        rw [hNone] at hv
        simp at hv
      by_cases hDt : ∃ s0 d0 i, __smtx_apply_head_value f = SmtValue.DtCons s0 d0 i
      · rcases hDt with ⟨s0, d0, i, hHead⟩
        have hHeadApply : __smtx_apply_head_value (SmtValue.Apply f x) = SmtValue.DtCons s0 d0 i := by
          simpa [__smtx_apply_head_value] using hHead
        have hRes :
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
                (vsm_num_apply_args (SmtValue.Apply f x)) =
              SmtType.Datatype s dd := by
          exact (dt_cons_chain_type_of_non_none hHeadApply hNN).symm.trans hv
        have hArgs :
            __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i -
              vsm_num_apply_args (SmtValue.Apply f x) =
            0 := by
          have hArgs := congrArg dt_cons_type_num_args hRes
          rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
          simpa [dt_cons_type_num_args] using hArgs
        have hle :
            vsm_num_apply_args (SmtValue.Apply f x) ≤
              __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i :=
          dt_cons_applied_type_rec_non_none_implies_le s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
            (vsm_num_apply_args (SmtValue.Apply f x)) (by rw [hRes]; simp)
        have hCount :
            vsm_num_apply_args (SmtValue.Apply f x) =
              __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i := by
          have hge :
              __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i ≤
                vsm_num_apply_args (SmtValue.Apply f x) :=
            (Nat.sub_eq_zero_iff_le).1 hArgs
          exact Nat.le_antisymm hge hle |> Eq.symm
        have hFull :
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
                (__smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i) =
              SmtType.Datatype s0 d0 :=
          dt_cons_applied_type_rec_full_arity s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
            (by rw [← hCount, hRes]; simp)
        have hBase :
            SmtType.Datatype s0 d0 = SmtType.Datatype s dd := by
          calc
            SmtType.Datatype s0 d0 =
                dt_cons_applied_type_rec s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
                  (__smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i) := by
              symm
              exact hFull
            _ =
                dt_cons_applied_type_rec s0 d0 (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
                  (vsm_num_apply_args (SmtValue.Apply f x)) := by rw [hCount]
            _ = SmtType.Datatype s dd := hRes
        injection hBase with hs hd
        have hLk0 : __smtx_dd_lookup s0 d0 = SmtDatatype.null := by
          rw [hs, hd]; exact hLk
        have hCount0 : vsm_num_apply_args (SmtValue.Apply f x) = 0 := by
          simpa [hLk0, __smtx_dt_resolve, __smtx_dt_num_sels] using hCount
        have hNone :
            dt_cons_applied_type_rec s0 d0
                (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i
                (vsm_num_apply_args (SmtValue.Apply f x)) =
              SmtType.None := by
          simp [hCount0, dt_cons_applied_type_rec, hLk0, __smtx_dt_resolve,
            __smtx_typeof_dt_cons_value_rec]
        rw [hNone] at hRes
        simp at hRes
      · exact hNN <|
          typeof_value_apply_of_head_ne_dt_cons f x
            (by
              intro s0 d0 i hm
              exact hDt ⟨s0, d0, i, hm⟩)

/-- Walks the declaration list to extract dt-level well-formedness of the named datatype. -/
theorem decl_wf_rec_lookup
    (s : native_String) (dd : SmtDatatypeDecl) :
    ∀ dd2, __smtx_dd_has_dt s dd2 = true →
      __smtx_decl_wf_rec dd dd2 = true →
      __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd2) = true
  | SmtDatatypeDecl.nil, hHas, _ => by
      simp [__smtx_dd_has_dt] at hHas
  | SmtDatatypeDecl.cons s2 d2 dd2, hHas, h => by
      by_cases hs : native_streq s s2 = true
      · have hDt : __smtx_dt_wf_rec dd d2 = true := by
          simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
          exact h.1
        simpa [__smtx_dd_lookup, native_ite, hs] using hDt
      · have hHasTail : __smtx_dd_has_dt s dd2 = true := by
          simpa [__smtx_dd_has_dt, native_or, hs] using hHas
        have hTail : __smtx_decl_wf_rec dd dd2 = true := by
          simp only [__smtx_decl_wf_rec, native_and, Bool.and_eq_true] at h
          exact h.2.2.1
        simpa [__smtx_dd_lookup, native_ite, hs] using
          decl_wf_rec_lookup s dd dd2 hHasTail hTail

/-- Extracts recursive datatype well-formedness from public type well-formedness. -/
theorem datatype_wf_rec_of_type_wf
    {s : native_String}
    {dd : SmtDatatypeDecl}
    (h : __smtx_type_wf (SmtType.Datatype s dd) = true) :
    __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true := by
  have hPair :
      native_inhabited_type (SmtType.Datatype s dd) = true ∧
        (__smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact decl_wf_rec_lookup s dd dd hPair.2.1 hPair.2.2

/-- Empty datatypes are uninhabited. -/
theorem not_type_inhabited_empty_datatype
    (s : native_String) {dd : SmtDatatypeDecl}
    (hLk : __smtx_dd_lookup s dd = SmtDatatype.null) :
    ¬ type_inhabited (SmtType.Datatype s dd) := by
  intro h
  exact no_value_of_empty_datatype s hLk h

/-- Derives `apply_arg_nth_type` from `non_none`. -/
theorem apply_arg_nth_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat},
      __smtx_apply_head_value v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      j < vsm_num_apply_args v ->
      __smtx_typeof_value (__smtx_apply_arg_nth_value v j (vsm_num_apply_args v)) =
        __smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j
  | SmtValue.NotValue, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Boolean b, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Numeral n, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Rational q, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Binary w n, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Map m, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Fun _ _ _, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Seq ss, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.Char c, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.UValue k e, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.RegLan r, s, d, i, j, hHead, hNN, hj => by
      simp [__smtx_apply_head_value] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, j, hHead, hNN, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Apply f a, s, d, i, j, hHead, hNN, hj => by
      have hHeadF : __smtx_apply_head_value f = SmtValue.DtCons s d i := by
        simpa [__smtx_apply_head_value] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone, __smtx_typeof_apply_value]
      have hChainF := dt_cons_chain_type_of_non_none hHeadF hFunNN
      have hChainV := dt_cons_chain_type_of_non_none hHead hNN
      have hSuccNN :
          dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f)) ≠
            SmtType.None := by
        intro hNone
        apply hNN
        rw [hChainV]
        simpa [vsm_num_apply_args] using hNone
      have hle :
          Nat.succ (vsm_num_apply_args f) ≤ __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i :=
        dt_cons_applied_type_rec_non_none_implies_le s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (Nat.succ (vsm_num_apply_args f)) hSuccNN
      have hlt :
          vsm_num_apply_args f < __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
        omega
      have hStepF := dt_cons_applied_type_rec_step s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
        (vsm_num_apply_args f) hlt
      by_cases hLast : j = vsm_num_apply_args f
      · subst hLast
        have hTyEq :
            __smtx_typeof_apply_value
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f)) := by
          calc
            __smtx_typeof_apply_value
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) := by
                rw [hChainF, hStepF]
            _ = __smtx_typeof_value (SmtValue.Apply f a) := by
                simp [__smtx_typeof_value]
            _ = dt_cons_applied_type_rec s d (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (Nat.succ (vsm_num_apply_args f)) := by
                simpa [vsm_num_apply_args] using hChainV
        have hArgTy :
            __smtx_typeof_value a =
              __smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f) := by
          by_cases hRNone :
              native_Teq
                (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                SmtType.None
          · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hRNone] at hTyEq
            exact (hSuccNN hTyEq.symm).elim
          · by_cases hEq :
                native_Teq
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f))
                  (__smtx_typeof_value a)
            · have hEq' :
                  __smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i (vsm_num_apply_args f) =
                    __smtx_typeof_value a := by
                simpa [native_Teq] using hEq
              exact hEq'.symm
            · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hRNone, hEq] at hTyEq
              exact (hSuccNN hTyEq.symm).elim
        have hcond : Smtm.native_nateq (vsm_num_apply_args f) (vsm_num_apply_args f) = true := by
          simp [Smtm.native_nateq]
        simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, native_ite, hcond] using hArgTy
      · have hjSucc : j < Nat.succ (vsm_num_apply_args f) := by
          simpa [vsm_num_apply_args] using hj
        have hj' : j < vsm_num_apply_args f := by
          have hle : j ≤ vsm_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle with
          | inl hEq =>
              exact False.elim (hLast hEq)
          | inr hLt =>
              exact hLt
        have hcond : Smtm.native_nateq j (vsm_num_apply_args f) = false := by
          simp [Smtm.native_nateq, hLast]
        simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, native_ite, hcond] using
          apply_arg_nth_type_of_non_none hHeadF hFunNN hj'

/-- Derives `dt_sel_arg_datatype` from `non_none`. -/
theorem dt_sel_arg_datatype_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner := __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hGuard : __smtx_typeof_guard_wf R inner = inner :=
    smtx_typeof_guard_wf_of_non_none R inner hGuardNN
  have hInnerNN : inner ≠ SmtType.None := by
    intro hNone
    apply hGuardNN
    rw [hGuard, hNone]
  by_cases hTypeEq : SmtType.Datatype s d = __smtx_typeof x
  · exact hTypeEq.symm
  · exfalso
    apply hInnerNN
    simp [inner, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hTypeEq]

/-- Derives `dt_sel_term_typeof` from `non_none`. -/
theorem dt_sel_term_typeof_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = __smtx_ret_typeof_sel s d i j := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_sel_arg_datatype_of_non_none ht
  let R := __smtx_ret_typeof_sel s d i j
  let inner := __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hGuard : __smtx_typeof_guard_wf R inner = inner :=
    smtx_typeof_guard_wf_of_non_none R inner hGuardNN
  calc
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        inner := by
      rw [typeof_dt_sel_apply_eq]
      simpa [R, inner] using hGuard
    _ = __smtx_ret_typeof_sel s d i j := by
      simp [inner, R, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hx]

/-- The well-formed fallback map for a datatype selector induces a well-formed
function type for its final lookup. -/
theorem dt_sel_wrong_fun_type_wf_of_map_wf
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i j : native_Nat)
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true) :
    __smtx_type_wf
      (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)) = true := by
  let D := SmtType.Datatype s d
  let R := __smtx_ret_typeof_sel s d i j
  have hM2WF :
      __smtx_type_wf (SmtType.Map SmtType.Int (SmtType.Map D R)) = true :=
    (map_type_wf_components_of_wf (A := SmtType.Int)
      (B := SmtType.Map SmtType.Int (SmtType.Map D R))
      (by simpa [D, R] using hMapWF)).2
  have hM3WF : __smtx_type_wf (SmtType.Map D R) = true :=
    (map_type_wf_components_of_wf (A := SmtType.Int)
      (B := SmtType.Map D R) hM2WF).2
  have hAll :
      native_inhabited_type (SmtType.Map D R) = true ∧
        ((native_inhabited_type D = true ∧ __smtx_type_wf_rec D = true) ∧
          (native_inhabited_type R = true ∧ __smtx_type_wf_rec R = true)) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using hM3WF
  have hRWF : __smtx_type_wf R = true :=
    type_wf_of_inhabited_and_wf_rec hAll.2.2.1 hAll.2.2.2
  change
    native_and (__smtx_type_wf_component D) (__smtx_type_wf R) = true
  simp [native_and,
    smtx_type_wf_component_of_parts hAll.2.1.1 hAll.2.1.2, hRWF]

/-- Shows that evaluating `dt_sel_wrong` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_sel_wrong
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i j : native_Nat)
    (v : SmtValue)
    (hT : type_inhabited (__smtx_ret_typeof_sel s d i j))
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
    (hv : __smtx_typeof_value v = SmtType.Datatype s d) :
    __smtx_typeof_value
      (__smtx_model_eval_apply M
        (native_model_lookup M (native_wrong_apply_sel_id i j)
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))
        v) = __smtx_ret_typeof_sel s d i j := by
  let D := SmtType.Datatype s d
  let R := __smtx_ret_typeof_sel s d i j
  have hM2WF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int (SmtType.Map D R)) = true := by
    exact (map_type_wf_components_of_wf (A := SmtType.Int)
      (B := SmtType.Map SmtType.Int (SmtType.Map D R))
      (by simpa [D, R] using hMapWF)).2
  have hM3WF : __smtx_type_wf (SmtType.Map D R) = true := by
    exact (map_type_wf_components_of_wf (A := SmtType.Int)
      (B := SmtType.Map D R) hM2WF).2
  have hDRParts :
      native_inhabited_type D = true ∧
        __smtx_type_wf_rec D = true ∧
          native_inhabited_type R = true ∧
            __smtx_type_wf_rec R = true := by
    have hAll :
        native_inhabited_type (SmtType.Map D R) = true ∧
          ((native_inhabited_type D = true ∧ __smtx_type_wf_rec D = true) ∧
            (native_inhabited_type R = true ∧ __smtx_type_wf_rec R = true)) := by
      simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        native_and] using hM3WF
    exact ⟨hAll.2.1.1, hAll.2.1.2, hAll.2.2.1, hAll.2.2.2⟩
  have hDParts :
      native_inhabited_type D = true ∧
        __smtx_type_wf_rec D = true :=
    ⟨hDRParts.1, hDRParts.2.1⟩
  have hRParts :
      native_inhabited_type R = true ∧
        __smtx_type_wf_rec R = true :=
    ⟨hDRParts.2.2.1, hDRParts.2.2.2⟩
  have hRWF : __smtx_type_wf R = true :=
    type_wf_of_inhabited_and_wf_rec hRParts.1 hRParts.2
  have hFunWF : __smtx_type_wf (SmtType.FunType D R) = true := by
    simp [__smtx_type_wf, __smtx_type_wf_component, native_and, hDParts.1, hDParts.2,
      hRWF]
  have hLookup :
      __smtx_typeof_value
        (native_model_lookup M (native_wrong_apply_sel_id i j) (SmtType.FunType D R)) =
          SmtType.FunType D R := by
    simpa [D, R] using
      model_total_typed_lookup hM (native_wrong_apply_sel_id i j)
        (SmtType.FunType D R) hFunWF
  generalize hfDef :
    native_model_lookup M (native_wrong_apply_sel_id i j) (SmtType.FunType D R) = f
  have hf : __smtx_typeof_value f = SmtType.FunType D R := by
    simpa [← hfDef] using hLookup
  have hvD : __smtx_typeof_value v = D := by
    simpa [D] using hv
  change __smtx_typeof_value (__smtx_model_eval_apply M f v) = R
  rcases fun_value_canonical hf with ⟨fid, rfl⟩
  have hvNN : v ≠ SmtValue.NotValue := by
    intro h
    subst v
    simp [D, __smtx_typeof_value] at hvD
  have hApply :
      __smtx_model_eval_apply M (SmtValue.Fun fid D R) v =
        native_eval_fun_apply M fid D R v := by
    cases v <;> simp [__smtx_model_eval_apply] at hvNN ⊢
  rw [hApply]
  exact (model_total_typed_native_fun_typed hM fid D R v hFunWF hvD).1

/-- Shows that evaluating `dt_sel` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_sel
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i j : native_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hWrongMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
    (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
    (hpresx : __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_sel_arg_datatype_of_non_none ht
  have hResTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        __smtx_ret_typeof_sel s d i j :=
    dt_sel_term_typeof_of_non_none ht
  have hResInh : type_inhabited (__smtx_ret_typeof_sel s d i j) := by
    rw [← hResTy]
    exact hT
  simp [__smtx_model_eval]
  rw [hResTy]
  let v := __smtx_model_eval M x
  have hv : __smtx_typeof_value v = SmtType.Datatype s d := by
    unfold v
    rw [hpresx, hx]
  unfold __smtx_model_eval_dt_sel
  by_cases hHead :
      native_veq (__smtx_apply_head_value v) (SmtValue.DtCons s d i)
  · have hHeadEq : __smtx_apply_head_value v = SmtValue.DtCons s d i := by
      simpa [native_veq] using hHead
    have hCountSub :
        vsm_num_apply_args v =
          __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i :=
      vsm_num_apply_args_eq_dt_num_sels_of_datatype hHeadEq hv
    have hCount : vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dd_lookup s d) i := by
      rw [dt_num_sels_resolve d (__smtx_dd_lookup s d) i] at hCountSub
      exact hCountSub
    have hSelNN : __smtx_ret_typeof_sel s d i j ≠ SmtType.None := by
      rw [← hResTy]
      exact ht
    have hltSel :
        j < __smtx_dt_num_sels (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
      exact ret_typeof_sel_rec_non_none_implies_lt
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j (by simpa [__smtx_ret_typeof_sel] using hSelNN)
    have hj : j < vsm_num_apply_args v := by
      simpa [hCountSub] using hltSel
    have hArgTy :
        __smtx_typeof_value (__smtx_apply_arg_nth_value v j (vsm_num_apply_args v)) =
          __smtx_ret_typeof_sel_rec (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j :=
      apply_arg_nth_type_of_non_none hHeadEq (by simp [hv]) hj
    have hArgTy' :
        __smtx_typeof_value
            (__smtx_apply_arg_nth_value v j (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) =
          __smtx_ret_typeof_sel s d i j := by
      simpa [__smtx_ret_typeof_sel, hCount] using hArgTy
    simpa [v, native_ite, hHead] using hArgTy'
  · simpa [v, native_ite, hHead] using
      typeof_value_model_eval_dt_sel_wrong M hM s d i j v hResInh hWrongMapWF hv

/-- Derives `dt_tester_arg_datatype` from `non_none`. -/
theorem dt_tester_arg_datatype_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  unfold term_has_non_none_type at ht
  rw [typeof_dt_tester_apply_eq] at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, h] at ht ⊢
  case Datatype s' d' =>
    rcases ht with ⟨_hCtor, hs, hd⟩
    exact ⟨hs.symm, hd.symm⟩

/-- Derives valid tester constructor typing from `non_none`. -/
theorem dt_tester_ctor_type_non_none_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i ≠
      SmtType.None := by
  unfold term_has_non_none_type at ht
  rw [typeof_dt_tester_apply_eq] at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, h] at ht
  case Datatype _s' _d' =>
    exact ht.1

/-- Derives `dt_tester_term_typeof` from `non_none`. -/
theorem dt_tester_term_typeof_of_non_none
    {s : native_String}
    {d : SmtDatatypeDecl}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) = SmtType.Bool := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_tester_arg_datatype_of_non_none ht
  have hCtor : __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i ≠
      SmtType.None :=
    dt_tester_ctor_type_non_none_of_non_none ht
  rw [typeof_dt_tester_apply_eq]
  simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hx, hCtor]

/-- Shows that evaluating `dt_tester` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_tester
    (M : SmtModel)
    (s : native_String)
    (d : SmtDatatypeDecl)
    (i : native_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  simp [__smtx_model_eval]
  simp [__smtx_model_eval_dt_tester, __smtx_typeof_value]

/-- Enumerates the cases for `typeof_apply_non_none`. -/
theorem typeof_apply_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply F X ≠ SmtType.None) :
    ∃ A B,
      (F = SmtType.FunType A B ∨
        F = SmtType.DtcAppType A B) ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | None => simp [__smtx_typeof_apply] at h
  | Bool => simp [__smtx_typeof_apply] at h
  | Int => simp [__smtx_typeof_apply] at h
  | Real => simp [__smtx_typeof_apply] at h
  | RegLan => simp [__smtx_typeof_apply] at h
  | BitVec w => simp [__smtx_typeof_apply] at h
  | Set T => simp [__smtx_typeof_apply] at h
  | Seq T => simp [__smtx_typeof_apply] at h
  | Char => simp [__smtx_typeof_apply] at h
  | Datatype s d => simp [__smtx_typeof_apply] at h
  | TypeRef s => simp [__smtx_typeof_apply] at h
  | USort n => simp [__smtx_typeof_apply] at h
  | Map A B =>
      simp [__smtx_typeof_apply] at h
  | FunType A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inl rfl, h.2.1.symm, h.1, h.2.2⟩
  | DtcAppType A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inr rfl, h.2.1.symm, h.1, h.2.2⟩

/-- Shows that evaluating `apply_fun` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_fun
    (M : SmtModel)
    (hM : model_wf M)
    {fid : native_String}
    {i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply M (SmtValue.Fun fid A B) i) = B := by
  have hArg : native_Teq (__smtx_typeof_value i) A = true := by
    simp [native_Teq, hi]
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  have hApply :
      __smtx_model_eval_apply M (SmtValue.Fun fid A B) i =
        native_eval_fun_apply M fid A B i := by
    cases i <;> simp [__smtx_model_eval_apply] at hiNN ⊢
  rw [hApply]
  exact (model_total_typed_native_fun_typed hM fid A B i hFunWF hi).1

theorem typeof_value_model_eval_apply_fun_value
    (M : SmtModel)
    (hM : model_wf M)
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (hf : __smtx_typeof_value f = SmtType.FunType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply M f i) = B := by
  rcases fun_value_canonical hf with ⟨fid, rfl⟩
  exact typeof_value_model_eval_apply_fun M hM hA hFunWF hi

theorem typeof_value_model_eval_apply_dt
    (M : SmtModel)
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply M f i) = B := by
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  have hDtConsApply :
      ∀ {s : native_String} {d : SmtDatatypeDecl} {n : native_Nat} {j : SmtValue},
        j ≠ SmtValue.NotValue ->
        __smtx_model_eval_apply M (SmtValue.DtCons s d n) j =
          SmtValue.Apply (SmtValue.DtCons s d n) j := by
    intro s d n j hj
    cases j <;> simp [__smtx_model_eval_apply] at hj ⊢
  have hApplyApply :
      ∀ {f v j : SmtValue},
        j ≠ SmtValue.NotValue ->
        __smtx_model_eval_apply M (SmtValue.Apply f v) j =
          SmtValue.Apply (SmtValue.Apply f v) j := by
    intro f v j hj
    cases j <;> simp [__smtx_model_eval_apply] at hj ⊢
  cases f with
  | NotValue => simp [__smtx_typeof_value] at hf
  | Boolean b => simp [__smtx_typeof_value] at hf
  | Numeral n => simp [__smtx_typeof_value] at hf
  | Rational q => simp [__smtx_typeof_value] at hf
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at hf
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Fun fid A B =>
      simp [__smtx_typeof_value] at hf
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hf
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Char c =>
      cases hValid : native_char_valid c <;>
        simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at hf
  | UValue k e => simp [__smtx_typeof_value] at hf
  | RegLan r => simp [__smtx_typeof_value] at hf
  | DtCons s d n =>
      have hOuter :
          __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s d n) i) =
            __smtx_typeof_apply_value
              (__smtx_typeof_value (SmtValue.DtCons s d n)) (__smtx_typeof_value i) := by
        simp [__smtx_typeof_value]
      rw [hDtConsApply hiNN, hOuter, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq, hA]
  | Apply f v =>
      have hOuter :
          __smtx_typeof_value (SmtValue.Apply (SmtValue.Apply f v) i) =
            __smtx_typeof_apply_value
              (__smtx_typeof_value (SmtValue.Apply f v)) (__smtx_typeof_value i) := by
        rfl
      rw [hApplyApply hiNN, hOuter, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Shows that evaluating `apply_generic` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_generic
    (M : SmtModel)
    (hM : model_wf M)
    (f x : SmtTerm)
    (hFunWF :
      ∀ {A B : SmtType},
        __smtx_typeof f = SmtType.FunType A B ->
          __smtx_type_wf (SmtType.FunType A B) = true)
    (hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hpresf : __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f)
    (hpresx : __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x) :
    __smtx_typeof_value (__smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x)) =
        __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
    rcases typeof_apply_non_none_cases hNN with ⟨A, B, hF, hX, hA, hB⟩
    have hArg : __smtx_typeof_value (__smtx_model_eval M x) = A := by
      simpa [hX] using hpresx
    rcases hF with hFunTy | hDtcTy
    ·
        rw [hFunTy, hX]
        have hFun :
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B := by
          simpa [hFunTy] using hpresf
        have hFunWf : __smtx_type_wf (SmtType.FunType A B) = true :=
          hFunWF hFunTy
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA] using
          typeof_value_model_eval_apply_fun_value M hM hA hFunWf hFun hArg
    ·
        rw [hDtcTy, hX]
        have hDt :
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
          simpa [hDtcTy] using hpresf
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA] using
          typeof_value_model_eval_apply_dt M hA hDt hArg

end Smtm
