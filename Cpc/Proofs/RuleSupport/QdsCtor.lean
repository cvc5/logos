module

public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

public section

open Eo
open SmtEval
open Smtm

namespace QuantDtSplitRule

attribute [local simp] Smtm.__smtx_type_wf_component

set_option maxHeartbeats 1000000000
set_option synthInstance.maxHeartbeats 1000000

inductive CH : Term -> Prop where
  | datatype (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      CH (Term.DtCons s d i)
  | tuple : CH (Term.UOp UserOp.tuple)
  | tupleUnit : CH (Term.UOp UserOp.tuple_unit)

inductive CS : Term -> Prop where
  | head {c : Term} : CH c -> CS c
  | apply {c : Term} {s : native_String} {T : Term} :
      CS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      CS (Term.Apply c (Term.Var (Term.String s) T))

inductive DCS : Term -> Prop where
  | head (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      DCS (Term.DtCons s d i)
  | apply {c : Term} {s : native_String} {T : Term} :
      DCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      DCS (Term.Apply c (Term.Var (Term.String s) T))

inductive TCS : Term -> Prop where
  | head : TCS (Term.UOp UserOp.tuple)
  | apply {c : Term} {s : native_String} {T : Term} :
      TCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      TCS (Term.Apply c (Term.Var (Term.String s) T))

inductive UCS : Term -> Prop where
  | head : UCS (Term.UOp UserOp.tuple_unit)
  | apply {c : Term} {s : native_String} {T : Term} :
      UCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      UCS (Term.Apply c (Term.Var (Term.String s) T))

theorem cs_cases {c : Term} (h : CS c) : DCS c ∨ TCS c ∨ UCS c := by
  induction h with
  | head hh =>
      cases hh with
      | datatype s d i => exact .inl (.head s d i)
      | tuple => exact .inr (.inl .head)
      | tupleUnit => exact .inr (.inr .head)
  | apply h wf ih =>
      rcases ih with ih | ih | ih
      · exact .inl (.apply ih wf)
      · exact .inr (.inl (.apply ih wf))
      · exact .inr (.inr (.apply ih wf))

/-! The generated SMT datatype typing functions expose selector types by
walking an application spine.  These small list views make that information
usable by the reverse quantifier proof. -/

def qdsSmtApplyHead : SmtTerm -> SmtTerm
  | SmtTerm.Apply f _ => qdsSmtApplyHead f
  | t => t

def qdsSmtNumApplyArgs : SmtTerm -> Nat
  | SmtTerm.Apply f _ => Nat.succ (qdsSmtNumApplyArgs f)
  | _ => 0

def qdsSmtApplyArgs : SmtTerm -> List SmtTerm
  | SmtTerm.Apply f a => qdsSmtApplyArgs f ++ [a]
  | _ => []

theorem qdsSmtApplyHead_foldl (f : SmtTerm) (args : List Term) :
    qdsSmtApplyHead
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) =
      qdsSmtApplyHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (SmtTerm.Apply f (__eo_to_smt a))

theorem qdsSmtApplyArgs_foldl (f : SmtTerm) (args : List Term) :
    qdsSmtApplyArgs
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) =
      qdsSmtApplyArgs f ++ args.map __eo_to_smt := by
  induction args generalizing f with
  | nil => simp
  | cons a args ih =>
      rw [show List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f
        (a :: args) = List.foldl
          (fun g a => SmtTerm.Apply g (__eo_to_smt a))
          (SmtTerm.Apply f (__eo_to_smt a)) args from rfl]
      rw [ih]
      simp [qdsSmtApplyArgs, List.append_assoc]

theorem qds_foldl_prefix_non_none
    {f : SmtTerm} {s : native_String} {d : SmtDatatypeDecl} {i : Nat}
    (args : List Term)
    (hHead : qdsSmtApplyHead f = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) ≠
      SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  induction args generalizing f with
  | nil => exact hNN
  | cons a args ih =>
      have hHeadApply : qdsSmtApplyHead (SmtTerm.Apply f (__eo_to_smt a)) =
          SmtTerm.DtCons s d i := by simpa [qdsSmtApplyHead] using hHead
      have hApplyNN : __smtx_typeof (SmtTerm.Apply f (__eo_to_smt a)) ≠
          SmtType.None :=
        ih hHeadApply hNN
      have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
        intro s₀ d₀ i₀ j₀ hf
        subst f
        simp [qdsSmtApplyHead] at hHead
      have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
        intro s₀ d₀ i₀ hf
        subst f
        simp [qdsSmtApplyHead] at hHead
      have hGeneric : generic_apply_type f (__eo_to_smt a) :=
        generic_apply_type_of_non_datatype_head hNotSel hNotTester
      have hApplyTypeNN : __smtx_typeof_apply (__smtx_typeof f)
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
        rw [← hGeneric]
        exact hApplyNN
      rcases typeof_apply_non_none_cases hApplyTypeNN with
        ⟨A, B, hFun, hArg, hA, hB⟩
      rcases hFun with hFun | hFun <;> rw [hFun] <;> simp

@[simp] theorem qdsSmtApplyArgs_length (t : SmtTerm) :
    (qdsSmtApplyArgs t).length = qdsSmtNumApplyArgs t := by
  cases t with
  | Apply f a =>
      simp [qdsSmtApplyArgs, qdsSmtNumApplyArgs, qdsSmtApplyArgs_length f]
  | _ => rfl
termination_by sizeOf t

private theorem qds_smt_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A) (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
      hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
      hA]

private theorem qds_smt_dt_cons_chain_type_aux :
    ∀ (n : Nat) (t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
      (i : native_Nat),
      qdsSmtNumApplyArgs t = n ->
      qdsSmtApplyHead t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      __smtx_typeof t =
        dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
          (qdsSmtNumApplyArgs t) := by
  intro n
  induction n with
  | zero =>
      intro t s d i hN hHead hNN
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case DtCons s' d' i' =>
        rcases hHead with ⟨rfl, hEq⟩
        rcases hEq with ⟨rfl, rfl⟩
        rw [Smtm.typeof_dt_cons_eq]
        have hGuard :
            __smtx_typeof_guard_wf (SmtType.Datatype s' d')
                (__smtx_typeof_dt_cons_rec (SmtType.Datatype s' d')
                  (__smtx_dt_resolve (__smtx_dd_lookup s' d') d') i') =
              __smtx_typeof_dt_cons_rec (SmtType.Datatype s' d')
                (__smtx_dt_resolve (__smtx_dd_lookup s' d') d') i' :=
          smtx_typeof_guard_wf_of_non_none _ _
            (by simpa [Smtm.typeof_dt_cons_eq] using hNN)
        simp only [hGuard, qdsSmtNumApplyArgs, dt_cons_applied_type_rec_zero,
          typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
  | succ n ih =>
      intro t s d i hN hHead hNN
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case Apply f a =>
        have hHeadF : qdsSmtApplyHead f = SmtTerm.DtCons s d i := by
          simpa using hHead
        have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
          intro s₀ d₀ i₀ j₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
          intro s₀ d₀ i₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hGeneric : generic_apply_type f a :=
          generic_apply_type_of_non_datatype_head hNotSel hNotTester
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof a) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hNN
          exact hNN
        rcases typeof_apply_non_none_cases hApplyNN with
          ⟨A, B, hHeadTy, hArg, hA, _hB⟩
        have hFunNN : __smtx_typeof f ≠ SmtType.None := by
          rcases hHeadTy with hHeadTy | hHeadTy <;> rw [hHeadTy] <;> simp
        have ihEq := ih f s d i hN hHeadF hFunNN
        have hLt : qdsSmtNumApplyArgs f <
            __smtx_dt_num_sels
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp only [dt_cons_type_num_args_fun_type] at hArgs
            omega
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp only [dt_cons_type_num_args_dtc_app_type] at hArgs
            omega
        let R := __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
            (qdsSmtNumApplyArgs f)
        let Rest := dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
            (Nat.succ (qdsSmtNumApplyArgs f))
        have hStep : dt_cons_applied_type_rec s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
                (qdsSmtNumApplyArgs f) =
            SmtType.DtcAppType R Rest := by
          simpa [R, Rest] using dt_cons_applied_type_rec_step s d
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
              (qdsSmtNumApplyArgs f) hLt
        have hArgR : __smtx_typeof a = R := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hBad : SmtType.DtcAppType R Rest = SmtType.FunType A B :=
              (ihEq.trans hStep).symm.trans hHeadTy
            cases hBad
          · have hCmp : SmtType.DtcAppType R Rest = SmtType.DtcAppType A B :=
              (ihEq.trans hStep).symm.trans hHeadTy
            injection hCmp with hAeq _
            exact hArg.trans hAeq.symm
        have hRNN : R ≠ SmtType.None := by
          rw [← hArgR, hArg]
          exact hA
        have hApplyTy : __smtx_typeof (SmtTerm.Apply f a) = Rest := by
          rw [hGeneric]
          exact qds_smt_typeof_apply_of_head_cases (Or.inr (ihEq.trans hStep))
            hArgR hRNN
        simpa [qdsSmtNumApplyArgs, Rest] using hApplyTy

theorem qds_smt_dt_cons_chain_type
    {t : SmtTerm} {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof t ≠ SmtType.None) :
    __smtx_typeof t =
      dt_cons_applied_type_rec s d
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
        (qdsSmtNumApplyArgs t) :=
  qds_smt_dt_cons_chain_type_aux (qdsSmtNumApplyArgs t) t s d i rfl hHead hNN

private theorem qds_smt_dt_cons_arg_types_aux :
    ∀ (n : Nat) (t : SmtTerm) (s : native_String) (d : SmtDatatypeDecl)
      (i : native_Nat),
      qdsSmtNumApplyArgs t = n ->
      qdsSmtApplyHead t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      ∀ j, j < (qdsSmtApplyArgs t).length ->
        __smtx_typeof (qdsSmtApplyArgs t)[j]! =
          __smtx_ret_typeof_sel_rec
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j := by
  intro n
  induction n with
  | zero =>
      intro t s d i hN hHead hNN j hJ
      have : (qdsSmtApplyArgs t).length = 0 := by
        rw [qdsSmtApplyArgs_length, hN]
      omega
  | succ n ih =>
      intro t s d i hN hHead hNN j hJ
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case Apply f a =>
        have hHeadF : qdsSmtApplyHead f = SmtTerm.DtCons s d i := by
          simpa using hHead
        have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
          intro s₀ d₀ i₀ j₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
          intro s₀ d₀ i₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hGeneric : generic_apply_type f a :=
          generic_apply_type_of_non_datatype_head hNotSel hNotTester
        have hApplyNN : __smtx_typeof_apply (__smtx_typeof f)
            (__smtx_typeof a) ≠ SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hNN
          exact hNN
        rcases typeof_apply_non_none_cases hApplyNN with
          ⟨A, B, hHeadTy, hArg, hA, _hB⟩
        have hFunNN : __smtx_typeof f ≠ SmtType.None := by
          rcases hHeadTy with hHeadTy | hHeadTy <;> rw [hHeadTy] <;> simp
        have hChain := qds_smt_dt_cons_chain_type hHeadF hFunNN
        have hLt : qdsSmtNumApplyArgs f <
            __smtx_dt_num_sels
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [hChain, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp only [dt_cons_type_num_args_fun_type] at hArgs
            omega
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [hChain, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp only [dt_cons_type_num_args_dtc_app_type] at hArgs
            omega
        let R := __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
            (qdsSmtNumApplyArgs f)
        let Rest := dt_cons_applied_type_rec s d
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
            (Nat.succ (qdsSmtNumApplyArgs f))
        have hStep : dt_cons_applied_type_rec s d
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
                (qdsSmtNumApplyArgs f) =
            SmtType.DtcAppType R Rest := by
          simpa [R, Rest] using dt_cons_applied_type_rec_step s d
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
              (qdsSmtNumApplyArgs f) hLt
        have hArgR : __smtx_typeof a = R := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hBad : SmtType.DtcAppType R Rest = SmtType.FunType A B :=
              (hChain.trans hStep).symm.trans hHeadTy
            cases hBad
          · have hCmp : SmtType.DtcAppType R Rest = SmtType.DtcAppType A B :=
              (hChain.trans hStep).symm.trans hHeadTy
            injection hCmp with hAeq _
            exact hArg.trans hAeq.symm
        rw [show qdsSmtApplyArgs (SmtTerm.Apply f a) =
          qdsSmtApplyArgs f ++ [a] from rfl] at hJ ⊢
        by_cases hLast : j = (qdsSmtApplyArgs f).length
        · subst j
          simpa [R] using hArgR
        · have hJ' : j < qdsSmtNumApplyArgs f + 1 := by
            simpa using hJ
          have hLast' : j ≠ qdsSmtNumApplyArgs f := by
            simpa using hLast
          have hPrefix' : j < qdsSmtNumApplyArgs f := by omega
          have hPrefix : j < (qdsSmtApplyArgs f).length := by
            simpa using hPrefix'
          have hGet : (qdsSmtApplyArgs f ++ [a])[j]! =
              (qdsSmtApplyArgs f)[j]! := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
              List.getElem?_append_left hPrefix]
          rw [hGet]
          exact ih f s d i hN hHeadF hFunNN j hPrefix

theorem qds_smt_dt_cons_arg_types
    {t : SmtTerm} {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof t ≠ SmtType.None) :
    ∀ j, j < (qdsSmtApplyArgs t).length ->
      __smtx_typeof (qdsSmtApplyArgs t)[j]! =
        __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j :=
  qds_smt_dt_cons_arg_types_aux (qdsSmtNumApplyArgs t) t s d i rfl
    hHead hNN

theorem qds_smt_dt_cons_num_args_of_datatype
    {t : SmtTerm} {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hTy : __smtx_typeof t = SmtType.Datatype s d) :
    qdsSmtNumApplyArgs t =
      __smtx_dt_num_sels
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i := by
  have hNN : __smtx_typeof t ≠ SmtType.None := by rw [hTy]; simp
  have hChain := qds_smt_dt_cons_chain_type hHead hNN
  have hRes : dt_cons_applied_type_rec s d
      (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      (qdsSmtNumApplyArgs t) = SmtType.Datatype s d := hChain.symm.trans hTy
  have hArgsZero : __smtx_dt_num_sels
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i -
      qdsSmtNumApplyArgs t = 0 := by
    have hArgs := congrArg dt_cons_type_num_args hRes
    rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
    simpa only [dt_cons_type_num_args_datatype] using hArgs
  have hLe : qdsSmtNumApplyArgs t ≤
      __smtx_dt_num_sels
        (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d
      (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i
      (qdsSmtNumApplyArgs t)
      (by rw [hRes]; simp)
  exact Nat.le_antisymm hLe (Nat.sub_eq_zero_iff_le.mp hArgsZero)

/-! A datatype-constructor spine has a particularly small EO type-state
machine: it is either still waiting for fields, has reached the constructor's
datatype, or is stuck.  Recording that invariant lets us use the well-formed
final type to rule out both incomplete and over-applied spines. -/

private inductive DcsTypeChain
    (s : native_String) (d : DatatypeDecl) : Term -> Prop where
  | base : DcsTypeChain s d (Term.DatatypeType s d)
  | field {A B : Term} : DcsTypeChain s d B ->
      DcsTypeChain s d (Term.DtcAppType A B)
  | stuck : DcsTypeChain s d Term.Stuck

mutual
  private theorem dcs_type_chain_cons (s : native_String) (d : DatatypeDecl)
      (c : DatatypeCons) (tail : Datatype) :
      DcsTypeChain s d
        (__eo_typeof_dt_cons_rec (Term.DatatypeType s d)
          (Datatype.sum c tail) 0) := by
    cases c with
    | unit =>
        simpa [__eo_typeof_dt_cons_rec] using (DcsTypeChain.base (s := s) (d := d))
    | cons A c =>
        simpa [__eo_typeof_dt_cons_rec] using
          (DcsTypeChain.field (dcs_type_chain_cons s d c tail))

  private theorem dcs_type_chain_rec (s : native_String) (d : DatatypeDecl) :
      ∀ (body : Datatype) (i : native_Nat),
        DcsTypeChain s d
          (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) body i)
    | Datatype.null, i => by
        simpa [__eo_typeof_dt_cons_rec] using
          (DcsTypeChain.stuck (s := s) (d := d))
    | Datatype.sum c tail, 0 => dcs_type_chain_cons s d c tail
    | Datatype.sum c tail, Nat.succ i => by
        simpa [__eo_typeof_dt_cons_rec] using dcs_type_chain_rec s d tail i
end

private theorem dcs_type_chain_apply_var
    {s : native_String} {d : DatatypeDecl} {F A : Term}
    (h : DcsTypeChain s d F) :
    DcsTypeChain s d
      (__eo_typeof_apply F A) := by
  cases h with
  | base =>
      cases A <;> simpa [__eo_typeof_apply] using
        (DcsTypeChain.stuck (s := s) (d := d))
  | @field U V hTail =>
      by_cases hAStuck : A = Term.Stuck
      · subst A
        simpa [__eo_typeof_apply] using
          (DcsTypeChain.stuck (s := s) (d := d))
      · have hApply : __eo_typeof_apply (Term.DtcAppType U V) A =
            __eo_requires U A V := by
          cases A <;> simp_all [__eo_typeof_apply]
        rw [hApply]
        cases hEq : native_teq U A <;>
          cases hOk : native_not (native_teq U Term.Stuck) <;>
            simp [__eo_requires, native_ite, hEq, hOk]
        · exact DcsTypeChain.stuck
        · exact DcsTypeChain.stuck
        · exact DcsTypeChain.stuck
        · exact hTail
  | stuck =>
      cases A <;> simpa [__eo_typeof_apply] using
        (DcsTypeChain.stuck (s := s) (d := d))

private def qdsEoApplyHead : Term -> Term
  | Term.Apply f _ => qdsEoApplyHead f
  | t => t

private theorem dcs_typeof_apply_eq_of_head
    (f x : Term) {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hHead : qdsEoApplyHead f = Term.DtCons s d i) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case __eo_List_cons => cases hHead
  case UOp op =>
    cases op <;> try rfl
    all_goals
      change Term.UOp _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case UOp1 op j =>
    cases op <;> try rfl
    all_goals
      change Term.UOp1 _ _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case UOp2 op j k =>
    cases op <;> try rfl
    all_goals
      change Term.UOp2 _ _ _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        change Term.UOp _ = Term.DtCons _ _ _ at hHead
        cases hHead
    case UOp1 op j =>
      cases op <;> try rfl
      all_goals
        change Term.UOp1 _ _ = Term.DtCons _ _ _ at hHead
        cases hHead
    case FunType =>
      change Term.FunType = Term.DtCons _ _ _ at hHead
      cases hHead
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          change Term.UOp _ = Term.DtCons _ _ _ at hHead
          cases hHead
      case Apply f'' c =>
        cases f'' <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            change Term.UOp _ = Term.DtCons _ _ _ at hHead
            cases hHead

private theorem dcs_type_chain {c : Term} (hs : DCS c) :
    ∃ (s : native_String) (d : DatatypeDecl) (i : native_Nat),
      qdsEoApplyHead c = Term.DtCons s d i ∧
      DcsTypeChain s d (__eo_typeof c) := by
  induction hs with
  | head s d i =>
      exact ⟨s, d, i, rfl,
        dcs_type_chain_rec s d (__eo_dd_resolve s d) i⟩
  | @apply c sx A hs hA ih =>
      obtain ⟨s, d, i, hHead, hChain⟩ := ih
      refine ⟨s, d, i, hHead, ?_⟩
      rw [dcs_typeof_apply_eq_of_head c
        (Term.Var (Term.String sx) A) hHead]
      exact dcs_type_chain_apply_var hChain

private theorem dcs_type_chain_wf_base
    {s : native_String} {d : DatatypeDecl} {T : Term}
    (h : DcsTypeChain s d T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    T = Term.DatatypeType s d := by
  cases h with
  | base => rfl
  | @field A B hTail =>
      exfalso
      cases hA : __eo_to_smt_type A <;>
        cases hB : __eo_to_smt_type B <;>
          simp [__eo_to_smt_type, __smtx_typeof_guard,
            __smtx_type_wf, __smtx_type_wf_component,
            __smtx_type_wf_rec, native_and, native_ite, native_Teq,
            hA, hB] at hWf
  | stuck =>
      exfalso
      simp [__eo_to_smt_type, __smtx_type_wf,
        __smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

private theorem dcs_apply_head_non_stuck
    {c : Term} (hs : DCS c)
    (hFinal : __eo_typeof c ≠ Term.Stuck) :
    __eo_typeof (qdsEoApplyHead c) ≠ Term.Stuck := by
  induction hs with
  | head s d i => exact hFinal
  | @apply c sx A hs hA ih =>
      apply ih
      intro hStuck
      apply hFinal
      obtain ⟨s, d, i, hHead, hChain⟩ := dcs_type_chain hs
      rw [dcs_typeof_apply_eq_of_head c
        (Term.Var (Term.String sx) A) hHead]
      rw [hStuck]
      cases A <;> rfl

private theorem dcs_smt_rec_non_none_of_eo_rec_non_stuck
    (T : Term) (base : SmtType)
    (hBase : base ≠ SmtType.None) :
    ∀ (body : Datatype) (i : native_Nat),
      __eo_typeof_dt_cons_rec T body i ≠ Term.Stuck ->
      __smtx_typeof_dt_cons_rec base
          (__eo_to_smt_datatype body) i ≠ SmtType.None
  | Datatype.null, i, h => by
      exfalso
      apply h
      cases T <;> cases i <;> simp [__eo_typeof_dt_cons_rec]
  | Datatype.sum c tail, 0, h => by
      cases c with
      | unit =>
          simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using hBase
      | cons A c =>
          simp [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_typeof_dt_cons_rec]
  | Datatype.sum c tail, Nat.succ i, h => by
      have hTail : __eo_typeof_dt_cons_rec T tail i ≠ Term.Stuck := by
        cases T <;> simp [__eo_typeof_dt_cons_rec] at h ⊢ <;> exact h
      simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using
        dcs_smt_rec_non_none_of_eo_rec_non_stuck T base hBase tail i hTail

private theorem dcs_var_translation
    (sx : native_String) (A : Term)
    (hWf : __smtx_type_wf (__eo_to_smt_type A) = true) :
    RuleProofs.eo_has_smt_translation
      (Term.Var (Term.String sx) A) := by
  unfold RuleProofs.eo_has_smt_translation
  change __smtx_typeof_guard_wf (__eo_to_smt_type A)
      (__eo_to_smt_type A) ≠ SmtType.None
  have hNN : __eo_to_smt_type A ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hWf
    simp [__smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] at hWf
  rw [show __smtx_typeof_guard_wf (__eo_to_smt_type A)
      (__eo_to_smt_type A) = __eo_to_smt_type A by
    unfold __smtx_typeof_guard_wf
    rw [hWf]
    rfl]
  exact hNN

private theorem dcs_translation_of_head
    {c : Term} (hs : DCS c)
    (hHead : RuleProofs.eo_has_smt_translation (qdsEoApplyHead c))
    (hFinal : __eo_typeof c ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation c := by
  induction hs with
  | head s d i => exact hHead
  | @apply c sx A hs hA ih =>
      have hPrefix : __eo_typeof c ≠ Term.Stuck := by
        intro hStuck
        apply hFinal
        obtain ⟨s, d, i, hRoot, hChain⟩ := dcs_type_chain hs
        rw [dcs_typeof_apply_eq_of_head c
          (Term.Var (Term.String sx) A) hRoot]
        rw [hStuck]
        cases A <;> rfl
      have hHead' : RuleProofs.eo_has_smt_translation (qdsEoApplyHead c) := by
        simpa [qdsEoApplyHead] using hHead
      exact SubstituteTranslatabilitySupport.eo_has_smt_translation_apply_of_head_arg_translation_and_type
        c (Term.Var (Term.String sx) A) (ih hHead' hPrefix)
        (dcs_var_translation sx A hA) hFinal

theorem dcs_translation {c T : Term} (hs : DCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    RuleProofs.eo_has_smt_translation c := by
  subst T
  obtain ⟨s, d, i, hHead, hChain⟩ := dcs_type_chain hs
  have hBase := dcs_type_chain_wf_base hChain hWf
  have hFinal : __eo_typeof c ≠ Term.Stuck := by rw [hBase]; simp
  have hHeadNe := dcs_apply_head_non_stuck hs hFinal
  rw [hHead] at hHeadNe
  have hReserved : __eo_to_smt_reserved_datatype_name s = false := by
    have hWf' := hWf
    rw [hBase] at hWf'
    cases hRes : __eo_to_smt_reserved_datatype_name s <;>
      simp [__eo_to_smt_type, native_ite, hRes,
        __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_and] at hWf' ⊢
  let dd := __eo_to_smt_datatype_decl d
  let body := __smtx_dt_resolve (__smtx_dd_lookup s dd) dd
  let base := SmtType.Datatype s dd
  have hBaseWf : __smtx_type_wf base = true := by
    rw [hBase] at hWf
    simpa [base, dd, __eo_to_smt_type, native_ite, hReserved] using hWf
  have hLookupWf :
      __smtx_dt_wf_rec dd (__smtx_dd_lookup s dd) = true :=
    Smtm.datatype_wf_rec_of_type_wf (by simpa [base] using hBaseWf)
  have hLookupNoNone :
      TranslationProofs.noNoneDt (__smtx_dd_lookup s dd) = true :=
    TranslationProofs.noNoneDt_of_wf dd (__smtx_dd_lookup s dd) hLookupWf
  have hWfParts :
      native_inhabited_type (SmtType.Datatype s dd) = true ∧
        (__smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true) := by
    simpa [base, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] using hBaseWf
  have hDeclNoNone : TranslationProofs.noNoneDecl dd = true :=
    TranslationProofs.noNoneDecl_of_wf dd dd hWfParts.2.2
  have hResolve :
      __eo_to_smt_datatype (__eo_dd_resolve s d) = body := by
    simpa [dd, body] using
      TranslationProofs.eo_to_smt_dd_resolve_of_no_none s d
        (by simpa [dd] using hLookupNoNone)
        (by simpa [dd] using hDeclNoNone)
  have hRawNN :
      __smtx_typeof_dt_cons_rec base
          body i ≠ SmtType.None := by
    rw [← hResolve]
    exact dcs_smt_rec_non_none_of_eo_rec_non_stuck
      (Term.DatatypeType s d) base (by simp [base])
      (__eo_dd_resolve s d) i hHeadNe
  have hRootTrans : RuleProofs.eo_has_smt_translation
      (Term.DtCons s d i) := by
    unfold RuleProofs.eo_has_smt_translation
    change __smtx_typeof
        (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s dd i)) ≠ SmtType.None
    rw [hReserved]
    change __smtx_typeof_guard_wf
      (SmtType.Datatype s dd)
      (__smtx_typeof_dt_cons_rec
        (SmtType.Datatype s dd) body i) ≠ SmtType.None
    unfold __smtx_typeof_guard_wf
    rw [show __smtx_type_wf (SmtType.Datatype s dd) = true by
      simpa [base] using hBaseWf]
    exact hRawNN
  apply dcs_translation_of_head hs
  · simpa [hHead] using hRootTrans
  · exact hFinal

private theorem qds_stuck_type_not_wf :
    __smtx_type_wf (__eo_to_smt_type Term.Stuck) ≠ true := by
  native_decide

private theorem qds_eo_typeof_apply_stuck_head (V : Term) :
    __eo_typeof_apply Term.Stuck V = Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_apply_unit_tuple_stuck (V : Term) :
    __eo_typeof_apply (Term.UOp UserOp.UnitTuple) V = Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_tuple_partial_var_stuck
    (s : native_String) (U : Term) :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.tuple)
          (Term.Var (Term.String s) U)) = Term.Stuck := by
  change __eo_typeof_apply Term.Stuck U = Term.Stuck
  exact qds_eo_typeof_apply_stuck_head U

private theorem qds_eo_typeof_tuple_unit_apply_var_stuck
    (s : native_String) (U : Term) :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.tuple_unit)
          (Term.Var (Term.String s) U)) = Term.Stuck := by
  change __eo_typeof_apply (Term.UOp UserOp.UnitTuple) U = Term.Stuck
  exact qds_eo_typeof_apply_unit_tuple_stuck U

private theorem qds_eo_typeof_apply_tuple_type_stuck (T U V : Term) :
    __eo_typeof_apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U) V =
      Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_apply_requires_tuple_type_stuck
    (P T U V : Term) :
    __eo_typeof_apply
        (__eo_requires P (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U)) V =
      Term.Stuck := by
  cases hP : native_teq P (Term.Boolean true) <;>
    cases hStuck : native_not (native_teq P Term.Stuck) <;>
      simp [__eo_requires, native_ite, hP, hStuck,
        qds_eo_typeof_apply_tuple_type_stuck,
        qds_eo_typeof_apply_stuck_head]

private theorem qds_eo_typeof_apply_typeof_tuple_stuck
    (T U V : Term) :
    __eo_typeof_apply (__eo_typeof_tuple T U) V = Term.Stuck := by
  unfold __eo_typeof_tuple
  split
  · cases V <;> simp [__eo_typeof_apply]
  · cases V <;> simp [__eo_typeof_apply]
  · exact qds_eo_typeof_apply_requires_tuple_type_stuck
      (__eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) U)) T U V

private theorem tcs_apply3_stuck {c : Term} (hs : TCS c) :
    ∀ (a₀ a₁ a₂ : Term),
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply c a₀) a₁) a₂) =
        Term.Stuck := by
  induction hs with
  | head =>
      intro a₀ a₁ a₂
      change __eo_typeof_apply
          (__eo_typeof_tuple (__eo_typeof a₀) (__eo_typeof a₁))
          (__eo_typeof a₂) = Term.Stuck
      exact qds_eo_typeof_apply_typeof_tuple_stuck _ _ _
  | @apply c s T hs hT ih =>
      intro a₀ a₁ a₂
      have hApply :
          __eo_typeof
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply c (Term.Var (Term.String s) T)) a₀) a₁) a₂) =
            __eo_typeof_apply
              (__eo_typeof
                (Term.Apply
                  (Term.Apply
                    (Term.Apply c (Term.Var (Term.String s) T)) a₀) a₁))
              (__eo_typeof a₂) := by
        cases c <;> try rfl
        case UOp op =>
          cases hs
          rfl
      rw [hApply, ih (Term.Var (Term.String s) T) a₀ a₁]
      exact qds_eo_typeof_apply_stuck_head (__eo_typeof a₂)

private def qdsAppHead : Term -> Term
  | Term.Apply f _ => qdsAppHead f
  | t => t

private theorem ucs_app_head {c : Term} (hs : UCS c) :
    qdsAppHead c = Term.UOp UserOp.tuple_unit := by
  induction hs with
  | head => rfl
  | apply hs hT ih => exact ih

private theorem qds_eo_typeof_unit_head_extra_application_stuck :
    ∀ (g x : Term),
      qdsAppHead g = Term.UOp UserOp.tuple_unit ->
      g ≠ Term.UOp UserOp.tuple_unit ->
      __eo_typeof (Term.Apply g x) = Term.Stuck
  | Term.Apply f y, x, hHead, _hNe => by
      cases f with
      | UOp op =>
          cases op with
          | tuple_unit =>
              change __eo_typeof_apply
                  (__eo_typeof_apply (Term.UOp UserOp.UnitTuple)
                    (__eo_typeof y)) (__eo_typeof x) = Term.Stuck
              rw [qds_eo_typeof_apply_unit_tuple_stuck]
              exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
          | _ => simp [qdsAppHead] at hHead
      | Apply f' y' =>
          cases f' with
          | UOp op =>
              cases op with
              | tuple_unit =>
                  change __eo_typeof_apply
                      (__eo_typeof_apply
                        (__eo_typeof_apply (Term.UOp UserOp.UnitTuple)
                          (__eo_typeof y')) (__eo_typeof y))
                      (__eo_typeof x) = Term.Stuck
                  rw [qds_eo_typeof_apply_unit_tuple_stuck,
                    qds_eo_typeof_apply_stuck_head]
                  exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
              | _ => simp [qdsAppHead] at hHead
          | Apply f'' z =>
              have hInner :
                  __eo_typeof
                    (Term.Apply (Term.Apply (Term.Apply f'' z) y') y) =
                      Term.Stuck :=
                qds_eo_typeof_unit_head_extra_application_stuck
                  (Term.Apply (Term.Apply f'' z) y') y
                  (by simpa [qdsAppHead] using hHead)
                  (by intro h; cases h)
              have hApply :
                  __eo_typeof
                      (Term.Apply
                        (Term.Apply (Term.Apply (Term.Apply f'' z) y') y) x) =
                    __eo_typeof_apply
                      (__eo_typeof
                        (Term.Apply (Term.Apply (Term.Apply f'' z) y') y))
                      (__eo_typeof x) := by
                cases f'' <;> try rfl
                case UOp op =>
                  cases op <;> try rfl
                  all_goals simp [qdsAppHead] at hHead
              rw [hApply, hInner]
              exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
          | _ => cases hHead
      | _ => cases hHead
  | Term.UOp op, x, hHead, hNe => by
      exact False.elim (hNe (by simpa [qdsAppHead] using hHead))
  | Term.UOp1 _ _, x, hHead, _hNe => by cases hHead
  | Term.UOp2 _ _ _, x, hHead, _hNe => by cases hHead
  | Term.UOp3 _ _ _ _, x, hHead, _hNe => by cases hHead
  | Term.__eo_List, x, hHead, _hNe => by cases hHead
  | Term.__eo_List_nil, x, hHead, _hNe => by cases hHead
  | Term.__eo_List_cons, x, hHead, _hNe => by cases hHead
  | Term.Bool, x, hHead, _hNe => by cases hHead
  | Term.Boolean _, x, hHead, _hNe => by cases hHead
  | Term.Numeral _, x, hHead, _hNe => by cases hHead
  | Term.Rational _, x, hHead, _hNe => by cases hHead
  | Term.String _, x, hHead, _hNe => by cases hHead
  | Term.Binary _ _, x, hHead, _hNe => by cases hHead
  | Term.Type, x, hHead, _hNe => by cases hHead
  | Term.Stuck, x, hHead, _hNe => by cases hHead
  | Term.FunType, x, hHead, _hNe => by cases hHead
  | Term.Var _ _, x, hHead, _hNe => by cases hHead
  | Term.DatatypeType _ _, x, hHead, _hNe => by cases hHead
  | Term.DatatypeTypeRef _, x, hHead, _hNe => by cases hHead
  | Term.DtcAppType _ _, x, hHead, _hNe => by cases hHead
  | Term.DtCons _ _ _, x, hHead, _hNe => by cases hHead
  | Term.DtSel _ _ _ _, x, hHead, _hNe => by cases hHead
  | Term.USort _, x, hHead, _hNe => by cases hHead
  | Term.UConst _ _, x, hHead, _hNe => by cases hHead

private theorem ucs_apply_var_stuck {c : Term} (hs : UCS c)
    (s : native_String) (U : Term) :
    __eo_typeof (Term.Apply c (Term.Var (Term.String s) U)) =
      Term.Stuck := by
  cases hs with
  | head => exact qds_eo_typeof_tuple_unit_apply_var_stuck s U
  | @apply c s₀ U₀ hs hU₀ =>
      exact qds_eo_typeof_unit_head_extra_application_stuck
        (Term.Apply c (Term.Var (Term.String s₀) U₀))
        (Term.Var (Term.String s) U)
        (by simpa [qdsAppHead] using ucs_app_head hs)
        (by intro h; cases h)

theorem tcs_full {c T : Term} (hs : TCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    ∃ (s₁ : native_String) (U₁ : Term) (s₂ : native_String) (U₂ : Term),
      c = Term.Apply
        (Term.Apply (Term.UOp UserOp.tuple) (Term.Var (Term.String s₁) U₁))
        (Term.Var (Term.String s₂) U₂) ∧
      __smtx_type_wf (__eo_to_smt_type U₁) = true ∧
      __smtx_type_wf (__eo_to_smt_type U₂) = true := by
  subst T
  cases hs with
  | head =>
      exact False.elim (qds_stuck_type_not_wf hWf)
  | @apply c s₂ U₂ hs hU₂ =>
      cases hs with
      | head =>
          rw [qds_eo_typeof_tuple_partial_var_stuck] at hWf
          exact False.elim (qds_stuck_type_not_wf hWf)
      | @apply c s₁ U₁ hs hU₁ =>
          cases hs with
          | head => exact ⟨s₁, U₁, s₂, U₂, rfl, hU₁, hU₂⟩
          | @apply c s₀ U₀ hs hU₀ =>
              have hStuck := tcs_apply3_stuck hs
                (Term.Var (Term.String s₀) U₀)
                (Term.Var (Term.String s₁) U₁)
                (Term.Var (Term.String s₂) U₂)
              rw [hStuck] at hWf
              exact False.elim (qds_stuck_type_not_wf hWf)

theorem ucs_full {c T : Term} (hs : UCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    c = Term.UOp UserOp.tuple_unit := by
  subst T
  cases hs with
  | head => rfl
  | @apply c s U hs hU =>
      rw [ucs_apply_var_stuck hs s U] at hWf
      exact False.elim (qds_stuck_type_not_wf hWf)

private theorem qds_requires_true_cases (P X : Term) :
    __eo_requires P (Term.Boolean true) X = Term.Stuck ∨
      __eo_requires P (Term.Boolean true) X = X := by
  unfold __eo_requires
  cases hEq : native_teq P (Term.Boolean true) <;>
    cases hOk : native_not (native_teq P Term.Stuck) <;>
      simp [native_ite, hEq, hOk]

private theorem qds_typeof_tuple_cases (A B : Term) :
    __eo_typeof_tuple A B = Term.Stuck ∨
      __eo_typeof_tuple A B =
        Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B := by
  by_cases hA : A = Term.Stuck
  · subst A
    exact Or.inl rfl
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp_all [__eo_typeof_tuple]
  have hDef : __eo_typeof_tuple A B =
      __eo_requires (__eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) B))
        (Term.Boolean true)
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B) := by
    cases A <;> cases B <;> simp_all [__eo_typeof_tuple]
  rw [hDef]
  exact qds_requires_true_cases _ _

theorem qds_typeof_tuple_eq_of_wf
    (A B : Term)
    (hWf : __smtx_type_wf (__eo_to_smt_type (__eo_typeof_tuple A B)) = true) :
    __eo_typeof_tuple A B =
      Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B := by
  rcases qds_typeof_tuple_cases A B with hStuck | hTuple
  · rw [hStuck] at hWf
    exact False.elim (qds_stuck_type_not_wf hWf)
  · exact hTuple

private theorem qds_smt_type_tuple_shape_of_wf
    {A B : SmtType}
    (hWf : __smtx_type_wf (__eo_to_smt_type_tuple A B) = true) :
    ∃ c : SmtDatatypeCons,
      B = SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) ∧
      __eo_to_smt_type_tuple A B =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum
              (SmtDatatypeCons.cons A c) SmtDatatype.null)) := by
  cases B <;> try
    { exfalso
      apply (show __smtx_type_wf SmtType.None ≠ true by native_decide)
      simpa [__eo_to_smt_type_tuple] using hWf }
  case Datatype s tailDD =>
    cases tailDD with
    | nil =>
        exfalso
        have : __smtx_type_wf SmtType.None = true := by
          simpa [__eo_to_smt_type_tuple] using hWf
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) this
    | cons s₂ tailD restDD =>
        cases tailD with
        | null =>
            exfalso
            have : __smtx_type_wf SmtType.None = true := by
              simpa [__eo_to_smt_type_tuple] using hWf
            exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) this
        | sum c restD =>
            cases restD with
            | sum c' restD' =>
                exfalso
                have : __smtx_type_wf SmtType.None = true := by
                  simpa [__eo_to_smt_type_tuple] using hWf
                exact (show __smtx_type_wf SmtType.None ≠ true by
                  native_decide) this
            | null =>
                cases restDD with
                | cons s₃ d₃ restDD' =>
                    exfalso
                    have : __smtx_type_wf SmtType.None = true := by
                      simpa [__eo_to_smt_type_tuple] using hWf
                    exact (show __smtx_type_wf SmtType.None ≠ true by
                      native_decide) this
                | nil =>
                    let gate :=
                      native_and
                        (native_and
                          (native_streq s (native_string_lit "@Tuple"))
                          (native_streq s₂ (native_string_lit "@Tuple")))
                        (__smtx_type_wf_component A)
                    have hGate : gate = true := by
                      cases hGate : gate
                      · exfalso
                        have : __smtx_type_wf SmtType.None = true := by
                          change __smtx_type_wf
                            (native_ite gate
                              (SmtType.Datatype
                                (native_string_lit "@Tuple")
                                (__eo_to_smt_tuple_decl
                                  (SmtDatatype.sum
                                    (SmtDatatypeCons.cons A c)
                                    SmtDatatype.null)))
                              SmtType.None) = true at hWf
                          rw [hGate] at hWf
                          exact hWf
                        exact (show __smtx_type_wf SmtType.None ≠ true by
                          native_decide) this
                      · rfl
                    have hParts :
                        (native_streq s (native_string_lit "@Tuple") = true ∧
                          native_streq s₂ (native_string_lit "@Tuple") = true) ∧
                            __smtx_type_wf_component A = true := by
                      simpa [gate, native_and] using hGate
                    have hs : s = native_string_lit "@Tuple" := by
                      simpa [native_streq] using hParts.1.1
                    have hs₂ : s₂ = native_string_lit "@Tuple" := by
                      simpa [native_streq] using hParts.1.2
                    subst s
                    subst s₂
                    refine ⟨c, by simp [__eo_to_smt_tuple_decl], ?_⟩
                    change native_ite gate
                      (SmtType.Datatype (native_string_lit "@Tuple")
                        (__eo_to_smt_tuple_decl
                          (SmtDatatype.sum
                            (SmtDatatypeCons.cons A c) SmtDatatype.null)))
                      SmtType.None =
                        SmtType.Datatype (native_string_lit "@Tuple")
                          (__eo_to_smt_tuple_decl
                            (SmtDatatype.sum
                              (SmtDatatypeCons.cons A c)
                              SmtDatatype.null))
                    rw [hGate]
                    rfl

theorem qds_tuple_type_shape_of_wf
    (A B : Term)
    (hWf : __smtx_type_wf
      (__eo_to_smt_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B)) = true) :
    ∃ c : SmtDatatypeCons,
      __eo_to_smt_type B =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) ∧
      __eo_to_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum
              (SmtDatatypeCons.cons (__eo_to_smt_type A) c)
              SmtDatatype.null)) := by
  let raw := __eo_to_smt_type_tuple (__eo_to_smt_type A) (__eo_to_smt_type B)
  have hGate : __smtx_type_wf raw = true := by
    cases hRawWf : __smtx_type_wf raw
    · exfalso
      rw [TranslationProofs.eo_to_smt_type_tuple_step] at hWf
      change __smtx_type_wf
        (native_ite (__smtx_type_wf raw) raw SmtType.None) = true at hWf
      rw [hRawWf] at hWf
      exact False.elim ((show __smtx_type_wf SmtType.None ≠ true by
        native_decide) hWf)
    · rfl
  obtain ⟨c, hTail, hRaw⟩ := qds_smt_type_tuple_shape_of_wf hGate
  refine ⟨c, hTail, ?_⟩
  rw [TranslationProofs.eo_to_smt_type_tuple_step]
  rw [show __smtx_type_wf raw = true from hGate]
  simpa [raw, native_ite] using hRaw

private def qdsNoTupleRefDtc : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      T ≠ SmtType.TypeRef (native_string_lit "@Tuple") ∧
        qdsNoTupleRefDtc c

private theorem qds_tuple_fields_no_tuple_ref :
    ∀ {T : Term} {c : SmtDatatypeCons},
      __eo_to_smt_type T =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)) ->
        qdsNoTupleRefDtc c
  | T, c, hT => by
      rcases TranslationProofs.eo_to_smt_type_eq_tuple_datatype hT with
        hUnit | hCons
      · rcases hUnit with ⟨rfl, hD⟩
        have hBody :
            SmtDatatype.sum c SmtDatatype.null =
              SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        injection hBody with hC _
        subst c
        trivial
      · rcases hCons with ⟨head, tail, tailC, rfl, hTail, hD⟩
        have hBody :
            SmtDatatype.sum c SmtDatatype.null =
              SmtDatatype.sum
                (SmtDatatypeCons.cons (__eo_to_smt_type head) tailC)
                SmtDatatype.null := by
          simpa [__eo_to_smt_tuple_decl] using hD
        injection hBody with hC _
        subst c
        exact ⟨TranslationProofs.eo_to_smt_type_ne_tuple_typeref head,
          qds_tuple_fields_no_tuple_ref hTail⟩
termination_by T c _hT => T

private theorem qds_tuple_resolve_cons_noop
    (c₀ : SmtDatatypeCons) :
    ∀ (c : SmtDatatypeCons),
      __smtx_dt_cons_wf_rec
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c₀ SmtDatatype.null)) c = true ->
      qdsNoTupleRefDtc c ->
      __smtx_dtc_resolve c
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c₀ SmtDatatype.null)) = c
  | SmtDatatypeCons.unit, hWf, hNoRef => rfl
  | SmtDatatypeCons.cons U c, hWf, hNoRef => by
      have hTailWf :
          __smtx_dt_cons_wf_rec
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum c₀ SmtDatatype.null)) c = true := by
        cases U <;> simp_all [__smtx_dt_cons_wf_rec, native_and]
      have hTail := qds_tuple_resolve_cons_noop c₀ c hTailWf hNoRef.2
      cases hU : U with
      | TypeRef s =>
          have hHas :
              __smtx_dd_has_dt s
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum c₀ SmtDatatype.null)) = true := by
            have hPair :
                __smtx_dd_has_dt s
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum c₀ SmtDatatype.null)) = true ∧
                  __smtx_dt_cons_wf_rec
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum c₀ SmtDatatype.null)) c = true := by
              simpa only [hU, __smtx_dt_cons_wf_rec, native_and,
                Bool.and_eq_true] using hWf
            exact hPair.1
          have hs : s = native_string_lit "@Tuple" := by
            simpa [__eo_to_smt_tuple_decl, __smtx_dd_has_dt,
              native_streq, native_or] using hHas
          subst s
          exact False.elim (hNoRef.1 hU)
      | _ =>
          simp [__smtx_dtc_resolve, hTail]

theorem qds_tuple_resolve_noop_of_eo_type
    (T : Term) (c : SmtDatatypeCons)
    (hShape : __eo_to_smt_type T =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)))
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    __smtx_dt_resolve
        (SmtDatatype.sum c SmtDatatype.null)
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)) =
      SmtDatatype.sum c SmtDatatype.null := by
  let body := SmtDatatype.sum c SmtDatatype.null
  let decl := __eo_to_smt_tuple_decl body
  have hDeclWf :
      __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple") decl) = true :=
    (congrArg __smtx_type_wf hShape).symm.trans hWf
  have hConsWf : __smtx_dt_cons_wf_rec decl c = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hDeclWf
    simpa [decl, body, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      __smtx_dt_wf_rec, native_streq, native_ite, native_and] using hDtWf
  have hNoRef : qdsNoTupleRefDtc c :=
    qds_tuple_fields_no_tuple_ref hShape
  have hResolveCons : __smtx_dtc_resolve c decl = c := by
    simpa [decl, body] using
      qds_tuple_resolve_cons_noop c c hConsWf hNoRef
  simp [decl, body, __smtx_dt_resolve, hResolveCons]

private theorem qds_tuple_ret_type_wf_aux (c₀ : SmtDatatypeCons) :
    ∀ (c : SmtDatatypeCons) (j : native_Nat),
      __smtx_dt_cons_wf_rec
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c₀ SmtDatatype.null)) c = true ->
      __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c₀ SmtDatatype.null))) = true ->
      j < __smtx_dtc_num_sels c ->
      __smtx_type_wf
        (__smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve
            (SmtDatatype.sum c SmtDatatype.null)
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c₀ SmtDatatype.null)))
          native_nat_zero j) = true
  | SmtDatatypeCons.unit, j, hWf, hOuterWf, hJ => by
      simp [__smtx_dtc_num_sels] at hJ
  | SmtDatatypeCons.cons U c, 0, hWf, hOuterWf, hJ => by
      by_cases hRef : ∃ s, U = SmtType.TypeRef s
      · rcases hRef with ⟨s, rfl⟩
        have hHas :
            __smtx_dd_has_dt s
                (__eo_to_smt_tuple_decl
                  (SmtDatatype.sum c₀ SmtDatatype.null)) = true := by
          have hPair :
              __smtx_dd_has_dt s
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum c₀ SmtDatatype.null)) = true := by
            have hPair' :
                __smtx_dd_has_dt s
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum c₀ SmtDatatype.null)) = true ∧
                  __smtx_dt_cons_wf_rec
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum c₀ SmtDatatype.null)) c = true := by
              simpa only [__smtx_dt_cons_wf_rec, native_and,
                Bool.and_eq_true] using hWf
            exact hPair'.1
          exact hPair
        have hs : s = native_string_lit "@Tuple" := by
          simpa [__eo_to_smt_tuple_decl, __smtx_dd_has_dt,
            native_streq, native_or] using hHas
        subst s
        simpa [__smtx_dt_resolve, __smtx_dtc_resolve,
          __smtx_ret_typeof_sel_rec] using hOuterWf
      · have hParts :
            native_inhabited_type U = true ∧
              __smtx_type_wf_rec U = true := by
          cases U <;>
            simp_all [__smtx_dt_cons_wf_rec, native_and]
        have hComp : __smtx_type_wf_component U = true :=
          Smtm.smtx_type_wf_component_of_parts hParts.1 hParts.2
        cases U <;>
          simp_all [__smtx_type_wf, __smtx_type_wf_component,
            __smtx_type_wf_rec, __smtx_dt_resolve,
            __smtx_dtc_resolve, __smtx_ret_typeof_sel_rec, native_and]
  | SmtDatatypeCons.cons U c, Nat.succ j, hWf, hOuterWf, hJ => by
      have hTailWf :
          __smtx_dt_cons_wf_rec
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum c₀ SmtDatatype.null)) c = true := by
        cases U <;>
          simp_all [__smtx_dt_cons_wf_rec, native_and]
      have hTailJ : j < __smtx_dtc_num_sels c := by
        simpa [__smtx_dtc_num_sels] using hJ
      have hTail :=
        qds_tuple_ret_type_wf_aux c₀ c j hTailWf hOuterWf hTailJ
      cases U <;>
        simpa [__smtx_dt_resolve, __smtx_dtc_resolve,
          __smtx_ret_typeof_sel_rec] using hTail

private theorem qds_tuple_ret_type_wf
    (c : SmtDatatypeCons) (j : native_Nat)
    (hWf :
      __smtx_dt_cons_wf_rec
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)) c = true)
    (hOuterWf :
      __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null))) = true)
    (hJ : j < __smtx_dtc_num_sels c) :
    __smtx_type_wf
      (__smtx_ret_typeof_sel_rec
        (__smtx_dt_resolve
          (SmtDatatype.sum c SmtDatatype.null)
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)))
        native_nat_zero j) = true :=
  qds_tuple_ret_type_wf_aux c c j hWf hOuterWf hJ

private theorem qds_tuple_selector_type
    (tail : SmtTerm) (c : SmtDatatypeCons) (j : native_Nat)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null))) = true)
    (hJ : j < __smtx_dtc_num_sels c) :
    __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.DtSel (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum c SmtDatatype.null))
              native_nat_zero j) tail) =
        __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve
            (SmtDatatype.sum c SmtDatatype.null)
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum c SmtDatatype.null)))
          native_nat_zero j ∧
      __smtx_type_wf
          (__smtx_ret_typeof_sel_rec
            (__smtx_dt_resolve
              (SmtDatatype.sum c SmtDatatype.null)
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum c SmtDatatype.null)))
            native_nat_zero j) = true := by
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let tailDD := __eo_to_smt_tuple_decl tailD
  have hConsWf : __smtx_dt_cons_wf_rec tailDD c = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hTailWf
    simpa [tailDD, tailD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      __smtx_dt_wf_rec, native_streq, native_ite, native_and] using hDtWf
  have hRetWf := qds_tuple_ret_type_wf c j hConsWf hTailWf hJ
  let R := __smtx_ret_typeof_sel_rec
    (__smtx_dt_resolve tailD tailDD) native_nat_zero j
  have hRetWfR : __smtx_type_wf R = true := by
    simpa [R, tailD, tailDD] using hRetWf
  have hRNN : R ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hRetWfR
    exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hRetWfR
  constructor
  · rw [Smtm.typeof_dt_sel_apply_eq]
    change __smtx_typeof_guard_wf R
      (__smtx_typeof_apply
        (SmtType.FunType
          (SmtType.Datatype (native_string_lit "@Tuple") tailDD) R)
        (__smtx_typeof tail)) = R
    rw [hTailTy]
    simp [R, tailDD, tailD, __smtx_typeof_apply,
      __smtx_typeof_guard, __smtx_typeof_guard_wf,
      hRetWfR, native_ite, native_Teq]
  · exact hRetWf

theorem qds_tuple_ret_type_wf_of_eo_type
    (T : Term) (c : SmtDatatypeCons) (j : native_Nat)
    (hShape : __eo_to_smt_type T =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)))
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hJ : j < __smtx_dtc_num_sels c) :
    __smtx_type_wf
      (__smtx_ret_typeof_sel_rec
        (__smtx_dt_resolve
          (SmtDatatype.sum c SmtDatatype.null)
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)))
        native_nat_zero j) = true := by
  let tailTy := SmtType.Datatype (native_string_lit "@Tuple")
    (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
  let tail := SmtTerm.Var (native_string_lit "@qds-tail") tailTy
  have hTailWf : __smtx_type_wf tailTy = true :=
    (congrArg __smtx_type_wf hShape).symm.trans hWf
  have hTailTy : __smtx_typeof tail = tailTy := by
    simp [tail, smtx_typeof_var_term_eq, __smtx_typeof_guard_wf,
      hTailWf, native_ite]
  exact (qds_tuple_selector_type tail c j
    (by simpa [tailTy] using hTailTy)
    (by simpa [tailTy] using hTailWf) hJ).2

private theorem qds_tuple_prepend_rec_head
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail acc : SmtTerm) : ∀ k,
    qdsSmtApplyHead
        (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
      qdsSmtApplyHead acc
  | 0 => by simp [__eo_to_smt_tuple_prepend_rec]
  | Nat.succ k => by
      simp [__eo_to_smt_tuple_prepend_rec, qdsSmtApplyHead,
        qds_tuple_prepend_rec_head tailDD tailD tail acc k]

private theorem qds_tuple_resolved_head
    (A : SmtType) (c : SmtDatatypeCons)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hFullWf :
      __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum
              (SmtDatatypeCons.cons A c) SmtDatatype.null))) = true) :
    let fullD :=
      SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    let fullDD := __eo_to_smt_tuple_decl fullD
    __smtx_ret_typeof_sel_rec
        (__smtx_dt_resolve fullD fullDD) native_nat_zero native_nat_zero =
      A := by
  intro fullD fullDD
  have hConsWf :
      __smtx_dt_cons_wf_rec fullDD (SmtDatatypeCons.cons A c) = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hFullWf
    simpa [fullDD, fullD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      __smtx_dt_wf_rec, native_streq, native_ite, native_and] using hDtWf
  cases hA : A with
  | TypeRef s =>
      have hHas : __smtx_dd_has_dt s fullDD = true := by
        have hPair :
            __smtx_dd_has_dt s fullDD = true ∧
              __smtx_dt_cons_wf_rec fullDD c = true := by
          simpa only [hA, __smtx_dt_cons_wf_rec, native_and,
            Bool.and_eq_true] using hConsWf
        exact hPair.1
      have hs : s = native_string_lit "@Tuple" := by
        simpa [fullDD, __eo_to_smt_tuple_decl, __smtx_dd_has_dt,
          native_streq, native_or] using hHas
      subst s
      exact False.elim (hANotTuple hA)
  | _ =>
      simp [fullDD, fullD, hA, __smtx_dt_resolve,
        __smtx_dtc_resolve, __smtx_ret_typeof_sel_rec]

private theorem qds_tuple_seed_type
    (head : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum
            (SmtDatatypeCons.cons A c) SmtDatatype.null))) = true) :
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    let fullDD := __eo_to_smt_tuple_decl fullD
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero)
          head) =
      dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
        (__smtx_dt_resolve fullD fullDD) native_nat_zero 1 := by
  intro fullD fullDD
  have hResolvedHead :
      __smtx_ret_typeof_sel_rec
          (__smtx_dt_resolve fullD fullDD) native_nat_zero native_nat_zero =
        A := by
    simpa [fullD, fullDD] using
      qds_tuple_resolved_head A c hANotTuple hFullWf
  let resolved := __smtx_dt_resolve fullD fullDD
  let R := __smtx_ret_typeof_sel_rec resolved native_nat_zero native_nat_zero
  let Rest := dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
    resolved native_nat_zero 1
  have hR : R = A := by simpa [R, resolved] using hResolvedHead
  have hANone : A ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hHeadWf
    exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hHeadWf
  have hLt : 0 < __smtx_dt_num_sels resolved native_nat_zero := by
    cases A <;>
      simp [resolved, fullD, fullDD, __smtx_dt_resolve,
        __smtx_dtc_resolve, __smtx_dt_num_sels, __smtx_dtc_num_sels]
  have hStep :
      dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
          resolved native_nat_zero 0 =
        SmtType.DtcAppType R Rest := by
    simpa [R, Rest] using
      dt_cons_applied_type_rec_step (native_string_lit "@Tuple") fullDD
        resolved native_nat_zero 0 hLt
  have hRootTy :
      __smtx_typeof
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
            native_nat_zero) =
        dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
          resolved native_nat_zero 0 := by
    rw [Smtm.typeof_dt_cons_eq]
    unfold __smtx_typeof_guard_wf
    rw [hFullWf]
    simp only [native_ite, dt_cons_applied_type_rec_zero]
    simpa [resolved, fullD, fullDD, __eo_to_smt_tuple_decl,
      __smtx_dd_lookup, native_streq, native_ite] using
      (typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
        (SmtType.Datatype (native_string_lit "@Tuple") fullDD)
        resolved native_nat_zero).symm
  change __smtx_typeof_apply
      (__smtx_typeof
        (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero))
      (__smtx_typeof head) = Rest
  rw [hRootTy, hHeadTy]
  exact qds_smt_typeof_apply_of_head_cases
    (Or.inr hStep) (by simp [hR]) (by simpa [hR] using hANone)

private theorem qds_tuple_prepend_rec_type
    (head tail : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null))) = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hCNoRef : qdsNoTupleRefDtc c)
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum
            (SmtDatatypeCons.cons A c) SmtDatatype.null))) = true) :
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let tailDD := __eo_to_smt_tuple_decl tailD
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    let fullDD := __eo_to_smt_tuple_decl fullD
    let resolvedFull := __smtx_dt_resolve fullD fullDD
    let seed := SmtTerm.Apply
      (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero) head
    ∀ k, k ≤ __smtx_dtc_num_sels c ->
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k seed) =
        dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
          resolvedFull native_nat_zero (Nat.succ k) := by
  intro tailD tailDD fullD fullDD resolvedFull seed k hK
  have hTailConsWf : __smtx_dt_cons_wf_rec tailDD c = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hTailWf
    simpa [tailDD, tailD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      __smtx_dt_wf_rec, native_streq, native_ite, native_and] using hDtWf
  have hTailResolveCons :
      __smtx_dtc_resolve c tailDD = c := by
    simpa [tailDD, tailD] using
      qds_tuple_resolve_cons_noop c c hTailConsWf hCNoRef
  have hTailResolve : __smtx_dt_resolve tailD tailDD = tailD := by
    simp [tailD, __smtx_dt_resolve, hTailResolveCons]
  have hFullConsWf :
      __smtx_dt_cons_wf_rec fullDD (SmtDatatypeCons.cons A c) = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hFullWf
    simpa [fullDD, fullD, __eo_to_smt_tuple_decl, __smtx_dd_lookup,
      __smtx_dt_wf_rec, native_streq, native_ite, native_and] using hDtWf
  have hFullResolveCons :
      __smtx_dtc_resolve (SmtDatatypeCons.cons A c) fullDD =
        SmtDatatypeCons.cons A c := by
    simpa [fullDD, fullD] using
      qds_tuple_resolve_cons_noop (SmtDatatypeCons.cons A c)
        (SmtDatatypeCons.cons A c) hFullConsWf ⟨hANotTuple, hCNoRef⟩
  have hFullResolve : resolvedFull = fullD := by
    simp [resolvedFull, fullD, __smtx_dt_resolve, hFullResolveCons]
  induction k with
  | zero =>
      simpa [tailD, tailDD, fullD, fullDD, resolvedFull, seed,
        __eo_to_smt_tuple_prepend_rec] using
        qds_tuple_seed_type head A c hHeadTy hHeadWf hANotTuple hFullWf
  | succ k ih =>
      have hKLe : k ≤ __smtx_dtc_num_sels c := Nat.le_trans (Nat.le_succ k) hK
      have hKLt : k < __smtx_dtc_num_sels c := Nat.lt_of_succ_le hK
      let recTerm :=
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail k seed
      let selTerm := SmtTerm.Apply
        (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD native_nat_zero k)
        tail
      have hRecTy : __smtx_typeof recTerm =
          dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD
            resolvedFull native_nat_zero (Nat.succ k) := ih hKLe
      have hChainLt :
          Nat.succ k < __smtx_dt_num_sels resolvedFull native_nat_zero := by
        rw [show __smtx_dt_num_sels resolvedFull native_nat_zero =
            __smtx_dt_num_sels fullD native_nat_zero by
          simpa [resolvedFull] using
            dt_num_sels_resolve fullDD fullD native_nat_zero]
        simpa [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels] using
          Nat.succ_lt_succ hKLt
      have hStep := dt_cons_applied_type_rec_step
        (native_string_lit "@Tuple") fullDD resolvedFull native_nat_zero
          (Nat.succ k) hChainLt
      have hSel := qds_tuple_selector_type tail c k hTailTy hTailWf hKLt
      have hSelTy : __smtx_typeof selTerm =
          __smtx_ret_typeof_sel_rec resolvedFull native_nat_zero
            (Nat.succ k) := by
        simpa [selTerm, tailD, tailDD, fullD, fullDD, resolvedFull,
          hTailResolve, hFullResolve,
          __smtx_ret_typeof_sel_rec] using hSel.1
      have hSelNN : __smtx_ret_typeof_sel_rec resolvedFull native_nat_zero
          (Nat.succ k) ≠ SmtType.None := by
        intro hNone
        have hWf := hSel.2
        rw [show __smtx_ret_typeof_sel_rec
            (__smtx_dt_resolve tailD tailDD) native_nat_zero k =
              __smtx_ret_typeof_sel_rec resolvedFull native_nat_zero
                (Nat.succ k) by
          simp [tailD, tailDD, fullD, fullDD, resolvedFull,
            hTailResolve, hFullResolve,
            __smtx_ret_typeof_sel_rec]] at hWf
        rw [hNone] at hWf
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hWf
      have hRecHead : qdsSmtApplyHead recTerm =
          SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
            native_nat_zero := by
        simp [recTerm, qds_tuple_prepend_rec_head, seed, qdsSmtApplyHead]
      have hNotSel : ∀ s d i j,
          recTerm ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        rw [hEq] at hRecHead
        simp [qdsSmtApplyHead] at hRecHead
      have hNotTester : ∀ s d i,
          recTerm ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        rw [hEq] at hRecHead
        simp [qdsSmtApplyHead] at hRecHead
      have hGeneric : generic_apply_type recTerm selTerm :=
        generic_apply_type_of_non_datatype_head hNotSel hNotTester
      simp only [__eo_to_smt_tuple_prepend_rec]
      rw [hGeneric]
      exact qds_smt_typeof_apply_of_head_cases
        (Or.inr (hRecTy.trans hStep)) hSelTy hSelNN

theorem qds_dtc_full_arity
    (s : native_String) (d0 : SmtDatatypeDecl) : ∀ c : SmtDatatypeCons,
    dt_cons_applied_type_rec s d0 (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero (__smtx_dtc_num_sels c) =
      SmtType.Datatype s d0
  | SmtDatatypeCons.unit => by
      rw [show __smtx_dtc_num_sels SmtDatatypeCons.unit = 0 by rfl]
      rw [dt_cons_applied_type_rec_zero]
      simp [__smtx_typeof_dt_cons_value_rec]
  | SmtDatatypeCons.cons U c => by
      rw [show __smtx_dtc_num_sels (SmtDatatypeCons.cons U c) =
        Nat.succ (__smtx_dtc_num_sels c) by rfl]
      rw [dt_cons_applied_type_rec_cons_succ]
      exact qds_dtc_full_arity s d0 c

private theorem qds_tuple_full_arity
    (A : SmtType) (c : SmtDatatypeCons) :
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    let fullDD := __eo_to_smt_tuple_decl fullD
    let resolvedFull := __smtx_dt_resolve fullD fullDD
    dt_cons_applied_type_rec (native_string_lit "@Tuple") fullDD resolvedFull
        native_nat_zero (__smtx_dt_num_sels resolvedFull native_nat_zero) =
      SmtType.Datatype (native_string_lit "@Tuple") fullDD := by
  intro fullD fullDD resolvedFull
  simpa [resolvedFull, fullD, __smtx_dt_resolve,
    __smtx_dt_num_sels] using
    qds_dtc_full_arity (native_string_lit "@Tuple") fullDD
      (__smtx_dtc_resolve (SmtDatatypeCons.cons A c) fullDD)

private theorem qds_tuple_prepend_non_none
    (head tail : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null))) = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hCNoRef : qdsNoTupleRefDtc c)
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum
            (SmtDatatypeCons.cons A c) SmtDatatype.null))) = true) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head A tail) ≠ SmtType.None := by
  unfold __eo_to_smt_tuple_prepend
  rw [hTailTy]
  have hFullWf' :
      __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple")
            (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
              (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null)
              SmtDatatypeDecl.nil)) = true := by
    simpa [__eo_to_smt_tuple_decl] using hFullWf
  simp [__eo_to_smt_tuple_prepend_of_type, __eo_to_smt_tuple_decl,
    native_streq, native_and, native_ite]
  rw [hFullWf']
  simp only [if_true]
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let tailDD := __eo_to_smt_tuple_decl tailD
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
  let fullDD := __eo_to_smt_tuple_decl fullD
  let resolvedFull := __smtx_dt_resolve fullD fullDD
  let seed := SmtTerm.Apply
    (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero) head
  have hRec := qds_tuple_prepend_rec_type head tail A c hHeadTy hHeadWf
    hTailTy hTailWf hANotTuple hCNoRef hFullWf
    (__smtx_dtc_num_sels c) (Nat.le_refl _)
  have hCount : Nat.succ (__smtx_dtc_num_sels c) =
      __smtx_dt_num_sels resolvedFull native_nat_zero := by
    rw [show __smtx_dt_num_sels resolvedFull native_nat_zero =
        __smtx_dt_num_sels fullD native_nat_zero by
      simpa [resolvedFull] using
        dt_num_sels_resolve fullDD fullD native_nat_zero]
    simp [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels]
  change __smtx_typeof
      (__eo_to_smt_tuple_prepend_rec tailDD tailD tail
        (__smtx_dtc_num_sels c) seed) ≠ SmtType.None
  rw [hRec, hCount, qds_tuple_full_arity A c]
  simp

theorem ctor_spine_translation {T c : Term} (hs : CS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    RuleProofs.eo_has_smt_translation c := by
  rcases cs_cases hs with hD | hT | hU
  · exact dcs_translation hD hEq hWf
  · obtain ⟨s₁, U₁, s₂, U₂, hFull, hU₁Wf, hU₂Wf⟩ :=
      tcs_full hT hEq hWf
    subst c
    subst T
    have hTypeWf : __smtx_type_wf
        (__eo_to_smt_type (__eo_typeof_tuple U₁ U₂)) = true := by
      exact hWf
    have hTypeEq := qds_typeof_tuple_eq_of_wf U₁ U₂ hTypeWf
    have hExplicitWf : __smtx_type_wf
        (__eo_to_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) U₁) U₂)) = true := by
      rw [← hTypeEq]
      exact hTypeWf
    obtain ⟨tailC, hTailShape, hFullShape⟩ :=
      qds_tuple_type_shape_of_wf U₁ U₂ hExplicitWf
    have hHeadTy : __smtx_typeof
        (__eo_to_smt (Term.Var (Term.String s₁) U₁)) =
          __eo_to_smt_type U₁ := by
      rw [TranslationProofs.eo_to_smt_var, smtx_typeof_var_term_eq]
      simp [__smtx_typeof_guard_wf, hU₁Wf, native_ite]
    have hTailTupleWf : __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum tailC SmtDatatype.null))) = true := by
      exact (congrArg __smtx_type_wf hTailShape).symm.trans hU₂Wf
    have hTailTy : __smtx_typeof
        (__eo_to_smt (Term.Var (Term.String s₂) U₂)) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum tailC SmtDatatype.null)) := by
      rw [TranslationProofs.eo_to_smt_var]
      rw [smtx_typeof_var_term_eq]
      simp [__smtx_typeof_guard_wf, hTailShape, hTailTupleWf, native_ite]
    have hFullTupleWf : __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum
              (SmtDatatypeCons.cons (__eo_to_smt_type U₁) tailC)
              SmtDatatype.null))) = true := by
      exact (congrArg __smtx_type_wf hFullShape).symm.trans hExplicitWf
    have hANotTuple : __eo_to_smt_type U₁ ≠
        SmtType.TypeRef (native_string_lit "@Tuple") :=
      TranslationProofs.eo_to_smt_type_ne_tuple_typeref U₁
    have hCNoRef := qds_tuple_fields_no_tuple_ref hTailShape
    unfold RuleProofs.eo_has_smt_translation
    change __smtx_typeof
      (__eo_to_smt_tuple_prepend
        (__eo_to_smt (Term.Var (Term.String s₁) U₁))
        (__smtx_typeof (__eo_to_smt (Term.Var (Term.String s₁) U₁)))
        (__eo_to_smt (Term.Var (Term.String s₂) U₂))) ≠ SmtType.None
    rw [hHeadTy]
    exact qds_tuple_prepend_non_none
      (__eo_to_smt (Term.Var (Term.String s₁) U₁))
      (__eo_to_smt (Term.Var (Term.String s₂) U₂))
      (__eo_to_smt_type U₁) tailC hHeadTy hU₁Wf hTailTy hTailTupleWf
      hANotTuple hCNoRef hFullTupleWf
  · have hFull := ucs_full hU hEq hWf
    subst c
    unfold RuleProofs.eo_has_smt_translation
    rw [TranslationProofs.eo_to_smt_term_tuple_unit,
      TranslationProofs.smtx_typeof_tuple_unit_translation]
    simp

end QuantDtSplitRule
