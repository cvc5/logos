module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

attribute [local simp] native_ite native_teq native_not native_zplus

def eoDatatypeNumCtors : Datatype -> Nat
  | Datatype.null => 0
  | Datatype.sum _ d => Nat.succ (eoDatatypeNumCtors d)

def smtDatatypeNumCtors : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ d => Nat.succ (smtDatatypeNumCtors d)

theorem smtDatatypeNumCtors_eo_to_smt :
    ∀ d : Datatype,
      smtDatatypeNumCtors (__eo_to_smt_datatype d) = eoDatatypeNumCtors d
  | Datatype.null => by
      simp [smtDatatypeNumCtors, eoDatatypeNumCtors, __eo_to_smt_datatype]
  | Datatype.sum c d => by
      simp [smtDatatypeNumCtors, eoDatatypeNumCtors, __eo_to_smt_datatype,
        smtDatatypeNumCtors_eo_to_smt d]

theorem smtDatatypeNumCtors_resolve
    (dd : SmtDatatypeDecl) :
    ∀ d : SmtDatatype,
      smtDatatypeNumCtors (__smtx_dt_resolve d dd) =
        smtDatatypeNumCtors d
  | SmtDatatype.null => by
      simp [smtDatatypeNumCtors, __smtx_dt_resolve]
  | SmtDatatype.sum c d => by
      simp [smtDatatypeNumCtors, __smtx_dt_resolve,
        smtDatatypeNumCtors_resolve dd d]

theorem dt_cons_applied_type_rec_non_none_implies_lt_ctors
    (s : native_String) (d0 : SmtDatatypeDecl) :
    ∀ {d : SmtDatatype} {i n : Nat},
      dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None ->
      i < smtDatatypeNumCtors d
  | SmtDatatype.null, i, n, h => by
      exact False.elim (h (dt_cons_applied_type_rec_null s d0 i n))
  | SmtDatatype.sum c d, 0, n, h => by
      simp [smtDatatypeNumCtors]
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      have h' : dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None := by
        simpa only [dt_cons_applied_type_rec_succ] using h
      have hlt := dt_cons_applied_type_rec_non_none_implies_lt_ctors
        s d0 (d := d) (i := i) (n := n) h'
      simpa [smtDatatypeNumCtors] using Nat.succ_lt_succ hlt

theorem smt_typeof_dt_cons_rec_non_none_implies_lt_ctors
    (T : SmtType) :
    ∀ {d : SmtDatatype} {i : Nat},
      __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None ->
      i < smtDatatypeNumCtors d
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec] at h
  | SmtDatatype.sum c d, 0, _h => by
      simp [smtDatatypeNumCtors]
  | SmtDatatype.sum c d, Nat.succ i, h => by
      have h' : __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None := by
        cases c <;> simpa [__smtx_typeof_dt_cons_rec] using h
      have hlt := smt_typeof_dt_cons_rec_non_none_implies_lt_ctors
        T (d := d) (i := i) h'
      simpa [smtDatatypeNumCtors] using Nat.succ_lt_succ hlt

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem eo_datatype_constructors_rec_ne_stuck
    (s : native_String) (dd : DatatypeDecl) :
    ∀ current start,
      __eo_datatype_constructors_rec s dd current start ≠ Term.Stuck
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      have hTail : tail ≠ Term.Stuck :=
        eo_datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s dd start)) tail ≠
          Term.Stuck
      rw [eo_mk_apply_of_ne_stuck (by simp) hTail]
      simp

theorem eo_get_nil_rec_datatype_constructors_rec
    (s : native_String) (dd : DatatypeDecl) :
    ∀ current start,
      __eo_get_nil_rec Term.__eo_List_cons
        (__eo_datatype_constructors_rec s dd current start) =
      Term.__eo_List_nil
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec, __eo_get_nil_rec,
        __eo_is_list_nil, __eo_requires]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        eo_datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      have ih :
          __eo_get_nil_rec Term.__eo_List_cons tail = Term.__eo_List_nil :=
        eo_get_nil_rec_datatype_constructors_rec s dd d (Nat.succ start)
      change
        __eo_get_nil_rec Term.__eo_List_cons
          (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s dd start)) tail) =
        Term.__eo_List_nil
      rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
      simp [__eo_get_nil_rec, __eo_requires, ih]

private theorem eo_is_list_of_get_nil_rec_eq_nil
    {x : Term}
    (hx : x ≠ Term.Stuck)
    (hGet : __eo_get_nil_rec Term.__eo_List_cons x = Term.__eo_List_nil) :
    __eo_is_list Term.__eo_List_cons x = Term.Boolean true := by
  cases x <;> simp [__eo_is_list, __eo_is_ok, hGet] at hx ⊢

theorem eo_is_list_datatype_constructors_rec
    (s : native_String) (dd : DatatypeDecl) :
    ∀ current start,
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s dd current start) =
      Term.Boolean true := by
  intro current start
  have hGet :
      __eo_get_nil_rec Term.__eo_List_cons
        (__eo_datatype_constructors_rec s dd current start) =
      Term.__eo_List_nil :=
    eo_get_nil_rec_datatype_constructors_rec s dd current start
  exact eo_is_list_of_get_nil_rec_eq_nil
    (eo_datatype_constructors_rec_ne_stuck s dd current start) hGet

theorem eo_list_len_rec_datatype_constructors_rec
    (s : native_String) (dd : DatatypeDecl) :
    ∀ current start,
      __eo_list_len_rec (__eo_datatype_constructors_rec s dd current start) =
        Term.Numeral (Int.ofNat (eoDatatypeNumCtors current))
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec, __eo_list_len_rec,
        eoDatatypeNumCtors]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s dd d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        eo_datatype_constructors_rec_ne_stuck s dd d (Nat.succ start)
      have ih :=
        eo_list_len_rec_datatype_constructors_rec s dd d (Nat.succ start)
      change
        __eo_list_len_rec
          (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s dd start)) tail) =
        Term.Numeral (Int.ofNat (eoDatatypeNumCtors (Datatype.sum c d)))
      rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
      change
        __eo_add (Term.Numeral 1) (__eo_list_len_rec tail) =
          Term.Numeral (Int.ofNat (eoDatatypeNumCtors (Datatype.sum c d)))
      rw [show
          __eo_list_len_rec tail =
            Term.Numeral (Int.ofNat (eoDatatypeNumCtors d)) by
        exact ih]
      simp [__eo_add, eoDatatypeNumCtors]
      rw [Int.add_comm]

theorem eo_list_len_dt_get_constructors_datatype
    (s : native_String) (dd : DatatypeDecl) :
    __eo_list_len Term.__eo_List_cons
        (__dt_get_constructors (Term.DatatypeType s dd)) =
      Term.Numeral (Int.ofNat (eoDatatypeNumCtors (__eo_dd_lookup s dd))) := by
  have hList :
      __eo_is_list Term.__eo_List_cons
          (__eo_datatype_constructors_rec s dd (__eo_dd_lookup s dd) native_nat_zero) =
        Term.Boolean true :=
    eo_is_list_datatype_constructors_rec s dd (__eo_dd_lookup s dd) native_nat_zero
  have hLen :
      __eo_list_len_rec
          (__eo_datatype_constructors_rec s dd (__eo_dd_lookup s dd) native_nat_zero) =
        Term.Numeral (Int.ofNat (eoDatatypeNumCtors (__eo_dd_lookup s dd))) :=
    eo_list_len_rec_datatype_constructors_rec
      s dd (__eo_dd_lookup s dd) native_nat_zero
  simp [__dt_get_constructors, __eo_dt_constructors, __eo_list_len,
    __eo_requires, hList, hLen]

theorem datatype_value_head_of_type
    {v : SmtValue} {s : native_String} {dd : SmtDatatypeDecl}
    (hTy : __smtx_typeof_value v = SmtType.Datatype s dd) :
    ∃ i, __smtx_apply_head_value v = SmtValue.DtCons s dd i := by
  by_cases hHead : ∃ s0 d0 i0, __smtx_apply_head_value v = SmtValue.DtCons s0 d0 i0
  · rcases hHead with ⟨s0, d0, i0, hHead⟩
    have hChain :=
      dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
    have hEq :
        dt_cons_applied_type_rec s0 d0
            (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
            (vsm_num_apply_args v) =
          SmtType.Datatype s dd := by
      exact hChain.symm.trans hTy
    have hArgsZero :
        __smtx_dt_num_sels
            (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0 -
            vsm_num_apply_args v =
          0 := by
      have hArgs := congrArg dt_cons_type_num_args hEq
      rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
      simpa only [dt_cons_type_num_args_datatype] using hArgs
    have hle :
        vsm_num_apply_args v ≤
          __smtx_dt_num_sels
            (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0 :=
      dt_cons_applied_type_rec_non_none_implies_le s0 d0
        (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
        (vsm_num_apply_args v) (by rw [hEq]; simp)
    have hCount :
        vsm_num_apply_args v =
          __smtx_dt_num_sels
            (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0 := by
      have hge :
          __smtx_dt_num_sels
              (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0 ≤
            vsm_num_apply_args v :=
        (Nat.sub_eq_zero_iff_le).1 hArgsZero
      exact Nat.le_antisymm hle hge
    have hFull :
        dt_cons_applied_type_rec s0 d0
            (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
            (__smtx_dt_num_sels
              (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0) =
          SmtType.Datatype s0 d0 :=
      dt_cons_applied_type_rec_full_arity s0 d0
        (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
        (by rw [← hCount, hEq]; simp)
    have hBase : SmtType.Datatype s0 d0 = SmtType.Datatype s dd := by
      calc
        SmtType.Datatype s0 d0 =
            dt_cons_applied_type_rec s0 d0
              (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
              (__smtx_dt_num_sels
                (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0) := by
          exact hFull.symm
        _ =
            dt_cons_applied_type_rec s0 d0
              (__smtx_dt_resolve (__smtx_dd_lookup s0 d0) d0) i0
              (vsm_num_apply_args v) := by rw [hCount]
        _ = SmtType.Datatype s dd := hEq
    injection hBase with hs hd
    subst hs
    subst hd
    exact ⟨i0, hHead⟩
  · cases v with
    | NotValue => simp [__smtx_typeof_value] at hTy
    | Boolean _ => simp [__smtx_typeof_value] at hTy
    | Numeral _ => simp [__smtx_typeof_value] at hTy
    | Rational _ => simp [__smtx_typeof_value] at hTy
    | Binary w n =>
        cases hWidth : native_zleq 0 w <;>
          cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and,
            hWidth, hMod] at hTy
    | Map m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            simp [__smtx_typeof_value, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Set m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hTy
    | Fun _ _ _ => simp [__smtx_typeof_value] at hTy
    | Seq ss =>
        cases typeof_seq_value_shape ss with
        | inl hSeq =>
            rcases hSeq with ⟨A, hSeq⟩
            simp [__smtx_typeof_value, hSeq] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Char c =>
        cases hValid : native_char_valid c <;>
          simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at hTy
    | UValue _ _ => simp [__smtx_typeof_value] at hTy
    | RegLan _ => simp [__smtx_typeof_value] at hTy
    | DtCons s0 d0 i0 =>
        exact False.elim (hHead ⟨s0, d0, i0, by simp [__smtx_apply_head_value]⟩)
    | Apply f a =>
        have hNone :
            __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
          typeof_value_apply_of_head_ne_dt_cons f a
            (by
              intro s0 d0 i0 hf
              exact hHead ⟨s0, d0, i0, by simpa [__smtx_apply_head_value] using hf⟩)
        rw [hNone] at hTy
        cases hTy

theorem datatype_head_index_lt
    {v : SmtValue} {s : native_String} {dd : SmtDatatypeDecl} {i : Nat}
    (hHead : __smtx_apply_head_value v = SmtValue.DtCons s dd i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s dd) :
    i < smtDatatypeNumCtors (__smtx_dd_lookup s dd) := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
  have hNN :
      dt_cons_applied_type_rec s dd
          (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) i
          (vsm_num_apply_args v) ≠ SmtType.None := by
    rw [← hChain, hTy]
    simp
  have hltSub := dt_cons_applied_type_rec_non_none_implies_lt_ctors
    s dd (d := __smtx_dt_resolve (__smtx_dd_lookup s dd) dd) (i := i)
    (n := vsm_num_apply_args v) hNN
  simpa [smtDatatypeNumCtors_resolve dd (__smtx_dd_lookup s dd)] using hltSub

theorem unit_tuple_value_head_zero_of_type
    {v : SmtValue}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
            SmtDatatypeDecl.nil)) :
    __smtx_apply_head_value v =
      SmtValue.DtCons (native_string_lit "@Tuple")
        (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
          SmtDatatypeDecl.nil)
        native_nat_zero := by
  rcases datatype_value_head_of_type hTy with ⟨i, hHead⟩
  have hlt := datatype_head_index_lt hHead hTy
  have hi : i = native_nat_zero := by
    simpa [__smtx_dd_lookup, native_ite, native_streq,
      smtDatatypeNumCtors] using hlt
  subst i
  exact hHead
