module

public import CpcMini.Proofs.TypePreservation
import all CpcMini.Proofs.TypePreservation
public import CpcMini.Proofs.Translation.EoTypeof
import all CpcMini.Proofs.Translation.EoTypeof
public import CpcMini.Proofs.Translation.Apply
import all CpcMini.Proofs.Translation.Apply

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


namespace RuleProofs

attribute [local simp] native_ite
attribute [local simp] Smtm.__smtx_type_wf_component

/-- Derives `eo_typeof_eq_self` from `not_stuck`. -/
private theorem eo_typeof_eq_self_of_not_stuck
    (A : Term)
    (hA : A ≠ Term.Stuck) :
    __eo_typeof_eq A A = Term.Bool := by
  cases A <;>
    try simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_teq, native_ite, native_not,
      SmtEval.native_not]
  exact False.elim (hA rfl)

/-- A translated datatype-constructor application type is never an SMT function type. -/
private theorem smtx_typeof_guard_dtc_app_ne_fun
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.FunType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT constructor-application type. -/
private theorem smtx_typeof_guard_fun_ne_dtc_app
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠ SmtType.DtcAppType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT constructor-application type. -/
private theorem smtx_typeof_guard_seq_ne_dtc_app
    (T A B : SmtType) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.DtcAppType A B := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Derives `eo_typeof_bool` from `smt_bool`. -/
private theorem eo_to_smt_type_eq_bool
    {T : Term} :
    __eo_to_smt_type T = SmtType.Bool ->
    T = Term.Bool :=
  TranslationProofs.eo_to_smt_type_eq_bool

/-- Derives `eo_typeof_bool` from `smt_bool`. -/
private theorem eo_typeof_bool_of_smt_bool
    {t : Term}
    (hRec : __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (hBool : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  have hTy : __eo_to_smt_type (__eo_typeof t) = SmtType.Bool := by
    rw [← hRec, hBool]
  exact eo_to_smt_type_eq_bool hTy

/-- Characterizes `__smtx_typeof_guard` producing a function type. -/
private theorem smtx_typeof_guard_eq_fun_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.FunType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.FunType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT function type. -/
private theorem eo_to_smt_type_eq_fun_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.FunType A B ↔
      ∃ T1 T2,
        T = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None :=
  TranslationProofs.eo_to_smt_type_eq_fun_iff

/-- Characterizes `__smtx_typeof_guard` producing a constructor-application type. -/
private theorem smtx_typeof_guard_eq_dtc_app_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.DtcAppType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT constructor-application type. -/
private theorem eo_to_smt_type_eq_dtc_app_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.DtcAppType A B ↔
      ∃ T1 T2,
        T = Term.DtcAppType T1 T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None :=
  TranslationProofs.eo_to_smt_type_eq_dtc_app_iff

/-- Characterizes translated EO types equal to an SMT datatype. -/
private theorem eo_to_smt_type_eq_datatype_iff
    {T : Term} {s : native_String} {d : SmtDatatypeDecl} :
    __eo_to_smt_type T = SmtType.Datatype s d ↔
      ∃ d0,
        T = Term.DatatypeType s d0 ∧
        __eo_to_smt_reserved_datatype_name s = false ∧
        __eo_to_smt_datatype_decl d0 = d :=
  TranslationProofs.eo_to_smt_type_eq_datatype_iff

/-- Characterizes translated EO types equal to an SMT type reference. -/
private theorem eo_to_smt_type_eq_typeref_iff
    {T : Term} {s : native_String} :
    __eo_to_smt_type T = SmtType.TypeRef s ↔
      T = Term.DatatypeTypeRef s ∧ __eo_to_smt_reserved_datatype_name s = false :=
  TranslationProofs.eo_to_smt_type_eq_typeref_iff

/-- Characterizes translated EO types equal to an SMT bit-vector type. -/
private theorem eo_to_smt_type_eq_bitvec_iff
    {T : Term} {w : native_Nat} :
    __eo_to_smt_type T = SmtType.BitVec w ↔
      ∃ n : native_Int,
        T = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
        native_zleq 0 n = true ∧
        native_int_to_nat n = w :=
  TranslationProofs.eo_to_smt_type_eq_bitvec_iff

/-- Extracts operand SMT typing information from a non-`None` equality term. -/
private theorem smtx_typeof_eq_operands_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof t1 = __smtx_typeof t2 ∧
      __smtx_typeof t1 ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
      native_ite, native_Teq, h1, h2] at ht ⊢
  all_goals
    exact ht

/-- Computes EO typing for generic double applications. -/
private theorem eo_typeof_double_apply_generic
    (g y x : Term)
    (hFun : g ≠ Term.FunType)
    (hAnd : g ≠ Term.UOp UserOp.and)
    (hImp : g ≠ Term.UOp UserOp.imp)
    (hEq : g ≠ Term.UOp UserOp.eq) :
    __eo_typeof (Term.Apply (Term.Apply g y) x) =
      __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x) := by
  cases g <;> try rfl
  case FunType =>
      exact False.elim (hFun rfl)
  case UOp op =>
      cases op <;> try rfl
      case and =>
          exact False.elim (hAnd rfl)
      case imp =>
          exact False.elim (hImp rfl)
      case eq =>
          exact False.elim (hEq rfl)

/-- Computes EO typing for generic single applications. -/
private theorem eo_typeof_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hBitVec : f ≠ Term.UOp UserOp.BitVec)
    (hSeq : f ≠ Term.UOp UserOp.Seq)
    (hListCons : f ≠ Term.__eo_List_cons)
    (hNot : f ≠ Term.UOp UserOp.not) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case UOp op =>
      cases op <;> try rfl
      case BitVec =>
          exact False.elim (hBitVec rfl)
      case Seq =>
          exact False.elim (hSeq rfl)
      case not =>
          exact False.elim (hNot rfl)
  case __eo_List_cons =>
      exact False.elim (hListCons rfl)

/-- Computes SMT translation for generic double EO applications. -/
private theorem eo_to_smt_double_apply_generic
    (g y x : Term)
    (hAnd : g ≠ Term.UOp UserOp.and)
    (hImp : g ≠ Term.UOp UserOp.imp)
    (hEq : g ≠ Term.UOp UserOp.eq) :
    __eo_to_smt (Term.Apply (Term.Apply g y) x) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x) := by
  cases g <;> try rfl
  case UOp op =>
      cases op <;> try rfl
      case and =>
          exact False.elim (hAnd rfl)
      case imp =>
          exact False.elim (hImp rfl)
      case eq =>
          exact False.elim (hEq rfl)

/-- Computes SMT translation for generic single EO applications. -/
private theorem eo_to_smt_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hNot : f ≠ Term.UOp UserOp.not) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case UOp op =>
      cases op <;> try rfl
      case not =>
          exact False.elim (hNot rfl)

/- BEGIN obsolete body-substitution helpers.
Datatype declarations now use lookup and resolution; declaration-aware
constructor and selector helpers follow this block.
/-- Extends a ref-list inclusion witness across a common head element. -/
private theorem cons_subset
    {refs refs' : List native_String} {s : native_String}
    (hsub : ∀ t, t ∈ refs -> t ∈ refs') :
    ∀ t, t ∈ s :: refs -> t ∈ s :: refs' := by
  intro t ht
  simp at ht ⊢
  rcases ht with rfl | ht
  · exact Or.inl rfl
  · exact Or.inr (hsub t ht)

/- Weakening EO validity along ref-list inclusion. -/
mutual

private theorem eo_type_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {T : Term},
      TranslationProofs.eo_type_valid_rec refs T ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      TranslationProofs.eo_type_valid_rec refs' T
  | Term.UOp op, h, _ => by
      cases op with
      | Int =>
          simp [TranslationProofs.eo_type_valid_rec]
      | Real =>
          simp [TranslationProofs.eo_type_valid_rec]
      | Char =>
          simp [TranslationProofs.eo_type_valid_rec]
      | _ =>
          simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.__eo_List, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.__eo_List_nil, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.__eo_List_cons, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Bool, _, _ => by
      simp [TranslationProofs.eo_type_valid_rec]
  | Term.Boolean b, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Numeral n, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Rational q, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.String s, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Binary w n, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Type, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Stuck, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h, _ => by
      simpa [TranslationProofs.eo_type_valid_rec] using h
  | Term.Apply (Term.UOp UserOp.Seq) x, h, _ => by
      simpa [TranslationProofs.eo_type_valid_rec] using h
  | Term.Apply (Term.Apply Term.FunType T1) T2, h, _ => by
      simpa [TranslationProofs.eo_type_valid_rec] using h
  | Term.Apply f x, h, _ => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  simpa [TranslationProofs.eo_type_valid_rec] using h
              | _ =>
                  simp [TranslationProofs.eo_type_valid_rec] at h
          | Seq =>
              simpa [TranslationProofs.eo_type_valid_rec] using h
          | _ =>
              simp [TranslationProofs.eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              simpa [TranslationProofs.eo_type_valid_rec] using h
          | _ =>
              simp [TranslationProofs.eo_type_valid_rec] at h
      | _ =>
          simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.FunType, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.Var name T, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.DatatypeType s d, h, hsub => by
      rcases h with ⟨hReserved, hD⟩
      exact ⟨hReserved, eo_datatype_valid_rec_weaken hD (cons_subset hsub)⟩
  | Term.DatatypeTypeRef s, h, hsub => by
      rcases h with ⟨hReserved, hMem⟩
      exact ⟨hReserved, hsub s hMem⟩
  | Term.DtcAppType T U, h, _ => by
      simpa [TranslationProofs.eo_type_valid_rec] using h
  | Term.DtCons s d i, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.DtSel s d i j, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h
  | Term.USort i, _, _ => by
      simp [TranslationProofs.eo_type_valid_rec]
  | Term.UConst i T, h, _ => by
      simp [TranslationProofs.eo_type_valid_rec] at h

private theorem eo_datatype_cons_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {c : DatatypeCons},
      TranslationProofs.eo_datatype_cons_valid_rec refs c ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      TranslationProofs.eo_datatype_cons_valid_rec refs' c
  | DatatypeCons.unit, _, _ => by
      simp [TranslationProofs.eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h, hsub => by
      rcases h with ⟨hT, hC⟩
      exact ⟨eo_type_valid_rec_weaken hT hsub, eo_datatype_cons_valid_rec_weaken hC hsub⟩

private theorem eo_datatype_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {d : Datatype},
      TranslationProofs.eo_datatype_valid_rec refs d ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      TranslationProofs.eo_datatype_valid_rec refs' d
  | Datatype.null, _, _ => by
      simp [TranslationProofs.eo_datatype_valid_rec]
  | Datatype.sum c d, h, hsub => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_weaken hC hsub, eo_datatype_valid_rec_weaken hD hsub⟩

end

/- Lifting (re-folding a datatype occurrence to a `TypeRef`) preserves validity when the
re-folded name is in scope. The lift is shallow at the type level. -/
mutual

private theorem eo_type_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {T : Term} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : TranslationProofs.eo_type_valid_rec refs T) :
    TranslationProofs.eo_type_valid_rec refs (__eo_type_lift s0 d0 T) := by
  cases T with
  | DatatypeType s2 d2 =>
      rcases hValid with ⟨hRes, hD⟩
      simp only [__eo_type_lift]
      by_cases hteq : native_teq (Term.DatatypeType s0 d0) (Term.DatatypeType s2 d2) = true
      · rw [native_ite, if_pos hteq]
        have hEq : Term.DatatypeType s0 d0 = Term.DatatypeType s2 d2 := of_decide_eq_true hteq
        injection hEq with hs hd
        subst hs
        exact ⟨hRes, hMem⟩
      · rw [native_ite, if_neg hteq]
        exact ⟨hRes, eo_datatype_lift_preserves_valid s0 d0 (List.mem_cons_of_mem _ hMem) hD⟩
  | _ => exact hValid

private theorem eo_datatype_cons_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {c : DatatypeCons} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : TranslationProofs.eo_datatype_cons_valid_rec refs c) :
    TranslationProofs.eo_datatype_cons_valid_rec refs (__eo_dtc_lift s0 d0 c) := by
  cases c with
  | unit => exact hValid
  | cons T c =>
      rcases hValid with ⟨hT, hC⟩
      exact ⟨eo_type_lift_preserves_valid s0 d0 hMem hT,
        eo_datatype_cons_lift_preserves_valid s0 d0 hMem hC⟩

private theorem eo_datatype_lift_preserves_valid (s0 : native_String) (d0 : Datatype)
    {d : Datatype} {refs : List native_String}
    (hMem : s0 ∈ refs) (hValid : TranslationProofs.eo_datatype_valid_rec refs d) :
    TranslationProofs.eo_datatype_valid_rec refs (__eo_dt_lift s0 d0 d) := by
  cases d with
  | null => exact hValid
  | sum c d =>
      rcases hValid with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_lift_preserves_valid s0 d0 hMem hC,
        eo_datatype_lift_preserves_valid s0 d0 hMem hD⟩

end

/- Substituting a valid datatype for a valid type-reference preserves datatype validity. -/
mutual

private theorem eo_datatype_cons_valid_rec_substitute
    (s : native_String) (dsub : Datatype) (refs : List native_String)
    (hSub : TranslationProofs.eo_datatype_valid_rec (s :: refs) dsub) :
    ∀ {c : DatatypeCons},
      TranslationProofs.eo_datatype_cons_valid_rec (s :: refs) c ->
      TranslationProofs.eo_datatype_cons_valid_rec refs (__eo_dtc_substitute s dsub c)
  | DatatypeCons.unit, _ => by
      simp [TranslationProofs.eo_datatype_cons_valid_rec, __eo_dtc_substitute]
  | DatatypeCons.cons T c, h => by
      rcases h with ⟨hT, hC⟩
      have hC' := eo_datatype_cons_valid_rec_substitute s dsub refs hSub hC
      cases T with
      | DatatypeType s2 d2 =>
          rcases hT with ⟨hReserved, hT⟩
          by_cases hs : s = s2
          · subst s2
            have hD2' : TranslationProofs.eo_datatype_valid_rec (s :: refs) d2 := by
              apply eo_datatype_valid_rec_weaken hT
              intro t ht
              cases ht with
              | head =>
                  simp
              | tail _ ht =>
                  exact ht
            have hT' :
                TranslationProofs.eo_type_valid_rec refs
                  (Term.DatatypeType s d2) := by
              exact ⟨hReserved, hD2'⟩
            simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
              TranslationProofs.eo_type_valid_rec, native_ite, native_streq] using
              And.intro hT' hC'
          · have hD2 : TranslationProofs.eo_datatype_valid_rec (s2 :: s :: refs) d2 := by
              exact hT
            have hSub' : TranslationProofs.eo_datatype_valid_rec (s :: s2 :: refs) dsub := by
              apply eo_datatype_valid_rec_weaken hSub
              intro t ht
              simp at ht ⊢
              rcases ht with rfl | ht
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ht)
            have hD2swap : TranslationProofs.eo_datatype_valid_rec (s :: s2 :: refs) d2 := by
              apply eo_datatype_valid_rec_weaken hD2
              intro t ht
              simp at ht ⊢
              rcases ht with rfl | rfl | ht
              · exact Or.inr (Or.inl rfl)
              · exact Or.inl rfl
              · exact Or.inr (Or.inr ht)
            have hSubLifted : TranslationProofs.eo_datatype_valid_rec (s :: s2 :: refs)
                (__eo_dt_lift s2 d2 dsub) :=
              eo_datatype_lift_preserves_valid s2 d2 (by simp) hSub'
            have hD2' :=
              eo_datatype_valid_rec_substitute s (__eo_dt_lift s2 d2 dsub) (s2 :: refs)
                hSubLifted hD2swap
            have hT' :
                TranslationProofs.eo_type_valid_rec refs
                  (Term.DatatypeType s2 (__eo_dt_substitute s (__eo_dt_lift s2 d2 dsub) d2)) := by
              exact ⟨hReserved, hD2'⟩
            simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
              TranslationProofs.eo_type_valid_rec, hs, native_ite, native_streq] using
              And.intro hT' hC'
      | DatatypeTypeRef s2 =>
          rcases hT with ⟨hReserved, hT⟩
          by_cases hs : s2 = s
          · subst s2
            have hT' : TranslationProofs.eo_type_valid_rec refs (Term.DatatypeType s dsub) := by
              exact ⟨hReserved, hSub⟩
            simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
              TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
              And.intro hT' hC'
          · have hMem : s2 ∈ s :: refs := by
              exact hT
            have hMem' : s2 ∈ refs := by
              simpa [hs] using hMem
            have hT' : TranslationProofs.eo_type_valid_rec refs (Term.DatatypeTypeRef s2) := by
              exact ⟨hReserved, hMem'⟩
            simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
              TranslationProofs.eo_type_valid_rec, native_ite, native_teq, hs] using
              And.intro hT' hC'
      | Bool =>
          simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
            TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
            And.intro trivial hC'
      | UOp op =>
          cases op with
          | Int =>
              simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                And.intro trivial hC'
          | Real =>
              simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                And.intro trivial hC'
          | Char =>
              simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                And.intro trivial hC'
          | _ =>
              simp [TranslationProofs.eo_type_valid_rec] at hT
      | UOp1 op x =>
          cases op <;> simp [TranslationProofs.eo_type_valid_rec] at hT
      | UOp2 op x y =>
          cases op <;> simp [TranslationProofs.eo_type_valid_rec] at hT
      | UOp3 op x y z =>
          cases op <;> simp [TranslationProofs.eo_type_valid_rec] at hT
      | USort i =>
          simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
            TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
            And.intro trivial hC'
      | DtcAppType T1 T2 =>
          simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
            TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
            And.intro hT hC'
      | Apply f x =>
          cases f with
          | UOp op =>
              cases op with
              | BitVec =>
                  cases x with
                  | Numeral n =>
                      simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                        TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                        And.intro hT hC'
                  | _ =>
                      simp [TranslationProofs.eo_type_valid_rec] at hT
              | Seq =>
                  simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                    TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                    And.intro hT hC'
              | _ =>
                  simp [TranslationProofs.eo_type_valid_rec] at hT
          | Apply g y =>
              cases g with
              | FunType =>
                  simpa [__eo_dtc_substitute, TranslationProofs.eo_datatype_cons_valid_rec,
                    TranslationProofs.eo_type_valid_rec, native_ite, native_teq] using
                    And.intro hT hC'
              | _ =>
                  simp [TranslationProofs.eo_type_valid_rec] at hT
          | _ =>
              simp [TranslationProofs.eo_type_valid_rec] at hT
      | __eo_List =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | __eo_List_nil =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | __eo_List_cons =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Boolean b =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Numeral n =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Rational q =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | String str =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Binary w n =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | «Type» =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Stuck =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | FunType =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | Var name ty =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | DtCons s0 d0 i0 =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | DtSel s0 d0 i0 j0 =>
          simp [TranslationProofs.eo_type_valid_rec] at hT
      | UConst i0 ty =>
          simp [TranslationProofs.eo_type_valid_rec] at hT

private theorem eo_datatype_valid_rec_substitute
    (s : native_String) (dsub : Datatype) (refs : List native_String)
    (hSub : TranslationProofs.eo_datatype_valid_rec (s :: refs) dsub) :
    ∀ {d : Datatype},
      TranslationProofs.eo_datatype_valid_rec (s :: refs) d ->
      TranslationProofs.eo_datatype_valid_rec refs (__eo_dt_substitute s dsub d)
  | Datatype.null, _ => by
      simp [TranslationProofs.eo_datatype_valid_rec, __eo_dt_substitute]
  | Datatype.sum c d, h => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_substitute s dsub refs hSub hC,
        eo_datatype_valid_rec_substitute s dsub refs hSub hD⟩

end

/-- Computes translated EO constructor typing at index zero on valid constructor chains. -/
private theorem eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid
    {T : Term}
    (hT : TranslationProofs.eo_type_valid_rec [] T) :
    ∀ {c : DatatypeCons} {d : Datatype},
      TranslationProofs.eo_datatype_cons_valid_rec [] c ->
      TranslationProofs.eo_datatype_valid_rec [] d ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
          (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
          native_nat_zero ∧
      TranslationProofs.eo_type_valid_rec []
        (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero)
  | DatatypeCons.unit, d, _, _ => by
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum DatatypeCons.unit d) native_nat_zero = T := by
        cases T <;> simp [__eo_typeof_dt_cons_rec, TranslationProofs.eo_type_valid_rec] at hT ⊢
      refine ⟨?_, ?_⟩
      · rw [hEq]
        simp [__smtx_typeof_dt_cons_rec]
      · rw [hEq]
        exact hT
  | DatatypeCons.cons U c, d, hC, hD => by
      rcases hC with ⟨hU, hC⟩
      have hRec :=
        eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid (T := T) hT hC hD
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hU
      have hRecNN :
          __eo_to_smt_type
              (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) ≠
            SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hRec.2
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum (DatatypeCons.cons U c) d) native_nat_zero =
            Term.DtcAppType U (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) := by
        cases T <;> simp [__eo_typeof_dt_cons_rec, TranslationProofs.eo_type_valid_rec] at hT ⊢
      have hRecTyNN :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
              native_nat_zero ≠
            SmtType.None := by
        rw [← hRec.1]
        exact hRecNN
      refine ⟨?_, ?_⟩
      · rw [hEq, TranslationProofs.eo_to_smt_type_dtc_app, hRec.1]
        simp [__smtx_typeof_dt_cons_rec, __eo_to_smt_datatype_cons,
          hUNN, hRecTyNN, __smtx_typeof_guard, native_ite, native_Teq]
      · rw [hEq]
        exact ⟨hU, hRec.2⟩

/-- Computes translated EO constructor typing at valid datatype indices where the SMT type is defined. -/
private theorem eo_to_smt_type_typeof_dt_cons_rec_of_valid
    {T : Term}
    (hT : TranslationProofs.eo_type_valid_rec [] T) :
    ∀ {d : Datatype} {i : native_Nat},
      TranslationProofs.eo_datatype_valid_rec [] d ->
      __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ≠ SmtType.None ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T d i) =
        __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ∧
      TranslationProofs.eo_type_valid_rec [] (__eo_typeof_dt_cons_rec T d i)
  | Datatype.null, i, hD, hNN => by
      exfalso
      exact hNN (by simp [__smtx_typeof_dt_cons_rec])
  | Datatype.sum c d, native_nat_zero, hD, _ => by
      exact eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid (T := T) hT hD.1 hD.2
  | Datatype.sum c d, native_nat_succ i, hD, hNN => by
      have hNN' :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ≠
            SmtType.None := by
        simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using hNN
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum c d) (native_nat_succ i) =
            __eo_typeof_dt_cons_rec T d i := by
        cases T <;> cases c <;> simp [__eo_typeof_dt_cons_rec]
      have hSmtEq :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (__eo_to_smt_datatype (Datatype.sum c d)) (native_nat_succ i) =
            __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i := by
        simp [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec]
      rw [hEq, hSmtEq]
      exact eo_to_smt_type_typeof_dt_cons_rec_of_valid (T := T) hT hD.2 hNN'

/-- Computes translated EO typing for datatype constructors on valid datatypes. -/
private theorem eo_to_smt_type_typeof_dt_cons_of_valid
    (s : native_String) (d : Datatype) (i : native_Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false)
    (hValid : TranslationProofs.eo_datatype_valid_rec [s] d)
    (hNN : __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ∧
    TranslationProofs.eo_type_valid_rec [] (__eo_typeof (Term.DtCons s d i)) := by
  let D : SmtType := SmtType.Datatype s (__eo_to_smt_datatype d)
  let inner : SmtType :=
    __smtx_typeof_dt_cons_rec D
      (__smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d)) i
  have hGuardNN : __smtx_typeof_guard_wf D inner ≠ SmtType.None := by
    simpa [D, inner, __smtx_typeof.eq_def] using hNN
  have hInnerEq :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = inner := by
    have hGuard : __smtx_typeof_guard_wf D inner = inner :=
      TranslationProofs.smtx_typeof_guard_wf_of_non_none D inner hGuardNN
    simpa [D, inner, __smtx_typeof.eq_def] using hGuard
  have hInnerNN : inner ≠ SmtType.None := by
    rw [← hInnerEq]
    exact hNN
  have hTyValid : TranslationProofs.eo_type_valid_rec [] (Term.DatatypeType s d) := by
    exact ⟨hReserved, hValid⟩
  have hSubValid : TranslationProofs.eo_datatype_valid_rec [] (__eo_dt_substitute s d d) := by
    exact eo_datatype_valid_rec_substitute s d [] hValid hValid
  have hRec :=
    eo_to_smt_type_typeof_dt_cons_rec_of_valid (T := Term.DatatypeType s d) hTyValid hSubValid
      (by
        simpa [D, inner, __eo_to_smt_type, hReserved,
          TranslationProofs.eo_to_smt_datatype_substitute s d d hValid] using hInnerNN)
  have hSubEq :
      __eo_to_smt_datatype (__eo_dt_substitute s d d) =
        __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d) :=
    TranslationProofs.eo_to_smt_datatype_substitute s d d hValid
  refine ⟨?_, ?_⟩
  · have hRec' :
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = inner := by
      simpa [__eo_typeof, __eo_to_smt_type, hReserved, D, inner, hSubEq] using hRec.1
    exact hRec'.trans hInnerEq.symm
  · simpa [__eo_typeof] using hRec.2

/-- Computes translated EO typing for selector application from exact SMT datatype typing plus validity. -/
private theorem eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_valid
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hValid : TranslationProofs.eo_type_valid_rec [] (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  have hTyEq :
      __eo_to_smt_type (__eo_typeof x) =
        __eo_to_smt_type (Term.DatatypeType s d) := by
    have hTyBare :
        __eo_to_smt_type (__eo_typeof x) =
          SmtType.Datatype s (__eo_to_smt_datatype d) := by
      rw [← hRec, hx]
    rcases TranslationProofs.eo_to_smt_type_eq_datatype_iff.mp hTyBare with
      ⟨_, _, hReserved, _⟩
    rw [← hRec]
    simp [__eo_to_smt_type, hReserved, hx]
  have hExact : __eo_typeof x = Term.DatatypeType s d :=
    TranslationProofs.eo_to_smt_type_eq_of_valid hValid hTyEq
  have hDtValid : TranslationProofs.eo_datatype_valid_rec [s] d := by
    have hTyValid : TranslationProofs.eo_type_valid_rec [] (Term.DatatypeType s d) := by
      simpa [hExact] using hValid
    exact hTyValid.2
  exact TranslationProofs.eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    x s d i j hDtValid hExact

-/

/-- Outside a direct datatype reference, proof-side type validity is independent
of the surrounding declaration-name list. -/
private theorem eo_type_valid_drop_refs_of_not_ref
    {refs : List native_String} {T : Term}
    (hNotRef : ∀ s, T ≠ Term.DatatypeTypeRef s)
    (h : TranslationProofs.eo_type_valid_rec refs T) :
    TranslationProofs.eo_type_valid_rec [] T := by
  cases T with
  | UOp op =>
      cases op <;> simp [TranslationProofs.eo_type_valid_rec] at h ⊢ <;> assumption
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> cases x <;>
            simp [TranslationProofs.eo_type_valid_rec] at h ⊢ <;> assumption
      | Apply g y =>
          cases g <;> simp [TranslationProofs.eo_type_valid_rec] at h ⊢ <;> assumption
      | _ => simp [TranslationProofs.eo_type_valid_rec] at h
  | DatatypeTypeRef s => exact False.elim (hNotRef s rfl)
  | _ => simp [TranslationProofs.eo_type_valid_rec] at h ⊢ <;> assumption

mutual

private theorem eo_datatype_cons_resolve_valid
    (dd : DatatypeDecl)
    (hDecl : TranslationProofs.eo_datatype_decl_valid_rec
      (TranslationProofs.eo_datatype_decl_names dd) dd) :
    ∀ {c : DatatypeCons},
      TranslationProofs.eo_datatype_cons_valid_rec
          (TranslationProofs.eo_datatype_decl_names dd) c ->
        TranslationProofs.eo_datatype_cons_valid_rec [] (__eo_dtc_resolve c dd)
  | DatatypeCons.unit, _ => by
      simp [TranslationProofs.eo_datatype_cons_valid_rec, __eo_dtc_resolve]
  | DatatypeCons.cons T c, h => by
      rcases h with ⟨hT, hC⟩
      by_cases hRef : ∃ s, T = Term.DatatypeTypeRef s
      · rcases hRef with ⟨s, rfl⟩
        exact ⟨⟨hT.1, hT.2, hDecl⟩,
          eo_datatype_cons_resolve_valid dd hDecl hC⟩
      · have hT' : TranslationProofs.eo_type_valid_rec [] T :=
          eo_type_valid_drop_refs_of_not_ref
            (by intro s hs; exact hRef ⟨s, hs⟩) hT
        have hResolve :
            __eo_dtc_resolve (DatatypeCons.cons T c) dd =
              DatatypeCons.cons T (__eo_dtc_resolve c dd) := by
          cases T <;> simp_all [__eo_dtc_resolve]
        rw [hResolve]
        exact ⟨hT', eo_datatype_cons_resolve_valid dd hDecl hC⟩

private theorem eo_datatype_resolve_valid
    (dd : DatatypeDecl)
    (hDecl : TranslationProofs.eo_datatype_decl_valid_rec
      (TranslationProofs.eo_datatype_decl_names dd) dd) :
    ∀ {d : Datatype},
      TranslationProofs.eo_datatype_valid_rec
          (TranslationProofs.eo_datatype_decl_names dd) d ->
        TranslationProofs.eo_datatype_valid_rec [] (__eo_dt_resolve d dd)
  | Datatype.null, _ => by
      simp [TranslationProofs.eo_datatype_valid_rec, __eo_dt_resolve]
  | Datatype.sum c d, h => by
      exact ⟨eo_datatype_cons_resolve_valid dd hDecl h.1,
        eo_datatype_resolve_valid dd hDecl h.2⟩

end

/-- A valid declaration lookup has a valid body in the declaration's name scope. -/
private theorem eo_datatype_decl_lookup_valid
    (s : native_String) (base : DatatypeDecl) :
    ∀ {dd : DatatypeDecl},
      s ∈ TranslationProofs.eo_datatype_decl_names dd ->
      TranslationProofs.eo_datatype_decl_valid_rec
          (TranslationProofs.eo_datatype_decl_names base) dd ->
      TranslationProofs.eo_datatype_valid_rec
          (TranslationProofs.eo_datatype_decl_names base) (__eo_dd_lookup s dd)
  | DatatypeDecl.nil, hMem, _ => by simp [TranslationProofs.eo_datatype_decl_names] at hMem
  | DatatypeDecl.cons s' d dd, hMem, hDecl => by
      rcases hDecl with ⟨hD, hDD⟩
      cases hEq : native_streq s s'
      · have hNe : s ≠ s' := by simpa [native_streq] using hEq
        have hTailMem : s ∈ TranslationProofs.eo_datatype_decl_names dd := by
          simpa [TranslationProofs.eo_datatype_decl_names, hNe] using hMem
        have hTail := eo_datatype_decl_lookup_valid s base hTailMem hDD
        simpa [__eo_dd_lookup, hEq, native_ite] using hTail
      · simpa [__eo_dd_lookup, hEq, native_ite] using hD
termination_by dd _ _ => sizeOf dd

/-- Resolving a valid declaration lookup removes all in-scope references. -/
private theorem eo_datatype_decl_resolve_valid
    (s : native_String) (dd : DatatypeDecl)
    (hMem : s ∈ TranslationProofs.eo_datatype_decl_names dd)
    (hDecl : TranslationProofs.eo_datatype_decl_valid_rec
      (TranslationProofs.eo_datatype_decl_names dd) dd) :
    TranslationProofs.eo_datatype_valid_rec [] (__eo_dd_resolve s dd) := by
  apply eo_datatype_resolve_valid dd hDecl
  exact eo_datatype_decl_lookup_valid s dd hMem hDecl

/-- Constructor result construction at index zero commutes with translation. -/
private theorem eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid
    {T : Term}
    (hT : TranslationProofs.eo_type_valid_rec [] T) :
    ∀ {c : DatatypeCons} {d : Datatype},
      TranslationProofs.eo_datatype_cons_valid_rec [] c ->
      TranslationProofs.eo_datatype_valid_rec [] d ->
      __eo_to_smt_type
          (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) =
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
            (SmtDatatype.sum (__eo_to_smt_datatype_cons c)
              (__eo_to_smt_datatype d)) native_nat_zero ∧
        TranslationProofs.eo_type_valid_rec []
          (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero)
  | DatatypeCons.unit, d, _, _ => by
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum DatatypeCons.unit d)
            native_nat_zero = T := by
        cases T <;>
          simp [__eo_typeof_dt_cons_rec, TranslationProofs.eo_type_valid_rec] at hT ⊢
      rw [hEq]
      exact ⟨by simp [__smtx_typeof_dt_cons_rec], hT⟩
  | DatatypeCons.cons U c, d, hC, hD => by
      rcases hC with ⟨hU, hC⟩
      have hRec :=
        eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid hT hC hD
      have hUNN := TranslationProofs.eo_type_valid_rec_non_none hU
      have hRecNN := TranslationProofs.eo_type_valid_rec_non_none hRec.2
      have hRecTyNN :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (SmtDatatype.sum (__eo_to_smt_datatype_cons c)
                (__eo_to_smt_datatype d)) native_nat_zero ≠ SmtType.None := by
        rw [← hRec.1]
        exact hRecNN
      have hEq :
          __eo_typeof_dt_cons_rec T
              (Datatype.sum (DatatypeCons.cons U c) d) native_nat_zero =
            Term.DtcAppType U
              (__eo_typeof_dt_cons_rec T (Datatype.sum c d) native_nat_zero) := by
        cases T <;>
          simp [__eo_typeof_dt_cons_rec, TranslationProofs.eo_type_valid_rec] at hT ⊢
      rw [hEq]
      refine ⟨?_, ⟨hU, hRec.2⟩⟩
      rw [TranslationProofs.eo_to_smt_type_dtc_app, hRec.1]
      simp [__smtx_typeof_dt_cons_rec, __eo_to_smt_datatype_cons,
        hUNN, hRecTyNN, __smtx_typeof_guard, native_ite, native_Teq]

/-- Constructor result construction commutes at defined datatype indices. -/
private theorem eo_to_smt_type_typeof_dt_cons_rec_of_valid
    {T : Term}
    (hT : TranslationProofs.eo_type_valid_rec [] T) :
    ∀ {d : Datatype} {i : native_Nat},
      TranslationProofs.eo_datatype_valid_rec [] d ->
      __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ≠
        SmtType.None ->
      __eo_to_smt_type (__eo_typeof_dt_cons_rec T d i) =
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T) (__eo_to_smt_datatype d) i ∧
        TranslationProofs.eo_type_valid_rec [] (__eo_typeof_dt_cons_rec T d i)
  | Datatype.null, i, _, hNN => by
      exfalso
      exact hNN (by simp [__smtx_typeof_dt_cons_rec])
  | Datatype.sum c d, native_nat_zero, hD, _ => by
      exact eo_to_smt_type_typeof_dt_cons_rec_zero_of_valid hT hD.1 hD.2
  | Datatype.sum c d, native_nat_succ i, hD, hNN => by
      have hNN' :
          __smtx_typeof_dt_cons_rec (__eo_to_smt_type T)
              (__eo_to_smt_datatype d) i ≠ SmtType.None := by
        simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using hNN
      have hEq :
          __eo_typeof_dt_cons_rec T (Datatype.sum c d) (native_nat_succ i) =
            __eo_typeof_dt_cons_rec T d i := by
        cases T <;> cases c <;> simp [__eo_typeof_dt_cons_rec]
      rw [hEq]
      simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using
        eo_to_smt_type_typeof_dt_cons_rec_of_valid hT hD.2 hNN'

/-- Valid EO proof-side types are never `Stuck`. -/
private theorem eo_type_valid_not_stuck
    {refs : List native_String} {T : Term}
    (h : TranslationProofs.eo_type_valid_rec refs T) :
    T ≠ Term.Stuck := by
  intro hStuck
  subst hStuck
  simp [TranslationProofs.eo_type_valid_rec] at h

/-- Transfers generic application typing and validity from EO terms to their SMT translations. -/
private theorem eo_to_smt_typeof_matches_translation_apply_generic
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) ∧
        TranslationProofs.eo_type_valid_rec [] (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) ∧
        TranslationProofs.eo_type_valid_rec [] (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hTypeof :
      __eo_typeof (Term.Apply f x) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) ∧
      TranslationProofs.eo_type_valid_rec [] (__eo_typeof (Term.Apply f x)) := by
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f)) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, _hB⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hF with hFun | hDtc
    · rw [hFun]
      simp
    · rw [hDtc]
      simp
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hA
  have hFAll := ihF hFNN
  have hXAll := ihX hXNN
  have hXEo : __eo_to_smt_type (__eo_typeof x) = A := by
    simpa [hXAll.1] using hX
  rcases hF with hFun | hRest
  · rcases TranslationProofs.eo_typeof_eq_translated_eo_fun_of_smt_fun hFAll.1 hFun with
      ⟨T1, T2, hFunTy, hT1, hT2, _hT1NN, _hT2NN⟩
    have hFValid' := hFAll.2
    rw [hFunTy] at hFValid'
    rcases (by
      simpa [TranslationProofs.eo_type_valid_rec] using hFValid' :
        TranslationProofs.eo_type_valid_rec [] T1 ∧
          TranslationProofs.eo_type_valid_rec [] T2) with ⟨hT1Valid, hT2Valid⟩
    have hArgTy : __eo_typeof x = T1 := by
      have hArgTy' : T1 = __eo_typeof x := by
        apply TranslationProofs.eo_to_smt_type_eq_of_valid hT1Valid
        rw [hT1, ← hXEo]
      exact hArgTy'.symm
    have hT1NotStuck : T1 ≠ Term.Stuck :=
      eo_type_valid_not_stuck hT1Valid
    have hTypeApply :
        __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T1) T2) T1 = T2 := by
      rw [__eo_typeof_apply.eq_def]
      by_cases hStuck : T1 = Term.Stuck
      · exact False.elim (hT1NotStuck hStuck)
      · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
      rw [hTranslate, hGeneric, hFun, hX]
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    refine ⟨?_, ?_⟩
    · rw [hSmt, hTypeof, hFunTy, hArgTy, hTypeApply, hT2]
    · rw [hTypeof, hFunTy, hArgTy, hTypeApply]
      exact hT2Valid
  · rcases TranslationProofs.eo_typeof_eq_translated_eo_dtc_app_of_smt_dtc_app hFAll.1 hRest with
      ⟨T1, T2, hDtcTy, hT1, hT2, _hT1NN, _hT2NN⟩
    have hFValid' := hFAll.2
    rw [hDtcTy] at hFValid'
    rcases (by
      simpa [TranslationProofs.eo_type_valid_rec] using hFValid' :
        TranslationProofs.eo_type_valid_rec [] T1 ∧
          TranslationProofs.eo_type_valid_rec [] T2) with ⟨hT1Valid, hT2Valid⟩
    have hArgTy : __eo_typeof x = T1 := by
      have hArgTy' : T1 = __eo_typeof x := by
        apply TranslationProofs.eo_to_smt_type_eq_of_valid hT1Valid
        rw [hT1, ← hXEo]
      exact hArgTy'.symm
    have hT1NotStuck : T1 ≠ Term.Stuck :=
      eo_type_valid_not_stuck hT1Valid
    have hTypeApply :
        __eo_typeof_apply (Term.DtcAppType T1 T2) T1 = T2 := by
      rw [__eo_typeof_apply.eq_def]
      by_cases hStuck : T1 = Term.Stuck
      · exact False.elim (hT1NotStuck hStuck)
      · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
      rw [hTranslate, hGeneric, hRest, hX]
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    refine ⟨?_, ?_⟩
    · rw [hSmt, hTypeof, hDtcTy, hArgTy, hTypeApply, hT2]
    · rw [hTypeof, hDtcTy, hArgTy, hTypeApply]
      exact hT2Valid

/-- Shows that translated SMT terms carry the type predicted by EO typing when the translation is defined. -/
private theorem eo_to_smt_typeof_matches_translation_and_valid :
    ∀ (t : Term),
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) ∧
        TranslationProofs.eo_type_valid_rec [] (__eo_typeof t)
  | Term.UOp op, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_nil, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_cons, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Bool, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Boolean b, _ => by
      refine ⟨?_, ?_⟩
      · simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof]
      · simp [TranslationProofs.eo_type_valid_rec, __eo_typeof]
  | Term.Numeral n, _ => by
      refine ⟨?_, ?_⟩
      · simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_Numeral]
      · simp [TranslationProofs.eo_type_valid_rec, __eo_typeof, __eo_lit_type_Numeral]
  | Term.Rational r, _ => by
      refine ⟨?_, ?_⟩
      · simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_Rational]
      · simp [TranslationProofs.eo_type_valid_rec, __eo_typeof, __eo_lit_type_Rational]
  | Term.String s, hNN => by
      have hValid : native_string_valid s = true := by
        cases h : native_string_valid s
        · exfalso
          apply hNN
          simp [__eo_to_smt.eq_def, __smtx_typeof, SmtEval.native_ite, h]
        · rfl
      refine ⟨?_, ?_⟩
      · simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __eo_lit_type_String,
          __eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq,
          SmtEval.native_ite, hValid]
      · simp [TranslationProofs.eo_type_valid_rec, __eo_typeof, __eo_lit_type_String]
  | Term.Binary w n, hNN => by
      have hWidth : native_zleq 0 w = true := by
        by_cases hw : native_zleq 0 w = true
        · exact hw
        · exfalso
          apply hNN
          simp [__eo_to_smt.eq_def, __smtx_typeof, native_ite, SmtEval.native_and, hw]
      have hSmt := TranslationProofs.smtx_typeof_binary_of_non_none w n
        (by simpa [__eo_to_smt.eq_def] using hNN)
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
            SmtType.BitVec (native_int_to_nat w) := by
        simp [__eo_typeof, __eo_lit_type_Binary, __eo_mk_apply, __eo_len,
          native_ite, hWidth]
      refine ⟨?_, ?_⟩
      · simpa [__eo_to_smt.eq_def] using hSmt.trans hEo.symm
      · simpa [TranslationProofs.eo_type_valid_rec, __eo_typeof, __eo_lit_type_Binary,
          __eo_mk_apply, __eo_len, native_zleq] using hWidth
  | Term.Type, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Stuck, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.FunType, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Var name T, hNN => by
      cases name with
      | String s =>
          refine ⟨?_, ?_⟩
          · simpa [__eo_to_smt.eq_def, __eo_typeof] using
              TranslationProofs.smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hNN
          · simpa [__eo_typeof] using
              (TranslationProofs.eo_type_valid_of_guard_wf_non_none
                [] T (__eo_to_smt_type T)
                (by simpa [__eo_to_smt.eq_def, __smtx_typeof] using hNN))
      | _ =>
          exact False.elim (hNN (by simp [__eo_to_smt.eq_def, __smtx_typeof]))
  | Term.DatatypeType s d, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DatatypeTypeRef s, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DtcAppType T U, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.DtCons s d i, hNN => by
      have hReserved : __eo_to_smt_reserved_datatype_name s = false := by
        by_cases hReservedTrue : __eo_to_smt_reserved_datatype_name s = true
        · exfalso
          apply hNN
          simp [__eo_to_smt.eq_def, __smtx_typeof, hReservedTrue]
        · cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReservedTrue ⊢
      let DD := __eo_to_smt_datatype_decl d
      let D := SmtType.Datatype s DD
      let body := __smtx_dt_resolve (__smtx_dd_lookup s DD) DD
      let inner := __smtx_typeof_dt_cons_rec D body i
      have hGuardNN : __smtx_typeof_guard_wf D inner ≠ SmtType.None := by
        simpa [DD, D, body, inner, __eo_to_smt.eq_def, __smtx_typeof,
          hReserved] using hNN
      have hWf : __smtx_type_wf D = true := by
        cases h : __smtx_type_wf D
        · exfalso
          exact hGuardNN (by simp [__smtx_typeof_guard_wf, h, native_ite])
        · rfl
      have hSmt : __smtx_typeof (__eo_to_smt (Term.DtCons s d i)) = inner := by
        simp [__eo_to_smt.eq_def, __smtx_typeof, hReserved, DD, D, body, inner,
          __smtx_typeof_guard_wf, hWf, native_ite]
      have hInnerNN : inner ≠ SmtType.None := by
        rw [← hSmt]
        exact hNN
      have hTyValid :
          TranslationProofs.eo_type_valid_rec [] (Term.DatatypeType s d) :=
        TranslationProofs.eo_type_valid_of_smt_wf [] (Term.DatatypeType s d)
          (by simpa [D, DD, __eo_to_smt_type, hReserved] using hWf)
      have hResolvedValid :
          TranslationProofs.eo_datatype_valid_rec [] (__eo_dd_resolve s d) :=
        eo_datatype_decl_resolve_valid s d hTyValid.2.1 hTyValid.2.2
      have hRec :=
        eo_to_smt_type_typeof_dt_cons_rec_of_valid
          (T := Term.DatatypeType s d) hTyValid
          (d := __eo_dd_resolve s d) (i := i) hResolvedValid
          (by
            simpa [inner, D, DD, body, __eo_to_smt_type, hReserved,
              TranslationProofs.eo_to_smt_datatype_decl_resolve] using hInnerNN)
      refine ⟨?_, hRec.2⟩
      rw [hSmt]
      simpa [__eo_typeof, inner, D, DD, body, __eo_to_smt_type, hReserved,
        TranslationProofs.eo_to_smt_datatype_decl_resolve] using hRec.1.symm
  | Term.DtSel s d i j, hNN => by
      have hNone : __smtx_typeof (__eo_to_smt (Term.DtSel s d i j)) = SmtType.None := by
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
        · simp [__eo_to_smt.eq_def, __smtx_typeof, hReserved]
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt.eq_def, hReservedFalse,
            TranslationProofs.smtx_typeof_dt_sel_head_none]
      exact (hNN hNone).elim
  | Term.USort i, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.UConst i T, hNN => by
      refine ⟨?_, ?_⟩
      · simpa [__eo_to_smt.eq_def, __eo_typeof] using
          TranslationProofs.smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hNN
      · simpa [__eo_typeof] using
          (TranslationProofs.eo_type_valid_of_guard_wf_non_none
            [] T (__eo_to_smt_type T)
            (by simpa [__eo_to_smt.eq_def, __smtx_typeof] using hNN))
  | Term.Apply f x, hNN => by
      by_cases hApply : ∃ g y, f = Term.Apply g y
      · rcases hApply with ⟨g, y, rfl⟩
        by_cases hFun : g = Term.FunType
        · subst hFun
          have hTranslate :
              __eo_to_smt (Term.Apply (Term.Apply Term.FunType y) x) =
                SmtTerm.Apply (__eo_to_smt (Term.Apply Term.FunType y)) (__eo_to_smt x) := by
            rfl
          have hHeadTranslate :
              __eo_to_smt (Term.Apply Term.FunType y) =
                SmtTerm.Apply (__eo_to_smt Term.FunType) (__eo_to_smt y) := by
            exact eo_to_smt_single_apply_generic Term.FunType y
              (by intro g z h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt Term.FunType = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        ·
            by_cases hAnd : g = Term.UOp UserOp.and
            · subst hAnd
              have hTranslate :
                  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) =
                    SmtTerm.and (__eo_to_smt y) (__eo_to_smt x) := by
                rw [__eo_to_smt.eq_def]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)) := by
                unfold term_has_non_none_type
                simpa [hTranslate] using hNN
              have hArgs := bool_binop_args_bool_of_non_none
                (op := SmtTerm.and) (__smtx_typeof.eq_7 (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
              have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                rw [hArgs.1]
                simp
              have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                rw [hArgs.2]
                simp
              have hIy := eo_to_smt_typeof_matches_translation_and_valid y h1NN
              have hIx := eo_to_smt_typeof_matches_translation_and_valid x h2NN
              have hTyY : __eo_typeof y = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIy.1 hArgs.1
              have hTyX : __eo_typeof x = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIx.1 hArgs.2
              have hTy :
                  __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) = Term.Bool := by
                simp [__eo_typeof, __eo_typeof_and, hTyY, hTyX]
              refine ⟨?_, ?_⟩
              · rw [hTy]
                exact TranslationProofs.smtx_typeof_translation_and_of_non_none y x hNN
              · rw [hTy]
                simp [TranslationProofs.eo_type_valid_rec]
            · by_cases hImp : g = Term.UOp UserOp.imp
              · subst hImp
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) y) x) =
                      SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hApplyNN :
                    term_has_non_none_type
                      (SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  simpa [hTranslate] using hNN
                have hArgs := bool_binop_args_bool_of_non_none
                  (op := SmtTerm.imp) (__smtx_typeof.eq_9 (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
                have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                  rw [hArgs.1]
                  simp
                have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgs.2]
                  simp
                have hIy := eo_to_smt_typeof_matches_translation_and_valid y h1NN
                have hIx := eo_to_smt_typeof_matches_translation_and_valid x h2NN
                have hTyY : __eo_typeof y = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIy.1 hArgs.1
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx.1 hArgs.2
                have hTy :
                    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) y) x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_and, hTyY, hTyX]
                refine ⟨?_, ?_⟩
                · rw [hTy]
                  exact TranslationProofs.smtx_typeof_translation_imp_of_non_none y x hNN
                · rw [hTy]
                  simp [TranslationProofs.eo_type_valid_rec]
              · by_cases hEq : g = Term.UOp UserOp.eq
                · subst hEq
                  have hTranslate :
                      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) =
                        SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x) := by
                    rw [__eo_to_smt.eq_def]
                  have hApplyNN :
                      term_has_non_none_type
                        (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x)) := by
                    unfold term_has_non_none_type
                    simpa [hTranslate] using hNN
                  have hArgs :=
                      smtx_typeof_eq_operands_of_non_none
                        (t1 := __eo_to_smt y) (t2 := __eo_to_smt x) hApplyNN
                  have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := hArgs.2
                  have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                    rw [← hArgs.1]
                    exact hArgs.2
                  have hIy := eo_to_smt_typeof_matches_translation_and_valid y h1NN
                  have hIx := eo_to_smt_typeof_matches_translation_and_valid x h2NN
                  have hTyEqTrans :
                      __eo_to_smt_type (__eo_typeof y) =
                        __eo_to_smt_type (__eo_typeof x) := by
                    rw [← hIy.1, hArgs.1, hIx.1]
                  have hTyEq : __eo_typeof y = __eo_typeof x := by
                    exact TranslationProofs.eo_to_smt_type_eq_of_valid hIy.2 hTyEqTrans
                  have hTyYNotStuck : __eo_typeof y ≠ Term.Stuck :=
                    eo_type_valid_not_stuck hIy.2
                  have hTyXNotStuck : __eo_typeof x ≠ Term.Stuck := by
                    intro hStuck
                    apply hTyYNotStuck
                    rw [hTyEq, hStuck]
                  have hEqSelf :
                      __eo_typeof_eq (__eo_typeof x) (__eo_typeof x) = Term.Bool :=
                    eo_typeof_eq_self_of_not_stuck (__eo_typeof x) hTyXNotStuck
                  have hTy :
                      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) = Term.Bool := by
                    simp [__eo_typeof, hTyEq, hEqSelf]
                  refine ⟨?_, ?_⟩
                  · rw [hTy]
                    exact TranslationProofs.smtx_typeof_translation_eq_of_non_none y x hNN
                  · rw [hTy]
                    simp [TranslationProofs.eo_type_valid_rec]
                ·
                  exact eo_to_smt_typeof_matches_translation_apply_generic
                    (Term.Apply g y) x
                    (eo_to_smt_typeof_matches_translation_and_valid (Term.Apply g y))
                    (eo_to_smt_typeof_matches_translation_and_valid x)
                    (TranslationProofs.eo_to_smt_apply_generic_type (Term.Apply g y) x
                      (by intro s d i j h; cases h))
                    (eo_to_smt_double_apply_generic g y x hAnd hImp hEq)
                    (eo_typeof_double_apply_generic g y x hFun hAnd hImp hEq)
                    hNN
      · by_cases hBitVec : f = Term.UOp UserOp.BitVec
        · subst hBitVec
          have hTranslate :
              __eo_to_smt (Term.Apply (Term.UOp UserOp.BitVec) x) =
                SmtTerm.Apply (__eo_to_smt (Term.UOp UserOp.BitVec)) (__eo_to_smt x) := by
            exact eo_to_smt_single_apply_generic (Term.UOp UserOp.BitVec) x
              (by intro g y h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt (Term.UOp UserOp.BitVec) = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        · by_cases hSeq : f = Term.UOp UserOp.Seq
          · subst hSeq
            have hTranslate :
                __eo_to_smt (Term.Apply (Term.UOp UserOp.Seq) x) =
                  SmtTerm.Apply (__eo_to_smt (Term.UOp UserOp.Seq)) (__eo_to_smt x) := by
              exact eo_to_smt_single_apply_generic (Term.UOp UserOp.Seq) x
                (by intro g y h; cases h)
                (by intro h; cases h)
            have hHeadNone : __eo_to_smt (Term.UOp UserOp.Seq) = SmtTerm.None := by
              rw [__eo_to_smt.eq_def]
            have hNN' := hNN
            rw [hTranslate, hHeadNone] at hNN'
            simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
          · by_cases hListCons : f = Term.__eo_List_cons
            · subst hListCons
              have hTranslate :
                  __eo_to_smt (Term.Apply Term.__eo_List_cons x) =
                    SmtTerm.Apply (__eo_to_smt Term.__eo_List_cons) (__eo_to_smt x) := by
                exact eo_to_smt_single_apply_generic Term.__eo_List_cons x
                  (by intro g y h; cases h)
                  (by intro h; cases h)
              have hHeadNone : __eo_to_smt Term.__eo_List_cons = SmtTerm.None := by
                rw [__eo_to_smt.eq_def]
              have hNN' := hNN
              rw [hTranslate, hHeadNone] at hNN'
              simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
            · by_cases hNot : f = Term.UOp UserOp.not
              · subst hNot
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) x) =
                      SmtTerm.not (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hArgSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
                  have hNN' := hNN
                  rw [hTranslate] at hNN'
                  cases h : __smtx_typeof (__eo_to_smt x) <;>
                    simp [__smtx_typeof, native_ite, native_Teq, h] at hNN'
                  simp
                have hArgNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgSmtTy]
                  simp
                have hIx := eo_to_smt_typeof_matches_translation_and_valid x hArgNN
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx.1 hArgSmtTy
                have hTy :
                    __eo_typeof (Term.Apply (Term.UOp UserOp.not) x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_not, hTyX]
                refine ⟨?_, ?_⟩
                · rw [hTy]
                  exact TranslationProofs.smtx_typeof_translation_not_of_non_none x hNN
                · rw [hTy]
                  simp [TranslationProofs.eo_type_valid_rec]
              · by_cases hDtSel : ∃ s d i j, f = Term.DtSel s d i j
                · rcases hDtSel with ⟨s, d, i, j, rfl⟩
                  let R := __smtx_ret_typeof_sel s (__eo_to_smt_datatype_decl d) i j
                  have hReserved : __eo_to_smt_reserved_datatype_name s = false := by
                    by_cases hReservedTrue : __eo_to_smt_reserved_datatype_name s = true
                    · exfalso
                      apply hNN
                      change
                        __smtx_typeof
                            (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x)) =
                          SmtType.None
                      rw [TranslationProofs.eo_to_smt_term_dt_sel]
                      simp [__smtx_typeof, __smtx_typeof_apply, hReservedTrue]
                    · cases hName : __eo_to_smt_reserved_datatype_name s <;>
                        simp [hName] at hReservedTrue ⊢
                  have hTranslate :
                      __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
                        SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) (__eo_to_smt x) := by
                    calc
                      __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
                          SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
                        exact eo_to_smt_single_apply_generic (Term.DtSel s d i j) x
                          (by intro g y h; cases h)
                          (by intro h; cases h)
                      _ = SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) (__eo_to_smt x) := by
                        rw [TranslationProofs.eo_to_smt_term_dt_sel]
                        simp [hReserved]
                  have hApplyNN :
                      term_has_non_none_type
                        (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) (__eo_to_smt x)) := by
                    unfold term_has_non_none_type
                    simpa [hTranslate] using hNN
                  have hArgTy :
                      __smtx_typeof (__eo_to_smt x) =
                        SmtType.Datatype s (__eo_to_smt_datatype_decl d) :=
                    dt_sel_arg_datatype_of_non_none hApplyNN
                  have hArgNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                    rw [hArgTy]
                    simp
                  have hIx := eo_to_smt_typeof_matches_translation_and_valid x hArgNN
                  have hArgExactTy :
                      __eo_to_smt_type (__eo_typeof x) =
                        __eo_to_smt_type (Term.DatatypeType s d) := by
                    rw [← hIx.1]
                    simpa [__eo_to_smt_type, hReserved] using hArgTy
                  have hArgExact : __eo_typeof x = Term.DatatypeType s d :=
                    TranslationProofs.eo_to_smt_type_eq_of_valid hIx.2 hArgExactTy
                  have hSmtTy :
                      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) = R := by
                    simpa [hTranslate, R] using dt_sel_term_typeof_of_non_none hApplyNN
                  have hEoTy :
                      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) = R := by
                    simpa [R] using
                      TranslationProofs.eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
                        x s d i j hArgExact
                  refine ⟨hSmtTy.trans hEoTy.symm, ?_⟩
                  have hGuardNN :
                      __smtx_typeof_guard_wf R
                        (__smtx_typeof_apply
                          (SmtType.FunType
                            (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) R)
                          (__smtx_typeof (__eo_to_smt x))) ≠
                        SmtType.None := by
                    simpa [term_has_non_none_type, __smtx_typeof, R] using hApplyNN
                  have hRetWf : __smtx_type_wf R = true := by
                    unfold __smtx_typeof_guard_wf at hGuardNN
                    by_cases hWf : __smtx_type_wf R = true
                    · exact hWf
                    · exfalso
                      simp [native_ite, hWf] at hGuardNN
                  apply TranslationProofs.eo_type_valid_of_smt_wf []
                  rw [hEoTy]
                  exact hRetWf
                ·
                  have hNoSel : ∀ s d i j, f ≠ Term.DtSel s d i j := by
                    intro s d i j hSel
                    exact hDtSel ⟨s, d, i, j, hSel⟩
                  have hApplyAll : ∀ g y, f ≠ Term.Apply g y := by
                    intro g y hEq
                    exact hApply ⟨g, y, hEq⟩
                  exact eo_to_smt_typeof_matches_translation_apply_generic
                    f x
                    (eo_to_smt_typeof_matches_translation_and_valid f)
                    (eo_to_smt_typeof_matches_translation_and_valid x)
                    (TranslationProofs.eo_to_smt_apply_generic_type f x hNoSel)
                    (eo_to_smt_single_apply_generic f x hApplyAll hNot)
                    (eo_typeof_single_apply_generic f x hApplyAll hBitVec hSeq hListCons hNot)
                    hNN
termination_by t _ => sizeOf t
decreasing_by
  all_goals
    subst_vars
    simp_wf
  all_goals
    omega

/-- Shows that translated SMT terms carry the type predicted by EO typing when the translation is defined. -/
private theorem eo_to_smt_typeof_matches_translation
    (t : Term)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) :=
  (eo_to_smt_typeof_matches_translation_and_valid t hNN).1

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNN hTy
  subst s T
  exact eo_to_smt_typeof_matches_translation t hNN

end RuleProofs
