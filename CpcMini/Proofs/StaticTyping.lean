module

public import CpcMini.SmtModel
import all CpcMini.SmtModel

public section

open SmtEval

set_option linter.unusedSimpArgs false

namespace Smtm

/-!
# Inhabitation and the default generator

The checker decides inhabitation structurally, with `native_inhabited_type`,
and never constructs a value. This file connects that check to the semantic
default generator `__smtx_type_default`:

* `native_inhabited_type_iff`: the check succeeds exactly when the generator
  constructs a value. This holds for every type, malformed declarations
  included.
* `type_default_typed`: on a recursively well-formed type, that value has the
  requested type.

Proofs about the generator use `type_default_induct` below rather than the
`.induct` principle Lean derives for it, whose motives and cases are ordered by
where the generated definitions happen to stand.
-/

section TypeDefaultInduct

-- Each case below uses only some of the hypotheses; all are shared.
set_option linter.unusedSectionVars false

variable
  (typeM : SmtType → Prop)
  (declM : native_String → SmtDatatypeDecl → SmtDatatypeDecl → Prop)
  (dtM : native_String → SmtDatatypeDecl → native_Nat → SmtDatatype →
    SmtDatatypeDecl → Prop)
  (consM : SmtValue → SmtDatatypeDecl → SmtDatatypeCons → SmtDatatypeDecl → Prop)
  (fieldM : SmtDatatypeDecl → SmtType → SmtDatatypeDecl → Prop)
  (hBool : typeM SmtType.Bool)
  (hInt : typeM SmtType.Int)
  (hReal : typeM SmtType.Real)
  (hRegLan : typeM SmtType.RegLan)
  (hBitVec : ∀ n, typeM (SmtType.BitVec n))
  (hMap : ∀ T U, typeM U → typeM (SmtType.Map T U))
  (hSet : ∀ T, typeM (SmtType.Set T))
  (hSeq : ∀ T, typeM (SmtType.Seq T))
  (hChar : typeM SmtType.Char)
  (hDatatype : ∀ s dd, declM s dd dd → typeM (SmtType.Datatype s dd))
  (hUSort : ∀ n, typeM (SmtType.USort n))
  (hFun : ∀ T U, typeM (SmtType.FunType T U))
  (hOther : ∀ T : SmtType,
    (T = SmtType.Bool → False) → (T = SmtType.Int → False) →
    (T = SmtType.Real → False) → (T = SmtType.RegLan → False) →
    (∀ n, T = SmtType.BitVec n → False) → (∀ A B, T = SmtType.Map A B → False) →
    (∀ A, T = SmtType.Set A → False) → (∀ A, T = SmtType.Seq A → False) →
    (T = SmtType.Char → False) → (∀ s dd, T = SmtType.Datatype s dd → False) →
    (∀ n, T = SmtType.USort n → False) → (∀ A B, T = SmtType.FunType A B → False) →
    typeM T)
  (hDeclCons : ∀ s dd sF dF ddF, dtM s dd Nat.zero dF ddF → declM s dd ddF →
    declM s dd (SmtDatatypeDecl.cons sF dF ddF))
  (hDeclNil : ∀ s dd ddF,
    (∀ sF dF ddF', ddF = SmtDatatypeDecl.cons sF dF ddF' → False) → declM s dd ddF)
  (hDtSum : ∀ s dd n cF dF ddF, consM (SmtValue.DtCons s dd n) dd cF ddF →
    dtM s dd (Nat.succ n) dF ddF → dtM s dd n (SmtDatatype.sum cF dF) ddF)
  (hDtNull : ∀ s dd n dF ddF,
    (∀ cF dF', dF = SmtDatatype.sum cF dF' → False) → dtM s dd n dF ddF)
  (hConsUnit : ∀ v dd ddF, consM v dd SmtDatatypeCons.unit ddF)
  (hConsCons : ∀ v dd T c ddF,
    have _v0 := __smtx_field_type_default dd T ddF
    fieldM dd T ddF → consM (SmtValue.Apply v _v0) dd c ddF →
      consM v dd (SmtDatatypeCons.cons T c) ddF)
  (hFieldRef : ∀ dd s ddF, declM s dd ddF → fieldM dd (SmtType.TypeRef s) ddF)
  (hFieldOther : ∀ dd T ddF, (∀ s, T = SmtType.TypeRef s → False) → typeM T →
    fieldM dd T ddF)

include hBool hInt hReal hRegLan hBitVec hMap hSet hSeq hChar hDatatype hUSort
  hFun hOther hDeclCons hDeclNil hDtSum hDtNull hConsUnit hConsCons hFieldRef
  hFieldOther

mutual

private theorem typeDefaultInduct_type : ∀ T, typeM T
  | SmtType.Bool => hBool
  | SmtType.Int => hInt
  | SmtType.Real => hReal
  | SmtType.RegLan => hRegLan
  | SmtType.BitVec n => hBitVec n
  | SmtType.Map T U => hMap T U (typeDefaultInduct_type U)
  | SmtType.Set T => hSet T
  | SmtType.Seq T => hSeq T
  | SmtType.Char => hChar
  | SmtType.Datatype s dd => hDatatype s dd (typeDefaultInduct_decl s dd dd)
  | SmtType.USort n => hUSort n
  | SmtType.FunType T U => hFun T U
  | SmtType.None => hOther _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | SmtType.TypeRef s => hOther _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  | SmtType.DtcAppType A B => hOther _ (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp)
termination_by T => 2 * sizeOf T

private theorem typeDefaultInduct_decl (s : native_String) (dd : SmtDatatypeDecl) :
    ∀ ddF, declM s dd ddF
  | SmtDatatypeDecl.cons sF dF ddF => hDeclCons s dd sF dF ddF
      (typeDefaultInduct_dt s dd Nat.zero dF ddF) (typeDefaultInduct_decl s dd ddF)
  | SmtDatatypeDecl.nil => hDeclNil s dd _ (by simp)
termination_by ddF => 2 * sizeOf ddF

private theorem typeDefaultInduct_dt (s : native_String) (dd : SmtDatatypeDecl)
    (n : native_Nat) : ∀ dF ddF, dtM s dd n dF ddF
  | SmtDatatype.sum cF dF, ddF => hDtSum s dd n cF dF ddF
      (typeDefaultInduct_cons (SmtValue.DtCons s dd n) dd cF ddF)
      (typeDefaultInduct_dt s dd (Nat.succ n) dF ddF)
  | SmtDatatype.null, ddF => hDtNull s dd n _ ddF (by simp)
termination_by dF ddF => 2 * (sizeOf dF + sizeOf ddF) + 1

private theorem typeDefaultInduct_cons (v : SmtValue) (dd : SmtDatatypeDecl) :
    ∀ c ddF, consM v dd c ddF
  | SmtDatatypeCons.unit, ddF => hConsUnit v dd ddF
  | SmtDatatypeCons.cons T c, ddF => hConsCons v dd T c ddF
      (typeDefaultInduct_field dd T ddF)
      (typeDefaultInduct_cons (SmtValue.Apply v (__smtx_field_type_default dd T ddF))
        dd c ddF)
termination_by c ddF => 2 * (sizeOf c + sizeOf ddF) + 2

private theorem typeDefaultInduct_field (dd : SmtDatatypeDecl) (T : SmtType)
    (ddF : SmtDatatypeDecl) : fieldM dd T ddF := by
  by_cases h : ∃ s, T = SmtType.TypeRef s
  · obtain ⟨s, rfl⟩ := h
    exact hFieldRef dd s ddF (typeDefaultInduct_decl s dd ddF)
  · exact hFieldOther dd T ddF (fun s hs => h ⟨s, hs⟩) (typeDefaultInduct_type T)
termination_by 2 * (sizeOf T + sizeOf ddF) + 3

end

/-- Induction following the recursion of the default generator, with one motive
per generator function: types, declaration search, datatype search,
constructor application and constructor fields. -/
theorem type_default_induct : ∀ T, typeM T :=
  typeDefaultInduct_type typeM declM dtM consM fieldM hBool hInt hReal hRegLan
    hBitVec hMap hSet hSeq hChar hDatatype hUSort hFun hOther hDeclCons hDeclNil
    hDtSum hDtNull hConsUnit hConsCons hFieldRef hFieldOther

end TypeDefaultInduct

/-- The type a constructor field has once a reference to a datatype of the
declaration `dd` is resolved, as `__smtx_dtc_resolve` resolves it. -/
private def fieldType (dd : SmtDatatypeDecl) : SmtType -> SmtType
  | SmtType.TypeRef s => SmtType.Datatype s dd
  | T => T

/-- Inhabitation of one constructor field, as `__smtx_dt_cons_inhabited` checks it. -/
private def fieldInhabited (ddF : SmtDatatypeDecl) : SmtType -> native_Bool
  | SmtType.TypeRef s => __smtx_decl_inhabited s ddF
  | T => native_inhabited_type T

private theorem dt_cons_inhabited_cons (T : SmtType) (c : SmtDatatypeCons)
    (ddF : SmtDatatypeDecl) :
    __smtx_dt_cons_inhabited (SmtDatatypeCons.cons T c) ddF =
      native_and (fieldInhabited ddF T) (__smtx_dt_cons_inhabited c ddF) := by
  cases T <;> simp [__smtx_dt_cons_inhabited, fieldInhabited]

private theorem dtc_resolve_cons (T : SmtType) (c : SmtDatatypeCons)
    (dd : SmtDatatypeDecl) :
    __smtx_dtc_resolve (SmtDatatypeCons.cons T c) dd =
      SmtDatatypeCons.cons (fieldType dd T) (__smtx_dtc_resolve c dd) := by
  cases T <;> simp [__smtx_dtc_resolve, fieldType]

theorem native_inhabited_type_ne_none {T : SmtType}
    (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  rintro rfl
  simp [native_inhabited_type] at h

/-- The structural check succeeds exactly when the generator constructs a value. -/
theorem native_inhabited_type_iff : ∀ T : SmtType,
    native_inhabited_type T = true ↔ __smtx_type_default T ≠ SmtValue.NotValue := by
  refine type_default_induct
    (typeM := fun T =>
      native_inhabited_type T = true ↔ __smtx_type_default T ≠ SmtValue.NotValue)
    (declM := fun s dd ddF =>
      __smtx_decl_inhabited s ddF = true ↔
        __smtx_datatype_decl_default s dd ddF ≠ SmtValue.NotValue)
    (dtM := fun s dd n dF ddF =>
      __smtx_dt_inhabited dF ddF = true ↔
        __smtx_datatype_default s dd n dF ddF ≠ SmtValue.NotValue)
    (consM := fun v dd c ddF =>
      v ≠ SmtValue.NotValue →
        (__smtx_dt_cons_inhabited c ddF = true ↔
          __smtx_datatype_cons_default v dd c ddF ≠ SmtValue.NotValue))
    (fieldM := fun dd T ddF =>
      fieldInhabited ddF T = true ↔
        __smtx_field_type_default dd T ddF ≠ SmtValue.NotValue)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  any_goals simp [native_inhabited_type, __smtx_type_default]; done
  case refine_6 T U ih =>
    by_cases h : __smtx_type_default U = SmtValue.NotValue <;>
      simp_all [native_inhabited_type, __smtx_type_default, native_ite, native_veq]
  case refine_10 s dd ih =>
    simpa [native_inhabited_type, __smtx_type_default] using ih
  case refine_13 T _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases T <;> simp_all [native_inhabited_type, __smtx_type_default]
  case refine_14 s dd sF dF ddF ihDt ihDecl =>
    by_cases h : native_streq s sF = true <;>
      simp_all [__smtx_decl_inhabited, __smtx_datatype_decl_default, native_ite]
  case refine_15 s dd ddF hnone =>
    cases ddF with
    | nil => simp [__smtx_decl_inhabited, __smtx_datatype_decl_default]
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  case refine_16 s dd n cF dF ddF ihCons ihTail =>
    have hCons := ihCons (by simp)
    by_cases h : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF =
        SmtValue.NotValue <;>
      simp_all [__smtx_dt_inhabited, __smtx_datatype_default, native_ite,
        native_not, native_veq, native_or]
  case refine_17 s dd n dF ddF hnone =>
    cases dF with
    | null => simp [__smtx_dt_inhabited, __smtx_datatype_default]
    | sum c tail => exact (hnone c tail rfl).elim
  case refine_18 v dd ddF hv =>
    simp [__smtx_dt_cons_inhabited, __smtx_datatype_cons_default, hv]
  case refine_19 v dd T c ddF f ihField ihTail hv =>
    have hTail := ihTail (by simp)
    dsimp only [f] at hTail
    rw [dt_cons_inhabited_cons, __smtx_datatype_cons_default]
    by_cases h : __smtx_field_type_default dd T ddF = SmtValue.NotValue <;>
      simp_all [native_ite, native_veq, native_and]
  case refine_20 dd s ddF ih =>
    simpa [fieldInhabited, __smtx_field_type_default] using ih
  case refine_21 dd T ddF hnotref ih =>
    cases T <;> simp_all [fieldInhabited, __smtx_field_type_default]

/-- Every datatype named in `ddF` is looked up in `dd` as it is in `ddF`. This
holds for `ddF = dd`, and for each suffix of a declaration with distinct names. -/
private def LookupAgrees (dd ddF : SmtDatatypeDecl) : Prop :=
  ∀ s, __smtx_dd_has_dt s ddF = true → __smtx_dd_lookup s dd = __smtx_dd_lookup s ddF

private theorem lookupAgrees_tail {dd : SmtDatatypeDecl} {sF : native_String}
    {dF : SmtDatatype} {ddF : SmtDatatypeDecl}
    (h : LookupAgrees dd (SmtDatatypeDecl.cons sF dF ddF))
    (hFresh : __smtx_dd_has_dt sF ddF = false) :
    LookupAgrees dd ddF := by
  intro s hs
  have hne : native_streq s sF = false := by
    cases hEq : native_streq s sF
    · rfl
    · simp [native_streq] at hEq
      subst hEq
      simp [hFresh] at hs
  have := h s (by simp [__smtx_dd_has_dt, native_or, hs])
  simpa [__smtx_dd_lookup, native_ite, hne] using this

/-- On a recursively well-formed type, the generated default has the requested type. -/
theorem type_default_typed : ∀ T : SmtType,
    native_inhabited_type T = true →
    __smtx_type_wf_rec T = true →
    __smtx_typeof_value (__smtx_type_default T) = T := by
  refine type_default_induct
    (typeM := fun T =>
      native_inhabited_type T = true →
      __smtx_type_wf_rec T = true →
      __smtx_typeof_value (__smtx_type_default T) = T)
    (declM := fun s dd ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      __smtx_datatype_decl_default s dd ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_decl_default s dd ddF) =
        SmtType.Datatype s dd)
    (dtM := fun s dd n dF ddF =>
      __smtx_dt_wf_rec dd dF = true →
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      (∀ m, __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
          (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) (n + m) =
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
          (__smtx_dt_resolve dF dd) m) →
      __smtx_datatype_default s dd n dF ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_default s dd n dF ddF) =
        SmtType.Datatype s dd)
    (consM := fun v dd c ddF =>
      __smtx_dt_cons_wf_rec dd c = true →
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      ∀ R d, __smtx_typeof_value v =
          __smtx_typeof_dt_cons_value_rec R
            (SmtDatatype.sum (__smtx_dtc_resolve c dd) d) 0 →
      __smtx_datatype_cons_default v dd c ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_cons_default v dd c ddF) = R)
    (fieldM := fun dd T ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      ((∃ s, T = SmtType.TypeRef s) ∨
        (native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true)) →
      __smtx_field_type_default dd T ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_field_type_default dd T ddF) = fieldType dd T)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  any_goals
    simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
      __smtx_typeof_seq_value, __smtx_map_to_set_type, native_ite, native_and,
      native_nat_to_int, native_zleq, native_zeq, native_mod_total,
      native_int_to_nat, native_char_valid]; done
  case refine_6 T U ih hInh hRec =>
    have hU : native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true := by
      simp_all [__smtx_type_wf_rec, native_and, native_inhabited_type]
    have hne := (native_inhabited_type_iff U).1 hU.1
    simp [__smtx_type_default, native_ite, native_veq, hne, __smtx_typeof_value,
      __smtx_typeof_map_value, ih hU.1 hU.2]
  case refine_10 s dd ih hInh hRec =>
    have hDecl : __smtx_decl_wf_rec dd dd = true := by
      simp_all [__smtx_type_wf_rec, native_and]
    have hne := (native_inhabited_type_iff (SmtType.Datatype s dd)).1 hInh
    simp only [__smtx_type_default] at hne ⊢
    exact ih hDecl (fun _ _ => rfl) hne
  case refine_13 T _ _ _ _ _ _ _ _ _ _ _ _ hInh _ =>
    cases T <;> simp_all [native_inhabited_type]
  case refine_14 s dd sF dF ddF ihDt ihDecl hWf hAgree hne =>
    have hParts :
        __smtx_dt_wf_rec dd dF = true ∧
        native_inhabited_type (SmtType.Datatype sF dd) = true ∧
        __smtx_decl_wf_rec dd ddF = true ∧
        __smtx_dd_has_dt sF ddF = false := by
      simpa [__smtx_decl_wf_rec, native_and, native_not] using hWf
    have hTail := lookupAgrees_tail hAgree hParts.2.2.2
    by_cases hs : native_streq s sF = true
    · have hsF : s = sF := by simpa [native_streq] using hs
      subst hsF
      have hLookup : __smtx_dd_lookup s dd = dF := by
        rw [hAgree s (by simp [__smtx_dd_has_dt, native_or, native_streq])]
        simp [__smtx_dd_lookup, native_ite, native_streq]
      simp only [__smtx_datatype_decl_default, native_ite, hs, ite_true] at hne ⊢
      exact ihDt hParts.1 hParts.2.2.1 hTail (by simp [hLookup]) hne
    · simp only [__smtx_datatype_decl_default, native_ite, hs] at hne ⊢
      simp only [Bool.false_eq_true, ite_false] at hne ⊢
      exact ihDecl hParts.2.2.1 hTail hne
  case refine_15 s dd ddF hnone _ _ hne =>
    cases ddF with
    | nil => simp [__smtx_datatype_decl_default] at hne
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  case refine_16 s dd n cF dF ddF ihCons ihTail hDt hDecl hAgree hIdx hne =>
    have hParts :
        __smtx_dt_cons_wf_rec dd cF = true ∧ __smtx_dt_wf_rec dd dF = true := by
      simpa [__smtx_dt_wf_rec, native_and] using hDt
    rw [__smtx_datatype_default] at hne ⊢
    by_cases hv : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF =
        SmtValue.NotValue
    · simp only [hv, native_ite, native_not, native_veq, decide_true,
        Bool.not_true, Bool.false_eq_true, ite_false] at hne ⊢
      refine ihTail hParts.2 hDecl hAgree (fun m => ?_) hne
      have := hIdx (m + 1)
      rw [show n + (m + 1) = Nat.succ n + m from (Nat.succ_add n m).symm] at this
      simpa [__smtx_dt_resolve, __smtx_typeof_dt_cons_value_rec] using this
    · simp only [native_ite, native_not, native_veq, hv, decide_false,
        Bool.not_false, ite_true]
      refine ihCons hParts.1 hDecl hAgree _ (__smtx_dt_resolve dF dd) ?_ hv
      have := hIdx 0
      simpa [__smtx_typeof_value, __smtx_dt_resolve] using this
  case refine_17 s dd n dF ddF hnone _ _ _ _ hne =>
    cases dF with
    | null => simp [__smtx_datatype_default] at hne
    | sum c tail => exact (hnone c tail rfl).elim
  case refine_18 v dd ddF _ _ _ R d hv _ =>
    simpa [__smtx_datatype_cons_default, __smtx_dtc_resolve,
      __smtx_typeof_dt_cons_value_rec] using hv
  case refine_19 v dd T c ddF f ihField ihTail hCons hDecl hAgree R d hv hne =>
    dsimp only [f] at ihTail
    have hField :
        ((∃ s, T = SmtType.TypeRef s) ∨
          (native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true)) ∧
        __smtx_dt_cons_wf_rec dd c = true := by
      cases T <;> simp_all [__smtx_dt_cons_wf_rec, native_and]
    have hFieldNe : fieldType dd T ≠ SmtType.None := by
      rcases hField.1 with ⟨s, rfl⟩ | ⟨hInh, _⟩
      · simp [fieldType]
      · have := native_inhabited_type_ne_none hInh
        cases T <;> simp_all [fieldType]
    rw [__smtx_datatype_cons_default] at hne ⊢
    by_cases hf : __smtx_field_type_default dd T ddF = SmtValue.NotValue
    · simp [hf, native_ite, native_veq] at hne
    · simp only [native_ite, native_veq, hf, decide_false, Bool.false_eq_true,
        ite_false] at hne ⊢
      refine ihTail hField.2 hDecl hAgree R d ?_ hne
      rw [dtc_resolve_cons] at hv
      simp [__smtx_typeof_value, hv, ihField hDecl hAgree hField.1 hf,
        __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
        __smtx_typeof_guard, native_ite, native_Teq, hFieldNe]
  case refine_20 dd s ddF ih hDecl hAgree _ hne =>
    simp only [__smtx_field_type_default] at hne
    simpa [__smtx_field_type_default, fieldType] using ih hDecl hAgree hne
  case refine_21 dd T ddF hnotref ih hDecl hAgree hField hne =>
    rcases hField with ⟨s, hs⟩ | ⟨hInh, hRec⟩
    · exact absurd hs (hnotref s)
    · have h := ih hInh hRec
      cases T <;> simp_all [__smtx_field_type_default, fieldType]

end Smtm
