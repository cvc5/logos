module

public import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import all Cpc.Proofs.RuleSupport.RegexRewriteSupport
public import Cpc.Proofs.RuleSupport.ReInterCstringSupport
import all Cpc.Proofs.RuleSupport.ReInterCstringSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport

public section

open Eo
open SmtEval
open Smtm

-- Keep string coercions on the model's explicit string-to-value embedding.
attribute [-instance] List.instMonad List.instAlternativeMonad_mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-!
Shared helpers for regex rules over constant strings (`str.to_re`):
EO-level typing inversions, SMT typing of `str.to_re`/`re.inter`, and
model-evaluation facts for string membership in `str.to_re` languages.
-/

namespace ReConstSupport

/-- The premise `(= (str.in_re s r) true)`. -/
abbrev strInRePrem (s r : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
    (Term.Boolean true)

/-! ### EO-level helpers -/

theorem eqs_of_eo_and2_eq_true
    (x1 y1 x2 y2 : Term)
    (h : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) =
        Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 := by
  rcases ReInterCstringProof.eo_and_eq_true h with ⟨h1, h2⟩
  exact ⟨ReInterCstringProof.eo_eq_eq_true h1,
    ReInterCstringProof.eo_eq_eq_true h2⟩

theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  cases A with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
                cases B with
                | UOp opb =>
                    cases opb <;> simp [__eo_typeof_str_in_re] at h ⊢
                | _ => simp [__eo_typeof_str_in_re] at h
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

theorem eo_typeof_str_to_re_eq_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_to_re T ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_to_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_to_re] at h ⊢
            | _ => simp [__eo_typeof_str_to_re] at h
      | _ => simp [__eo_typeof_str_to_re] at h
  | _ => simp [__eo_typeof_str_to_re] at h

/-! ### SMT typing -/

theorem smt_seq_char_of_eo_type (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  have hsimpa := hTyRaw
  try simp [TranslationProofs.eo_to_smt_type_seq,
    TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
  exact hsimpa

theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSTy, native_ite, native_Teq]

theorem smtx_typeof_re_inter_of_args (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.RegLan
  rw [typeof_re_inter_eq]
  simp [hx, hy, native_ite, native_Teq]

theorem reInter_list_smt_typeof_reglan_of_non_none (t : Term) :
    __eo_is_list (Term.UOp UserOp.re_inter) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan := by
  intro hList hNN
  cases t <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList ⊢
  next op =>
    cases op <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, __smtx_typeof] at hList ⊢
  next f y =>
    cases f <;>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_ok, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList ⊢
    next g x =>
      rw [← hList.1] at hNN ⊢
      have hArgs :
          __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ∧
            __smtx_typeof (__eo_to_smt y) = SmtType.RegLan :=
        reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
          (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN
      change __smtx_typeof
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.RegLan
      rw [typeof_re_inter_eq]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]

/-! ### Sequence values -/

theorem seq_char_eval (M : SmtModel) (hM : model_wf M) (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    ∃ ss : SmtSeq,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  exact ⟨ss, hSEval, by simpa [hSEval, __smtx_typeof_value] using hSEvalTy⟩

theorem smt_seq_eq_of_unpack_eq_same_type
    (sx sy : SmtSeq) (T : SmtType)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T)
    (hUnpack : native_unpack_seq sx = native_unpack_seq sy) :
    sx = sy := by
  have hSxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  calc
    sx = native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx) := (native_pack_unpack_seq sx).symm
    _ = native_pack_seq (__smtx_elem_typeof_seq_value sy)
        (native_unpack_seq sy) := by
          rw [hSxElem, hSyElem, hUnpack]
    _ = sy := native_pack_unpack_seq sy

/-! ### Membership in `str.to_re` languages -/

theorem str_in_re_true_of_prem
    (M : SmtModel) (s r : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (strInRePrem s r) true) :
    native_str_in_re (native_unpack_string ss) rv = true := by
  have hUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)
      (Term.Boolean true) hPrem
  have hInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval,
      hUnpack]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInEval, hTrueEval] at hPremRel
  have hValueEq :
      SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hValueEq

theorem nativeListInRe_char_self
    (c : native_Char) (hc : native_char_valid c = true) :
    RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [RuleProofs.nativeListInRe, native_re_deriv, native_re_nullable, hc]

theorem nativeListInRe_re_of_list_self :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        RuleProofs.nativeListInRe pat (impl_native_re_of_list pat) = true
  | [], _ => by
      simp [impl_native_re_of_list, RuleProofs.nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases RuleProofs.native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self c hc
      have hTail : RuleProofs.nativeListInRe cs (impl_native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self cs hcs
      have hConcat :
          RuleProofs.nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list cs)) = true :=
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (c :: cs) (SmtRegLan.char c) (impl_native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [impl_native_re_of_list] using hConcat

theorem native_str_in_re_str_to_re_self
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    native_str_in_re pat (native_str_to_re pat) = true := by
  rw [← RuleProofs.native_str_in_re_eq_model]
  simpa [RuleProofs.native_str_in_re, hValid, native_str_to_re] using
    nativeListInRe_re_of_list_self pat hValid

/-- `str.in_re st (str.to_re ss)` evaluates like `st = ss` on string values. -/
theorem smtx_model_eval_re_in_cstring_eq
    (st ss : SmtSeq)
    (hStTy : __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval_str_in_re (SmtValue.Seq st)
        (SmtValue.RegLan (native_str_to_re (native_unpack_seq ss))) =
      __smtx_model_eval_eq (SmtValue.Seq st) (SmtValue.Seq ss) := by
  have hStUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hStTy
  have hSsUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  change
    SmtValue.Boolean
        (Smtm.native_str_in_re (native_unpack_seq st)
          (native_str_to_re (native_unpack_seq ss))) =
      SmtValue.Boolean (native_veq (SmtValue.Seq st) (SmtValue.Seq ss))
  rw [hStUnpack, hSsUnpack]
  by_cases hEq : st = ss
  · subst st
    have hValid : native_string_valid (native_unpack_string ss) = true :=
      native_unpack_string_valid_of_typeof_seq_char hSsTy
    have hMem :
        native_str_in_re (native_unpack_string ss)
          (native_str_to_re (native_unpack_string ss)) = true :=
      native_str_in_re_str_to_re_self (native_unpack_string ss) hValid
    simp [hMem, native_veq]
  · have hValueNe : SmtValue.Seq st ≠ SmtValue.Seq ss := by
      intro hVal
      cases hVal
      exact hEq rfl
    have hMemFalse :
        native_str_in_re (native_unpack_string st)
          (native_str_to_re (native_unpack_string ss)) = false := by
      cases hMem :
          native_str_in_re (native_unpack_string st)
            (native_str_to_re (native_unpack_string ss))
      · rfl
      · have hMemStr :
            RuleProofs.native_str_in_re (native_unpack_string st)
                (native_str_to_re (native_unpack_string ss)) = true := by
          rw [RuleProofs.native_str_in_re_eq_model]
          exact hMem
        have hStrEq :
            native_unpack_string st = native_unpack_string ss :=
          RuleProofs.native_str_in_re_str_to_re_eq
            (native_unpack_string_valid_of_typeof_seq_char hStTy) (by
              simpa [impl_native_string_to_values, List.map_eq_flatMap] using hMemStr)
        have hPackSt :
            native_pack_string (native_unpack_string st) = st :=
          StrLeqConcatSupport.native_pack_string_unpack_string_of_typeof_seq_char
            st hStTy
        have hPackSs :
            native_pack_string (native_unpack_string ss) = ss :=
          StrLeqConcatSupport.native_pack_string_unpack_string_of_typeof_seq_char
            ss hSsTy
        have hSeqEq : st = ss := by
          rw [← hPackSt, ← hPackSs, hStrEq]
        exact False.elim (hEq hSeqEq)
    simp [hMemFalse, native_veq, hValueNe]

end ReConstSupport
