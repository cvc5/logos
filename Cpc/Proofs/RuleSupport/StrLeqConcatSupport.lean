module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrLeqConcatSupport

theorem eqs_of_requires4_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term)
    (hProg :
      __eo_requires
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h123 := StrEqReplSupport.eo_and_eq_true_left hGuard
  have h4 := StrEqReplSupport.eo_and_eq_true_right hGuard
  have h12 := StrEqReplSupport.eo_and_eq_true_left h123
  have h3 := StrEqReplSupport.eo_and_eq_true_right h123
  have h1 := StrEqReplSupport.eo_and_eq_true_left h12
  have h2 := StrEqReplSupport.eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4⟩

theorem eo_typeof_str_leq_args_of_ne_stuck
    (T U : Term)
    (h : __eo_typeof_str_lt T U ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧
      U = Term.Apply Term.Seq Term.Char := by
  cases T <;> simp [__eo_typeof_str_lt] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp opx =>
          cases opx <;> simp at h ⊢
          case Char =>
            cases U <;> simp [__eo_typeof_str_lt] at h ⊢
            case Apply g y =>
              cases g <;> simp at h ⊢
              case UOp opg =>
                cases opg <;> simp at h ⊢
                case Seq =>
                  cases y <;> simp at h ⊢
                  case UOp opy =>
                    cases opy <;> simp at h ⊢

theorem eo_typeof_str_concat_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_concat A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_concat] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_concat] at h ⊢
            case Seq =>
              have hEq := RuleProofs.eq_of_requires_eq_true_not_stuck
                x y (Term.Apply Term.Seq x) h
              subst y
              simp

theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  have hCharNN : __eo_to_smt_type Term.Char ≠ SmtType.None := by decide
  simpa [TranslationProofs.eo_to_smt_type_char] using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type Term.Char) (SmtType.Seq (__eo_to_smt_type Term.Char))
      hCharNN)

theorem smtx_eval_str_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_leq x y) =
      __smtx_model_eval_str_leq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_str_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs →
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [impl_native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

theorem native_pack_string_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) = ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string,
    Smtm.native_unpack_pack_seq, impl_native_ssm_char_of_value,
    Function.comp_def]

theorem native_pack_string_inj (s t : native_String) :
    native_pack_string s = native_pack_string t ↔ s = t := by
  constructor
  · intro h
    have := congrArg native_unpack_string h
    simpa [native_unpack_string_pack_string] using this
  · intro h
    rw [h]

theorem native_pack_seq_concat_eq_pack_string_append
    (sx sy : SmtSeq)
    (hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq SmtType.Char)
    (hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq SmtType.Char) :
    native_pack_seq (__smtx_elem_typeof_seq_value sx)
        (native_unpack_seq sx ++ native_unpack_seq sy) =
      native_pack_string
        (native_unpack_string sx ++ native_unpack_string sy) := by
  have hSxTyped : list_typed SmtType.Char (native_unpack_seq sx) :=
    typed_unpack_seq_of_typeof_seq_value hSxTy
  have hSyTyped : list_typed SmtType.Char (native_unpack_seq sy) :=
    typed_unpack_seq_of_typeof_seq_value hSyTy
  have hSxMap := list_typed_char_pack_unpack hSxTyped
  have hSyMap := list_typed_char_pack_unpack hSyTyped
  have hSxMap' :
      (native_unpack_seq sx).map
          (SmtValue.Char ∘ impl_native_ssm_char_of_value) =
        native_unpack_seq sx := by
    simpa [Function.comp_def] using hSxMap
  have hSyMap' :
      (native_unpack_seq sy).map
          (SmtValue.Char ∘ impl_native_ssm_char_of_value) =
        native_unpack_seq sy := by
    simpa [Function.comp_def] using hSyMap
  have hSxElem : __smtx_elem_typeof_seq_value sx = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  unfold native_pack_string native_unpack_string
  rw [hSxElem, List.map_append]
  simp only [List.map_map]
  rw [hSxMap', hSyMap']

def native_str_leq_bool (s t : native_String) : native_Bool :=
  SmtEval.native_or (decide (s = t)) (native_str_lt s t)

theorem native_str_leq_bool_append_left_of_same_len_ne
    (s t tail : native_String)
    (hLen : s.length = t.length) (hNe : s ≠ t) :
    native_str_leq_bool (s ++ tail) t = native_str_leq_bool s t := by
  induction s generalizing t with
  | nil =>
      have hTNil : t = [] := List.eq_nil_of_length_eq_zero hLen.symm
      exact False.elim (hNe hTNil.symm)
  | cons x xs ih =>
      cases t with
      | nil => simp at hLen
      | cons y ys =>
          have hTailLen : xs.length = ys.length := by simpa using hLen
          by_cases hxy : x = y
          · subst y
            have hTailNe : xs ≠ ys := by
              intro h
              exact hNe (by rw [h])
            simpa [native_str_leq_bool, native_str_lt,
              List.cons_lt_cons_iff] using ih ys hTailLen hTailNe
          · simp [native_str_leq_bool, native_str_lt,
              List.cons_lt_cons_iff, hxy]

theorem native_str_leq_bool_append_right_of_same_len_ne
    (s t tail : native_String)
    (hLen : s.length = t.length) (hNe : s ≠ t) :
    native_str_leq_bool s (t ++ tail) = native_str_leq_bool s t := by
  induction s generalizing t with
  | nil =>
      have hTNil : t = [] := List.eq_nil_of_length_eq_zero hLen.symm
      exact False.elim (hNe hTNil.symm)
  | cons x xs ih =>
      cases t with
      | nil => simp at hLen
      | cons y ys =>
          have hTailLen : xs.length = ys.length := by simpa using hLen
          by_cases hxy : x = y
          · subst y
            have hTailNe : xs ≠ ys := by
              intro h
              exact hNe (by rw [h])
            simpa [native_str_leq_bool, native_str_lt,
              List.cons_lt_cons_iff] using ih ys hTailLen hTailNe
          · simp [native_str_leq_bool, native_str_lt,
              List.cons_lt_cons_iff, hxy]

theorem smtx_eval_str_leq_pack_string
    (s t : native_String) :
    __smtx_model_eval_str_leq
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string t)) =
      SmtValue.Boolean (native_str_leq_bool s t) := by
  simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
    __smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
    native_str_leq_bool, native_unpack_string_pack_string,
    native_pack_string_inj, SmtEval.native_or]

end StrLeqConcatSupport
