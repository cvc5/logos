module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

public section

open Eo
open SmtEval
open Smtm
open StrLeqConcatSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrLeqConcatNarySupport

theorem eqs_of_requires6_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 B : Term)
    (hProg :
      __eo_requires
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
                  (__eo_eq x3 y3))
                (__eo_eq x4 y4))
              (__eo_eq x5 y5))
            (__eo_eq x6 y6))
          (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 ∧
      y5 = x5 ∧ y6 = x6 := by
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
                (__eo_eq x3 y3))
              (__eo_eq x4 y4))
            (__eo_eq x5 y5))
          (__eo_eq x6 y6) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h12345 := StrEqReplSupport.eo_and_eq_true_left hGuard
  have h6 := StrEqReplSupport.eo_and_eq_true_right hGuard
  have h1234 := StrEqReplSupport.eo_and_eq_true_left h12345
  have h5 := StrEqReplSupport.eo_and_eq_true_right h12345
  have h123 := StrEqReplSupport.eo_and_eq_true_left h1234
  have h4 := StrEqReplSupport.eo_and_eq_true_right h1234
  have h12 := StrEqReplSupport.eo_and_eq_true_left h123
  have h3 := StrEqReplSupport.eo_and_eq_true_right h123
  have h1 := StrEqReplSupport.eo_and_eq_true_left h12
  have h2 := StrEqReplSupport.eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4,
    RuleProofs.eq_of_eo_eq_true x5 y5 h5,
    RuleProofs.eq_of_eo_eq_true x6 y6 h6⟩

abbrev mkStrLeq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y

theorem native_str_leq_bool_append_common
    (pre s t : native_String) :
    native_str_leq_bool (pre ++ s) (pre ++ t) =
      native_str_leq_bool s t := by
  induction pre with
  | nil => rfl
  | cons c pre ih =>
      simpa [native_str_leq_bool, native_str_lt,
        List.cons_lt_cons_iff] using ih

theorem native_str_leq_bool_append_both_of_same_len_ne
    (s t sTail tTail : native_String)
    (hLen : s.length = t.length) (hNe : s ≠ t) :
    native_str_leq_bool (s ++ sTail) (t ++ tTail) =
      native_str_leq_bool s t := by
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
              List.cons_lt_cons_iff] using
                ih ys hTailLen hTailNe
          · simp [native_str_leq_bool, native_str_lt,
              List.cons_lt_cons_iff, hxy]

private theorem eval_type_seq_char
    (M : SmtModel) (hM : model_wf M) (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) =
      SmtType.Seq SmtType.Char) :
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
      SmtType.Seq SmtType.Char := by
  simpa [hxTy] using
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
      unfold term_has_non_none_type
      rw [hxTy]
      simp)

theorem smtx_typeof_list_concat_rec_of_eo_type
    (a z U : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hRecEoTy :
      __eo_typeof (__eo_list_concat_rec a z) = Term.Apply Term.Seq U) :
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.Seq (__eo_to_smt_type U) := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      simp [__eo_is_list] at hList
  | case2 a hA =>
      unfold RuleProofs.eo_has_smt_translation at hZTrans
      exact False.elim (hZTrans rfl)
  | case3 g x y z hZ ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
          g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) x y hList
      have hTailNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) y z hTailList hZ
      have hRecEq :
          __eo_list_concat_rec (mkConcat x y) z =
            mkConcat x (__eo_list_concat_rec y z) :=
        eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x y z hTailNe
      rw [hRecEq] at hRecEoTy ⊢
      have hRecArgs :=
        StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
          x (__eo_list_concat_rec y z) U hRecEoTy
      have hPrefixNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        simpa [RuleProofs.eo_has_smt_translation] using hATrans
      rcases str_concat_args_of_non_none x y hPrefixNN with
        ⟨T, hXTyT, hYTyT⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyT]
        exact seq_ne_none T
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyT]
        exact seq_ne_none T
      have hXTy := StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof x U
        hXTrans hRecArgs.1
      have hTailTy := ih hTailList hYTrans hZTrans hRecArgs.2
      exact smt_typeof_str_concat_of_seq x (__eo_list_concat_rec y z)
        (__eo_to_smt_type U) hXTy hTailTy
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq] at hRecEoTy ⊢
      exact StrConcatClashSupport.smtx_typeof_seq_of_eo_typeof z U
        hZTrans hRecEoTy

theorem smtx_eval_str_leq_list_concat_rec_common
    (M : SmtModel) (hM : model_wf M) :
    ∀ (a z1 z2 : Term),
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt z1) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt z2) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z1)) =
        SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z2)) =
        SmtType.Seq SmtType.Char ->
      __smtx_model_eval M
          (__eo_to_smt
            (mkStrLeq (__eo_list_concat_rec a z1)
              (__eo_list_concat_rec a z2))) =
        __smtx_model_eval M (__eo_to_smt (mkStrLeq z1 z2)) := by
  intro a z1 z2
  induction a, z1 using __eo_list_concat_rec.induct generalizing z2 with
  | case1 z1 =>
      intro hList
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro _ hZ1Ty
      change __smtx_typeof SmtTerm.None = SmtType.Seq SmtType.Char at hZ1Ty
      rw [TranslationProofs.smtx_typeof_none] at hZ1Ty
      cases hZ1Ty
  | case3 g x y z1 hZ1 ih =>
      intro hList hZ1Ty hZ2Ty hRec1Ty hRec2Ty
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
          g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) x y hList
      have hZ2 : z2 ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq z2 SmtType.Char hZ2Ty
      have hTail1Ne : __eo_list_concat_rec y z1 ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) y z1 hTailList hZ1
      have hTail2Ne : __eo_list_concat_rec y z2 ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) y z2 hTailList hZ2
      have hRec1Eq :
          __eo_list_concat_rec (mkConcat x y) z1 =
            mkConcat x (__eo_list_concat_rec y z1) :=
        eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x y z1 hTail1Ne
      have hRec2Eq :
          __eo_list_concat_rec (mkConcat x y) z2 =
            mkConcat x (__eo_list_concat_rec y z2) :=
        eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x y z2 hTail2Ne
      rw [hRec1Eq] at hRec1Ty
      rw [hRec2Eq] at hRec2Ty
      have hArgs1 := str_concat_args_of_seq_type x
        (__eo_list_concat_rec y z1) SmtType.Char hRec1Ty
      have hArgs2 := str_concat_args_of_seq_type x
        (__eo_list_concat_rec y z2) SmtType.Char hRec2Ty
      have hXTy := hArgs1.1
      have hTail1Ty := hArgs1.2
      have hTail2Ty := hArgs2.2
      have hXEvalTy := eval_type_seq_char M hM x hXTy
      have hTail1EvalTy := eval_type_seq_char M hM
        (__eo_list_concat_rec y z1) hTail1Ty
      have hTail2EvalTy := eval_type_seq_char M hM
        (__eo_list_concat_rec y z2) hTail2Ty
      rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
      rcases seq_value_canonical hTail1EvalTy with ⟨s1, hTail1Eval⟩
      rcases seq_value_canonical hTail2EvalTy with ⟨s2, hTail2Eval⟩
      have hSxTy :
          __smtx_typeof_seq_value sx = SmtType.Seq SmtType.Char := by
        simpa [__smtx_typeof_value, hXEval] using hXEvalTy
      have hS1Ty :
          __smtx_typeof_seq_value s1 = SmtType.Seq SmtType.Char := by
        simpa [__smtx_typeof_value, hTail1Eval] using hTail1EvalTy
      have hS2Ty :
          __smtx_typeof_seq_value s2 = SmtType.Seq SmtType.Char := by
        simpa [__smtx_typeof_value, hTail2Eval] using hTail2EvalTy
      have hXPack : native_pack_string (native_unpack_string sx) = sx :=
        native_pack_string_unpack_string_of_typeof_seq_char sx hSxTy
      have hS1Pack : native_pack_string (native_unpack_string s1) = s1 :=
        native_pack_string_unpack_string_of_typeof_seq_char s1 hS1Ty
      have hS2Pack : native_pack_string (native_unpack_string s2) = s2 :=
        native_pack_string_unpack_string_of_typeof_seq_char s2 hS2Ty
      have hConcat1Pack :
          native_pack_seq (__smtx_elem_typeof_seq_value sx)
              (native_unpack_seq sx ++ native_unpack_seq s1) =
            native_pack_string
              (native_unpack_string sx ++ native_unpack_string s1) :=
        native_pack_seq_concat_eq_pack_string_append sx s1 hSxTy hS1Ty
      have hConcat2Pack :
          native_pack_seq (__smtx_elem_typeof_seq_value sx)
              (native_unpack_seq sx ++ native_unpack_seq s2) =
            native_pack_string
              (native_unpack_string sx ++ native_unpack_string s2) :=
        native_pack_seq_concat_eq_pack_string_append sx s2 hSxTy hS2Ty
      have hCancel :
          __smtx_model_eval M
              (__eo_to_smt
                (mkStrLeq
                  (mkConcat x (__eo_list_concat_rec y z1))
                  (mkConcat x (__eo_list_concat_rec y z2)))) =
            __smtx_model_eval M
              (__eo_to_smt
                (mkStrLeq (__eo_list_concat_rec y z1)
                  (__eo_list_concat_rec y z2))) := by
        change __smtx_model_eval M
            (SmtTerm.str_leq
              (SmtTerm.str_concat (__eo_to_smt x)
                (__eo_to_smt (__eo_list_concat_rec y z1)))
              (SmtTerm.str_concat (__eo_to_smt x)
                (__eo_to_smt (__eo_list_concat_rec y z2)))) =
          __smtx_model_eval M
            (SmtTerm.str_leq
              (__eo_to_smt (__eo_list_concat_rec y z1))
              (__eo_to_smt (__eo_list_concat_rec y z2)))
        rw [smtx_eval_str_leq_term_eq,
          smtx_eval_str_concat_term_eq, smtx_eval_str_concat_term_eq,
          smtx_eval_str_leq_term_eq, hXEval, hTail1Eval, hTail2Eval]
        change __smtx_model_eval_str_leq
            (SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sx)
                (native_unpack_seq sx ++ native_unpack_seq s1)))
            (SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sx)
                (native_unpack_seq sx ++ native_unpack_seq s2))) =
          __smtx_model_eval_str_leq (SmtValue.Seq s1) (SmtValue.Seq s2)
        rw [hConcat1Pack, hConcat2Pack, ← hS1Pack, ← hS2Pack,
          smtx_eval_str_leq_pack_string, smtx_eval_str_leq_pack_string]
        simp only [native_unpack_string_pack_string]
        congr 1
        exact native_str_leq_bool_append_common _ _ _
      rw [hRec1Eq, hRec2Eq]
      exact hCancel.trans
        (ih z2 hTailList hZ1Ty hZ2Ty hTail1Ty hTail2Ty)
  | case4 nil z1 hNil hZ1 hNot =>
      intro _ _ hZ2Ty _ _
      have hZ2 : z2 ≠ Term.Stuck :=
        term_ne_stuck_of_smt_type_seq z2 SmtType.Char hZ2Ty
      have hEq1 : __eo_list_concat_rec nil z1 = z1 := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      have hEq2 : __eo_list_concat_rec nil z2 = z2 := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq1, hEq2]

end StrLeqConcatNarySupport
