module

public import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import all Cpc.Proofs.RuleSupport.ConcatSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_prog_concat_split_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_split rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s tc sc,
      x1 = mkEq t s ∧
        x2 = mkNot (mkEq (mkStrLen tc) (mkStrLen sc)) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 t =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply notOp inner =>
                      cases notOp with
                      | UOp notU =>
                          cases notU with
                          | not =>
                              cases inner with
                              | Apply lhs2 rhs2 =>
                                  cases lhs2 with
                                  | Apply op2 lhsLen =>
                                      cases op2 with
                                      | UOp u2 =>
                                          cases u2 with
                                          | eq =>
                                              cases lhsLen with
                                              | Apply lenOp tc =>
                                                  cases lenOp with
                                                  | UOp lenU1 =>
                                                      cases lenU1 with
                                                      | str_len =>
                                                          cases rhs2 with
                                                          | Apply lenOp2 sc =>
                                                              cases lenOp2 with
                                                              | UOp lenU2 =>
                                                                  cases lenU2 with
                                                                  | str_len =>
                                                                      exact
                                                                        ⟨t, rhs1, tc, sc,
                                                                          rfl, rfl⟩
                                                                  | _ =>
                                                                      cases rev <;>
                                                                        simp [__eo_prog_concat_split]
                                                                          at hProg
                                                              | _ =>
                                                                  cases rev <;>
                                                                    simp [__eo_prog_concat_split]
                                                                      at hProg
                                                          | _ =>
                                                              cases rev <;>
                                                                simp [__eo_prog_concat_split]
                                                                  at hProg
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_split]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_split]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_split]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_split] at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_split] at hProg
                                  | _ =>
                                      cases rev <;> simp [__eo_prog_concat_split] at hProg
                              | _ =>
                                  cases rev <;> simp [__eo_prog_concat_split] at hProg
                          | _ =>
                              cases rev <;> simp [__eo_prog_concat_split] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_split] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_split] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_split] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_split] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_split] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_split] at hProg

private theorem concat_split_lengths_ne_of_not_len_eq_eval
    (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hLenNe :
      eo_interprets M (mkNot (mkEq (mkStrLen x) (mkStrLen y))) true) :
    (native_unpack_seq sx).length ≠ (native_unpack_seq sy).length := by
  have hEqFalse :
      eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) false :=
    RuleProofs.eo_interprets_not_true_implies_false M
      (mkEq (mkStrLen x) (mkStrLen y)) hLenNe
  have hEval :
      __smtx_model_eval M (__eo_to_smt (mkEq (mkStrLen x) (mkStrLen y))) =
        SmtValue.Boolean false := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (mkEq (mkStrLen x) (mkStrLen y)) false).mp hEqFalse with
    | intro_false _ hEval => exact hEval
  change
    __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.str_len (__eo_to_smt y))) =
      SmtValue.Boolean false at hEval
  rw [smtx_eval_eq_term_eq] at hEval
  rw [smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq] at hEval
  simp [hxEval, hyEval, __smtx_model_eval_str_len,
    __smtx_model_eval_eq, native_seq_len, native_veq] at hEval
  intro hLen
  exact hEval (by exact_mod_cast hLen)

private theorem facts_concat_split_false_formula
    (M : SmtModel) (hM : model_wf M)
    (tc sc tTail sTail : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T)
    (hsTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tc tTail) (mkConcat sc sTail)) true)
    (hLenNe :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) true) :
    eo_interprets M (concatSplitFalseFormula tc sc) true := by
  let split := concatSplitTerm tc sc (Term.Boolean false)
  let nilS := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof sc)
  let nilT := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof tc)
  let rhsT := mkConcat sc (mkConcat split nilS)
  let rhsS := mkConcat tc (mkConcat split nilT)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_false tc sc T htcTy hscTy
  have hNilSTy :
      __smtx_typeof (__eo_to_smt nilS) = SmtType.Seq T := by
    simpa [nilS] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq sc T hscTy
  have hNilTTy :
      __smtx_typeof (__eo_to_smt nilT) = SmtType.Seq T := by
    simpa [nilT] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq tc T htcTy
  have hSplitNilS :
      __smtx_typeof (__eo_to_smt (mkConcat split nilS)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilS T hSplitTy hNilSTy
  have hSplitNilT :
      __smtx_typeof (__eo_to_smt (mkConcat split nilT)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq split nilT T hSplitTy hNilTTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq sc (mkConcat split nilS)
      T hscTy hSplitNilS
  have hRhsSTy : __smtx_typeof (__eo_to_smt rhsS) = SmtType.Seq T := by
    simpa [rhsS] using smt_typeof_mkConcat_seq tc (mkConcat split nilT)
      T htcTy hSplitNilT
  have hEqTBool : RuleProofs.eo_has_bool_type (mkEq tc rhsT) :=
    eo_has_bool_type_eq_of_seq_type tc rhsT T htcTy hRhsTTy
  have hEqSBool : RuleProofs.eo_has_bool_type (mkEq sc rhsS) :=
    eo_has_bool_type_eq_of_seq_type sc rhsS T hscTy hRhsSTy
  have hOrRightBool :
      RuleProofs.eo_has_bool_type (mkOr (mkEq sc rhsS) (Term.Boolean false)) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq sc rhsS) (Term.Boolean false) hEqSBool
      RuleProofs.eo_has_bool_type_false
  rcases concat_split_append_eq_of_concat_eq M hM tc tTail sc sTail T
      htcTy htTailTy hscTy hsTailTy hConcatEq with
    ⟨st, stTail, ss, ssTail, htcEval, _htTailEval, hscEval, _hsTailEval,
      hAppend⟩
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hLenNeLists :
      (native_unpack_seq st).length ≠ (native_unpack_seq ss).length :=
    concat_split_lengths_ne_of_not_len_eq_eval M tc sc st ss htcEval hscEval
      hLenNe
  have hLenNeXY : xs.length ≠ ys.length := by
    simpa [xs, ys] using hLenNeLists
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hstElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hssElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have hNilSEval :
      __smtx_model_eval M (__eo_to_smt nilS) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nilS] using eval_nil_str_concat_typeof_of_smt_type_seq M sc T hscTy
  have hNilTEval :
      __smtx_model_eval M (__eo_to_smt nilT) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nilT] using eval_nil_str_concat_typeof_of_smt_type_seq M tc T htcTy
  by_cases hleOrig :
      (native_unpack_seq ss).length <= (native_unpack_seq st).length
  · have hle : ys.length <= xs.length := by
      simpa [xs, ys] using hleOrig
    have hAppendXY :
        xs ++ native_unpack_seq stTail =
          ys ++ native_unpack_seq ssTail := by
      simpa [xs, ys] using hAppend
    have hList : xs = ys ++ xs.drop ys.length :=
      concat_split_left_eq_append_drop_of_append_eq_of_le xs ys
        (native_unpack_seq stTail) (native_unpack_seq ssTail) hAppendXY hle
    have hSplitEval :
        __smtx_model_eval M (__eo_to_smt split) =
          SmtValue.Seq (native_pack_seq T (xs.drop ys.length)) := by
      simpa [split, xs, ys] using
        eval_concatSplitTerm_false_left M hM tc sc T htcTy hscTy st ss
          htcEval hscEval hleOrig
    have hRhsEval :
        __smtx_model_eval M (__eo_to_smt rhsT) =
          SmtValue.Seq (native_pack_seq T xs) := by
      have hNested := eval_mkConcat_right_nested M sc split nilS T ss
        (native_pack_seq T (xs.drop ys.length)) (SmtSeq.empty T) hscEval
        hSplitEval hNilSEval hssElem
      calc
        __smtx_model_eval M (__eo_to_smt rhsT) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq ss ++
                  native_unpack_seq (native_pack_seq T (xs.drop ys.length)) ++
                  native_unpack_seq (SmtSeq.empty T))) := by
          simpa only [rhsT] using hNested
        _ = SmtValue.Seq (native_pack_seq T xs) := by
          rw [_root_.native_unpack_pack_seq]
          change
            SmtValue.Seq
              (native_pack_seq T (ys ++ xs.drop ys.length ++ [])) =
            SmtValue.Seq (native_pack_seq T xs)
          rw [List.append_nil, ← hList]
    have hEqRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt tc))
          (__smtx_model_eval M (__eo_to_smt rhsT)) := by
      unfold RuleProofs.smt_value_rel
      rw [htcEval, hRhsEval]
      exact smt_seq_rel_pack_unpack T st hstElem
    have hEqTrue : eo_interprets M (mkEq tc rhsT) true :=
      RuleProofs.eo_interprets_eq_of_rel M tc rhsT hEqTBool hEqRel
    have hSplitPos : 0 < (xs.drop ys.length).length := by
      rw [List.length_drop]
      omega
    have hTailTrue :
        eo_interprets M
          (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
            (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
          true :=
      concat_split_nonempty_tail M split T (xs.drop ys.length) hSplitTy
        hSplitEval hSplitPos
    have hOrTrue :
        eo_interprets M
          (mkOr (mkEq tc rhsT)
            (mkOr (mkEq sc rhsS) (Term.Boolean false))) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_left_intro M hM (mkEq tc rhsT)
          (mkOr (mkEq sc rhsS) (Term.Boolean false)) hEqTrue hOrRightBool
    simpa [concatSplitFalseFormula, split, nilS, nilT, rhsT, rhsS, mkAnd,
      mkOr] using
      RuleProofs.eo_interprets_and_intro M
        (mkOr (mkEq tc rhsT) (mkOr (mkEq sc rhsS) (Term.Boolean false)))
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        hOrTrue hTailTrue
  · have hltOrig :
        (native_unpack_seq st).length < (native_unpack_seq ss).length := by
      omega
    have hlt : xs.length < ys.length := by
      simpa [xs, ys] using hltOrig
    have hleRight : xs.length <= ys.length := Nat.le_of_lt hlt
    have hAppendYX :
        ys ++ native_unpack_seq ssTail =
          xs ++ native_unpack_seq stTail := by
      simpa [xs, ys] using hAppend.symm
    have hList : ys = xs ++ ys.drop xs.length :=
      concat_split_left_eq_append_drop_of_append_eq_of_le ys xs
        (native_unpack_seq ssTail) (native_unpack_seq stTail) hAppendYX hleRight
    have hSplitEval :
        __smtx_model_eval M (__eo_to_smt split) =
          SmtValue.Seq (native_pack_seq T (ys.drop xs.length)) := by
      simpa [split, xs, ys] using
        eval_concatSplitTerm_false_right M hM tc sc T htcTy hscTy st ss
          htcEval hscEval hltOrig
    have hRhsEval :
        __smtx_model_eval M (__eo_to_smt rhsS) =
          SmtValue.Seq (native_pack_seq T ys) := by
      have hNested := eval_mkConcat_right_nested M tc split nilT T st
        (native_pack_seq T (ys.drop xs.length)) (SmtSeq.empty T) htcEval
        hSplitEval hNilTEval hstElem
      calc
        __smtx_model_eval M (__eo_to_smt rhsS) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq st ++
                  native_unpack_seq (native_pack_seq T (ys.drop xs.length)) ++
                  native_unpack_seq (SmtSeq.empty T))) := by
          simpa only [rhsS] using hNested
        _ = SmtValue.Seq (native_pack_seq T ys) := by
          rw [_root_.native_unpack_pack_seq]
          change
            SmtValue.Seq
              (native_pack_seq T (xs ++ ys.drop xs.length ++ [])) =
            SmtValue.Seq (native_pack_seq T ys)
          rw [List.append_nil, ← hList]
    have hEqRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sc))
          (__smtx_model_eval M (__eo_to_smt rhsS)) := by
      unfold RuleProofs.smt_value_rel
      rw [hscEval, hRhsEval]
      exact smt_seq_rel_pack_unpack T ss hssElem
    have hEqTrue : eo_interprets M (mkEq sc rhsS) true :=
      RuleProofs.eo_interprets_eq_of_rel M sc rhsS hEqSBool hEqRel
    have hSplitPos : 0 < (ys.drop xs.length).length := by
      rw [List.length_drop]
      omega
    have hTailTrue :
        eo_interprets M
          (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
            (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
          true :=
      concat_split_nonempty_tail M split T (ys.drop xs.length) hSplitTy
        hSplitEval hSplitPos
    have hOrRightTrue :
        eo_interprets M (mkOr (mkEq sc rhsS) (Term.Boolean false)) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_left_intro M hM (mkEq sc rhsS)
          (Term.Boolean false) hEqTrue RuleProofs.eo_has_bool_type_false
    have hOrTrue :
        eo_interprets M
          (mkOr (mkEq tc rhsT)
            (mkOr (mkEq sc rhsS) (Term.Boolean false))) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_right_intro M hM (mkEq tc rhsT)
          (mkOr (mkEq sc rhsS) (Term.Boolean false)) hEqTBool
          hOrRightTrue
    simpa [concatSplitFalseFormula, split, nilS, nilT, rhsT, rhsS, mkAnd,
      mkOr] using
      RuleProofs.eo_interprets_and_intro M
        (mkOr (mkEq tc rhsT) (mkOr (mkEq sc rhsS) (Term.Boolean false)))
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        hOrTrue hTailTrue

private theorem facts_concat_split_true_formula
    (M : SmtModel) (hM : model_wf M)
    (tc sc tPrefix sPrefix : Term) (T : SmtType)
    (htcTy : __smtx_typeof (__eo_to_smt tc) = SmtType.Seq T)
    (hscTy : __smtx_typeof (__eo_to_smt sc) = SmtType.Seq T)
    (htPrefixTy : __smtx_typeof (__eo_to_smt tPrefix) = SmtType.Seq T)
    (hsPrefixTy : __smtx_typeof (__eo_to_smt sPrefix) = SmtType.Seq T)
    (hConcatEq :
      eo_interprets M (mkEq (mkConcat tPrefix tc) (mkConcat sPrefix sc)) true)
    (hLenNe :
      eo_interprets M (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) true) :
    eo_interprets M (concatSplitTrueFormula tc sc) true := by
  let split := concatSplitTerm tc sc (Term.Boolean true)
  let nilSplit := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof split)
  let rhsT := mkConcat split (mkConcat sc nilSplit)
  let rhsS := mkConcat split (mkConcat tc nilSplit)
  have hSplitTy :
      __smtx_typeof (__eo_to_smt split) = SmtType.Seq T := by
    simpa [split] using smt_typeof_concatSplitTerm_true tc sc T htcTy hscTy
  have hNilSplitTy :
      __smtx_typeof (__eo_to_smt nilSplit) = SmtType.Seq T := by
    simpa [nilSplit] using
      smt_typeof_nil_str_concat_typeof_of_smt_type_seq split T hSplitTy
  have hSNil :
      __smtx_typeof (__eo_to_smt (mkConcat sc nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq sc nilSplit T hscTy hNilSplitTy
  have hTNil :
      __smtx_typeof (__eo_to_smt (mkConcat tc nilSplit)) =
        SmtType.Seq T :=
    smt_typeof_mkConcat_seq tc nilSplit T htcTy hNilSplitTy
  have hRhsTTy : __smtx_typeof (__eo_to_smt rhsT) = SmtType.Seq T := by
    simpa [rhsT] using smt_typeof_mkConcat_seq split (mkConcat sc nilSplit)
      T hSplitTy hSNil
  have hRhsSTy : __smtx_typeof (__eo_to_smt rhsS) = SmtType.Seq T := by
    simpa [rhsS] using smt_typeof_mkConcat_seq split (mkConcat tc nilSplit)
      T hSplitTy hTNil
  have hEqTBool : RuleProofs.eo_has_bool_type (mkEq tc rhsT) :=
    eo_has_bool_type_eq_of_seq_type tc rhsT T htcTy hRhsTTy
  have hEqSBool : RuleProofs.eo_has_bool_type (mkEq sc rhsS) :=
    eo_has_bool_type_eq_of_seq_type sc rhsS T hscTy hRhsSTy
  have hOrRightBool :
      RuleProofs.eo_has_bool_type (mkOr (mkEq sc rhsS) (Term.Boolean false)) := by
    simpa [mkOr] using RuleProofs.eo_has_bool_type_or_of_bool_args
      (mkEq sc rhsS) (Term.Boolean false) hEqSBool
      RuleProofs.eo_has_bool_type_false
  rcases concat_split_append_eq_of_concat_eq M hM tPrefix tc sPrefix sc T
      htPrefixTy htcTy hsPrefixTy hscTy hConcatEq with
    ⟨stPrefix, st, ssPrefix, ss, _htPrefixEval, htcEval, _hsPrefixEval,
      hscEval, hAppend⟩
  let xs := native_unpack_seq st
  let ys := native_unpack_seq ss
  have hLenNeLists :
      (native_unpack_seq st).length ≠ (native_unpack_seq ss).length :=
    concat_split_lengths_ne_of_not_len_eq_eval M tc sc st ss htcEval hscEval
      hLenNe
  have hLenNeXY : xs.length ≠ ys.length := by
    simpa [xs, ys] using hLenNeLists
  have htcValTy := smt_model_eval_preserves_type M hM (__eo_to_smt tc)
    (SmtType.Seq T) htcTy (seq_ne_none T) (type_inhabited_seq T)
  have hscValTy := smt_model_eval_preserves_type M hM (__eo_to_smt sc)
    (SmtType.Seq T) hscTy (seq_ne_none T) (type_inhabited_seq T)
  have hstTy : __smtx_typeof_seq_value st = SmtType.Seq T := by
    simpa [htcEval, __smtx_typeof_value] using htcValTy
  have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [hscEval, __smtx_typeof_value] using hscValTy
  have hstElem : __smtx_elem_typeof_seq_value st = T :=
    elem_typeof_seq_value_of_typeof_seq_value hstTy
  have hssElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hssTy
  have hNilSplitEval :
      __smtx_model_eval M (__eo_to_smt nilSplit) =
        SmtValue.Seq (SmtSeq.empty T) := by
    simpa [nilSplit] using
      eval_nil_str_concat_typeof_of_smt_type_seq M split T hSplitTy
  by_cases hleOrig :
      (native_unpack_seq ss).length <= (native_unpack_seq st).length
  · have hle : ys.length <= xs.length := by
      simpa [xs, ys] using hleOrig
    have hAppendXY :
        native_unpack_seq stPrefix ++ xs =
          native_unpack_seq ssPrefix ++ ys := by
      simpa [xs, ys] using hAppend
    have hList : xs = xs.take (xs.length - ys.length) ++ ys :=
      concat_split_suffix_eq_take_append_of_append_eq_of_le
        (native_unpack_seq stPrefix) xs (native_unpack_seq ssPrefix) ys
        hAppendXY hle
    have hSplitEval :
        __smtx_model_eval M (__eo_to_smt split) =
          SmtValue.Seq (native_pack_seq T (xs.take (xs.length - ys.length))) := by
      simpa [split, xs, ys] using
        eval_concatSplitTerm_true_left M hM tc sc T htcTy hscTy st ss
          htcEval hscEval hleOrig
    have hRhsEval :
        __smtx_model_eval M (__eo_to_smt rhsT) =
          SmtValue.Seq (native_pack_seq T xs) := by
      have hNested := eval_mkConcat_right_nested M split sc nilSplit T
        (native_pack_seq T (xs.take (xs.length - ys.length))) ss
        (SmtSeq.empty T) hSplitEval hscEval hNilSplitEval
        (elem_typeof_pack_seq T (xs.take (xs.length - ys.length)))
      calc
        __smtx_model_eval M (__eo_to_smt rhsT) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq
                    (native_pack_seq T (xs.take (xs.length - ys.length))) ++
                  native_unpack_seq ss ++ native_unpack_seq (SmtSeq.empty T))) := by
          simpa only [rhsT] using hNested
        _ = SmtValue.Seq (native_pack_seq T xs) := by
          rw [_root_.native_unpack_pack_seq]
          change
            SmtValue.Seq
              (native_pack_seq T
                (xs.take (xs.length - ys.length) ++ ys ++ [])) =
            SmtValue.Seq (native_pack_seq T xs)
          rw [List.append_nil, ← hList]
    have hEqRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt tc))
          (__smtx_model_eval M (__eo_to_smt rhsT)) := by
      unfold RuleProofs.smt_value_rel
      rw [htcEval, hRhsEval]
      exact smt_seq_rel_pack_unpack T st hstElem
    have hEqTrue : eo_interprets M (mkEq tc rhsT) true :=
      RuleProofs.eo_interprets_eq_of_rel M tc rhsT hEqTBool hEqRel
    have hDiffPos : 0 < xs.length - ys.length := by
      omega
    have hSplitPos : 0 < (xs.take (xs.length - ys.length)).length := by
      rw [List.length_take]
      rw [Nat.min_eq_left (Nat.sub_le _ _)]
      exact hDiffPos
    have hTailTrue :
        eo_interprets M
          (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
            (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
          true :=
      concat_split_nonempty_tail M split T (xs.take (xs.length - ys.length))
        hSplitTy hSplitEval hSplitPos
    have hOrTrue :
        eo_interprets M
          (mkOr (mkEq tc rhsT)
            (mkOr (mkEq sc rhsS) (Term.Boolean false))) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_left_intro M hM (mkEq tc rhsT)
          (mkOr (mkEq sc rhsS) (Term.Boolean false)) hEqTrue hOrRightBool
    simpa [concatSplitTrueFormula, split, nilSplit, rhsT, rhsS, mkAnd,
      mkOr] using
      RuleProofs.eo_interprets_and_intro M
        (mkOr (mkEq tc rhsT) (mkOr (mkEq sc rhsS) (Term.Boolean false)))
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        hOrTrue hTailTrue
  · have hltOrig :
        (native_unpack_seq st).length < (native_unpack_seq ss).length := by
      omega
    have hlt : xs.length < ys.length := by
      simpa [xs, ys] using hltOrig
    have hleRight : xs.length <= ys.length := Nat.le_of_lt hlt
    have hAppendYX :
        native_unpack_seq ssPrefix ++ ys =
          native_unpack_seq stPrefix ++ xs := by
      simpa [xs, ys] using hAppend.symm
    have hList : ys = ys.take (ys.length - xs.length) ++ xs :=
      concat_split_suffix_eq_take_append_of_append_eq_of_le
        (native_unpack_seq ssPrefix) ys (native_unpack_seq stPrefix) xs
        hAppendYX hleRight
    have hSplitEval :
        __smtx_model_eval M (__eo_to_smt split) =
          SmtValue.Seq (native_pack_seq T (ys.take (ys.length - xs.length))) := by
      simpa [split, xs, ys] using
        eval_concatSplitTerm_true_right M hM tc sc T htcTy hscTy st ss
          htcEval hscEval hltOrig
    have hRhsEval :
        __smtx_model_eval M (__eo_to_smt rhsS) =
          SmtValue.Seq (native_pack_seq T ys) := by
      have hNested := eval_mkConcat_right_nested M split tc nilSplit T
        (native_pack_seq T (ys.take (ys.length - xs.length))) st
        (SmtSeq.empty T) hSplitEval htcEval hNilSplitEval
        (elem_typeof_pack_seq T (ys.take (ys.length - xs.length)))
      calc
        __smtx_model_eval M (__eo_to_smt rhsS) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq
                    (native_pack_seq T (ys.take (ys.length - xs.length))) ++
                  native_unpack_seq st ++ native_unpack_seq (SmtSeq.empty T))) := by
          simpa only [rhsS] using hNested
        _ = SmtValue.Seq (native_pack_seq T ys) := by
          rw [_root_.native_unpack_pack_seq]
          change
            SmtValue.Seq
              (native_pack_seq T
                (ys.take (ys.length - xs.length) ++ xs ++ [])) =
            SmtValue.Seq (native_pack_seq T ys)
          rw [List.append_nil, ← hList]
    have hEqRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sc))
          (__smtx_model_eval M (__eo_to_smt rhsS)) := by
      unfold RuleProofs.smt_value_rel
      rw [hscEval, hRhsEval]
      exact smt_seq_rel_pack_unpack T ss hssElem
    have hEqTrue : eo_interprets M (mkEq sc rhsS) true :=
      RuleProofs.eo_interprets_eq_of_rel M sc rhsS hEqSBool hEqRel
    have hDiffPos : 0 < ys.length - xs.length := by
      omega
    have hSplitPos : 0 < (ys.take (ys.length - xs.length)).length := by
      rw [List.length_take]
      rw [Nat.min_eq_left (Nat.sub_le _ _)]
      exact hDiffPos
    have hTailTrue :
        eo_interprets M
          (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
            (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
          true :=
      concat_split_nonempty_tail M split T (ys.take (ys.length - xs.length))
        hSplitTy hSplitEval hSplitPos
    have hOrRightTrue :
        eo_interprets M (mkOr (mkEq sc rhsS) (Term.Boolean false)) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_left_intro M hM (mkEq sc rhsS)
          (Term.Boolean false) hEqTrue RuleProofs.eo_has_bool_type_false
    have hOrTrue :
        eo_interprets M
          (mkOr (mkEq tc rhsT)
            (mkOr (mkEq sc rhsS) (Term.Boolean false))) true := by
      simpa [mkOr] using
        RuleProofs.eo_interprets_or_right_intro M hM (mkEq tc rhsT)
          (mkOr (mkEq sc rhsS) (Term.Boolean false)) hEqTBool
          hOrRightTrue
    simpa [concatSplitTrueFormula, split, nilSplit, rhsT, rhsS, mkAnd,
      mkOr] using
      RuleProofs.eo_interprets_and_intro M
        (mkOr (mkEq tc rhsT) (mkOr (mkEq sc rhsS) (Term.Boolean false)))
        (mkAnd (mkNot (mkEq split (__seq_empty (__eo_typeof split))))
          (mkAnd (mkGt (mkStrLen split) (Term.Numeral 0)) (Term.Boolean true)))
        hOrTrue hTailTrue

private theorem step_concat_split_core
    (M : SmtModel) (hM : model_wf M)
    (rev t s tc sc : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq t s))
    (hLenNeBool :
      RuleProofs.eo_has_bool_type
        (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))
    (hProg :
      __eo_prog_concat_split rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc)))) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_split rev (Proof.pf (mkEq t s))
            (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))) =
        Term.Bool) :
    StepRuleProperties M [mkEq t s, mkNot (mkEq (mkStrLen tc) (mkStrLen sc))]
      (__eo_prog_concat_split rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))))) := by
  rcases eo_prog_concat_split_eq_of_ne_stuck rev t s tc sc hProg with
    ⟨hProgEq, _, _⟩
  rcases concat_split_head_types_same_of_prog rev t s tc sc hPremBool
      hLenNeBool hProg with
    ⟨T, htcTy, hscTy⟩
  have htcNe : tc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation tc
      (by
        unfold RuleProofs.eo_has_smt_translation
        rw [htcTy]
        exact seq_ne_none T)
  rcases concatSplit_rev_cases_of_prog_ne_stuck rev t s tc sc hProg htcNe
    with hRev | hRev
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hLenNe :
          eo_interprets M (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) true :=
        hPremisesTrue (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) (by simp)
      rcases concat_split_true_context M hM t s tc sc hPremBool hLenNeBool
          hProg hST with
        ⟨T, tPrefix, sPrefix, htcTy', hscTy', htPrefixTy, hsPrefixTy,
          hConcatEq⟩
      rw [hProgEq]
      rw [concatSplitFormula_true_eq_plain tc sc T htcTy' hscTy']
      exact facts_concat_split_true_formula M hM tc sc tPrefix sPrefix T
        htcTy' hscTy' htPrefixTy hsPrefixTy hConcatEq hLenNe
    · rw [hProgEq]
      rw [concatSplitFormula_true_eq_plain tc sc T htcTy hscTy]
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatSplitTrueFormula_has_bool_type tc sc T htcTy hscTy)
  · subst rev
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      have hST : eo_interprets M (mkEq t s) true :=
        hPremisesTrue (mkEq t s) (by simp)
      have hLenNe :
          eo_interprets M (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) true :=
        hPremisesTrue (mkNot (mkEq (mkStrLen tc) (mkStrLen sc))) (by simp)
      rcases concat_split_false_context M hM t s tc sc hPremBool hLenNeBool
          hProg hST with
        ⟨T, tTail, sTail, htcTy', hscTy', htTailTy, hsTailTy, hConcatEq⟩
      rw [hProgEq]
      rw [concatSplitFormula_false_eq_plain tc sc T htcTy' hscTy']
      exact facts_concat_split_false_formula M hM tc sc tTail sTail T
        htcTy' hscTy' htTailTy hsTailTy hConcatEq hLenNe
    · rw [hProgEq]
      rw [concatSplitFormula_false_eq_plain tc sc T htcTy hscTy]
      exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (concatSplitFalseFormula_has_bool_type tc sc T htcTy hscTy)

public theorem cmd_step_concat_split_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_split args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_split args premises ≠
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        have hArgs : RuleProofs.eo_has_smt_translation a1 ∧
                            True := by
                          simpa [cmdTranslationOk, cArgListTranslationOk]
                            using hCmdTrans
                        exact hArgs.1
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_split a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_split a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_split_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, lhs1, rhs1, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkNot (mkEq (mkStrLen lhs1) (mkStrLen rhs1)) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hLenNeBool :
                          RuleProofs.eo_has_bool_type
                            (mkNot (mkEq (mkStrLen lhs1) (mkStrLen rhs1))) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_split a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkNot
                                  (mkEq (mkStrLen lhs1) (mkStrLen rhs1)))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_split a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkNot
                                    (mkEq (mkStrLen lhs1)
                                      (mkStrLen rhs1))))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_split a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_split a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_split_core M hM a1 lhs rhs lhs1 rhs1
                        hA1Trans hPremEqBool hLenNeBool hProgRule
                        hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
