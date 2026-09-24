module

public import Cpc.Proofs.RuleSupport.ArithPolyNormSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Init.Data.Repr

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem native_qlt_false_nonneg {q : native_Rat} :
    native_qlt q (native_mk_rational 0 1) = false ->
  0 ≤ q := by
  intro h
  unfold native_qlt at h
  rw [native_mk_rational_zero] at h
  exact Rat.not_lt.mp (of_decide_eq_false h)

private theorem arith_poly_norm_atom_denote_real_str_len_nonneg_of_rational
    (M : SmtModel) (s : Term) {q : native_Rat} :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.UOp UserOp.str_len) s) =
      SmtValue.Rational q ->
  0 ≤ q := by
  intro h
  unfold arith_poly_norm_atom_denote_real at h
  change
    __smtx_to_real_coerce
        (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s))) =
      SmtValue.Rational q at h
  simp [__smtx_model_eval] at h
  cases hEval : __smtx_model_eval M (__eo_to_smt s) <;>
    simp [hEval, __smtx_model_eval_str_len, __smtx_to_real_coerce] at h
  case Seq x =>
    rw [← h]
    dsimp [native_to_real, native_mk_rational, native_seq_len]
    rw [rat_div_one_intCast]
    exact_mod_cast Int.natCast_nonneg (native_unpack_seq x).length

private theorem str_arith_entail_simple_rec_mon_denote_nonneg
    (M : SmtModel) (tail : Term)
    (hTailNonneg :
      ∀ q : native_Rat,
        __str_arith_entail_simple_rec tail = Term.Boolean true ->
        arith_poly_denote_real M tail = SmtValue.Rational q ->
        0 ≤ q) :
    (vars : Term) -> (c qm : native_Rat) ->
      __str_arith_entail_simple_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
              (Term.Rational c))) tail) = Term.Boolean true ->
      arith_mon_denote_real M
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
            (Term.Rational c)) = SmtValue.Rational qm ->
      0 ≤ qm ∧ __str_arith_entail_simple_rec tail = Term.Boolean true
  | vars, c, qm, hSimple, hDen => by
      cases vars with
      | __eo_List_nil =>
          have hParts :
              native_qlt c (native_mk_rational 0 1) = false ∧
                __str_arith_entail_simple_rec tail = Term.Boolean true := by
            cases hNeg : native_qlt c (native_mk_rational 0 1) <;>
              simp [__str_arith_entail_simple_rec, __eo_is_neg, __eo_ite, native_ite,
                native_teq, hNeg] at hSimple ⊢
            exact hSimple
          simp [arith_mon_denote_real, arith_mvar_denote_real, __smtx_model_eval_mult,
            native_qmult, native_mk_rational_one, Rat.mul_one] at hDen
          subst qm
          exact ⟨native_qlt_false_nonneg hParts.1, hParts.2⟩
      | Apply f rest =>
          cases f with
          | Apply g a =>
              cases g with
              | __eo_List_cons =>
                  cases a with
                  | Apply fArg s =>
                      cases fArg with
                      | UOp op =>
                          cases op <;> simp [__str_arith_entail_simple_rec] at hSimple
                          case str_len =>
                            cases hAtom :
                                arith_poly_norm_atom_denote_real M
                                  (Term.Apply (Term.UOp UserOp.str_len) s) <;>
                              cases hRest : arith_mvar_denote_real M rest <;>
                              simp [arith_mon_denote_real, arith_mvar_denote_real, hAtom,
                                hRest, __smtx_model_eval_mult, native_qmult] at hDen
                            case Rational.Rational qa qr =>
                              have hRestMon :
                                  arith_mon_denote_real M
                                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon)
                                        rest) (Term.Rational c)) =
                                    SmtValue.Rational (native_qmult c qr) := by
                                simp [arith_mon_denote_real, hRest, __smtx_model_eval_mult,
                                  native_qmult]
                              have hRec :=
                                str_arith_entail_simple_rec_mon_denote_nonneg M tail
                                  hTailNonneg rest c (native_qmult c qr) hSimple hRestMon
                              have hAtomNonneg :
                                  0 ≤ qa :=
                                arith_poly_norm_atom_denote_real_str_len_nonneg_of_rational M s hAtom
                              have hProdRaw : 0 ≤ c * (qa * qr) := by
                                have hMul : 0 ≤ qa * (c * qr) :=
                                  Rat.mul_nonneg hAtomNonneg hRec.1
                                rw [show c * (qa * qr) = qa * (c * qr) by
                                  rw [← Rat.mul_assoc, Rat.mul_comm c qa, Rat.mul_assoc]]
                                exact hMul
                              have hProd : 0 ≤ qm := by
                                rw [← hDen]
                                exact hProdRaw
                              exact ⟨hProd, hRec.2⟩
                      | _ =>
                          simp [__str_arith_entail_simple_rec] at hSimple
                  | _ =>
                      simp [__str_arith_entail_simple_rec] at hSimple
              | _ =>
                  simp [__str_arith_entail_simple_rec] at hSimple
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | _ =>
          simp [__str_arith_entail_simple_rec] at hSimple
termination_by vars c qm => sizeOf vars

private theorem str_arith_entail_simple_rec_denote_nonneg
    (M : SmtModel) :
    (p : Term) -> (q : native_Rat) ->
      __str_arith_entail_simple_rec p = Term.Boolean true ->
      arith_poly_denote_real M p = SmtValue.Rational q ->
      0 ≤ q
  | p, q, hSimple, hDen => by
      cases p with
      | UOp op =>
          cases op with
          | _at__at_poly_zero =>
              simp [arith_poly_denote_real] at hDen
              subst q
              simp [native_mk_rational_zero]
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | Apply f tail =>
          cases f with
          | Apply g mon =>
              cases g with
              | UOp op =>
                  cases op with
                  | _at__at_poly =>
                      cases mon with
                      | Apply monF coeff =>
                          cases monF with
                          | Apply monHead vars =>
                              cases monHead with
                              | UOp monOp =>
                                  cases monOp with
                                  | _at__at_mon =>
                                      cases coeff with
                                      | Rational c =>
                                          cases hMon :
                                              arith_mon_denote_real M
                                                (Term.Apply
                                                  (Term.Apply
                                                    (Term.UOp UserOp._at__at_mon) vars)
                                                  (Term.Rational c)) <;>
                                            cases hTail : arith_poly_denote_real M tail <;>
                                            simp [arith_poly_denote_real, hMon, hTail,
                                              __smtx_model_eval_plus, native_qplus] at hDen
                                          case Rational.Rational qm qp =>
                                            have hMonTail :=
                                              str_arith_entail_simple_rec_mon_denote_nonneg
                                                M tail
                                                (str_arith_entail_simple_rec_denote_nonneg
                                                  M tail)
                                                vars c qm hSimple hMon
                                            have hTailNonneg :=
                                              str_arith_entail_simple_rec_denote_nonneg M
                                                tail qp hMonTail.2 hTail
                                            exact by
                                              rw [← hDen]
                                              exact Rat.add_nonneg hMonTail.1 hTailNonneg
                                      | _ =>
                                          simp [arith_poly_denote_real, arith_mon_denote_real,
                                            __smtx_model_eval_plus] at hDen
                                  | _ =>
                                      simp [arith_poly_denote_real, arith_mon_denote_real,
                                        __smtx_model_eval_plus] at hDen
                              | _ =>
                                  simp [arith_poly_denote_real, arith_mon_denote_real,
                                    __smtx_model_eval_plus] at hDen
                          | _ =>
                              simp [arith_poly_denote_real, arith_mon_denote_real,
                                __smtx_model_eval_plus] at hDen
                      | _ =>
                          simp [arith_poly_denote_real, arith_mon_denote_real,
                            __smtx_model_eval_plus] at hDen
                  | _ =>
                      simp [__str_arith_entail_simple_rec] at hSimple
              | _ =>
                  simp [__str_arith_entail_simple_rec] at hSimple
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | _ =>
          simp [__str_arith_entail_simple_rec] at hSimple
termination_by p q => sizeOf p

private theorem geq_left_int_type_of_has_bool_type
    (n : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) ->
  __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) =
        SmtType.Bool := by
    exact hTy
  have hNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) hNN with
    hInt | hReal
  · exact hInt.1
  · have hZeroInt :
        __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
      rw [show __eo_to_smt (Term.Numeral 0) = SmtTerm.Numeral 0 by rfl]
      rw [__smtx_typeof.eq_2]
    rw [hZeroInt] at hReal
    cases hReal.2

private theorem geq_zero_eval_true_of_int_denote_nonneg
    (M : SmtModel) (hM : model_wf M)
    (n : Term) (q : native_Rat) :
  __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
  arith_poly_norm_atom_denote_real M n = SmtValue.Rational q ->
  0 ≤ q ->
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) =
    SmtValue.Boolean true := by
  intro hTy hDen hq
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        __smtx_typeof (__eo_to_smt n) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (by simp [term_has_non_none_type, hTy])
  rcases int_value_canonical (by simpa [hTy] using hEvalTy) with ⟨z, hEval⟩
  have hDenEq : native_to_real z = q := by
    have h :
        SmtValue.Rational (native_to_real z) = SmtValue.Rational q := by
      simpa [arith_poly_norm_atom_denote_real, hEval, __smtx_to_real_coerce] using hDen
    simpa using h
  have hzNonneg : (0 : Int) ≤ z := by
    have hq' : (0 : Rat) ≤ native_to_real z := by
      simpa [hDenEq] using hq
    dsimp [native_to_real, native_mk_rational] at hq'
    rw [rat_div_one_intCast z] at hq'
    exact_mod_cast hq'
  rw [show
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) =
        SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0) by rfl]
  rw [__smtx_model_eval.eq_20, hEval]
  have hZle : native_zleq 0 z = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hzNonneg
  have hZeroEval :
      __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
    rw [__smtx_model_eval.eq_2]
  rw [hZeroEval]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hZle]

private theorem geq_eval_true_of_diff_denote_nonneg
    (M : SmtModel) (hM : model_wf M)
    (n m : Term) (q : native_Rat) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) ->
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m) =
      SmtValue.Rational q ->
  0 ≤ q ->
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) =
    SmtValue.Boolean true := by
  intro hGeqBool hDiffDen hq
  have hGeqTy :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Bool := by
    exact hGeqBool
  have hGeqNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hGeqTy]
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hGeqNN with
    hInt | hReal
  · have hEvalNTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
          __smtx_typeof (__eo_to_smt n) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simp [term_has_non_none_type, hInt.1])
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical (by simpa [hInt.1] using hEvalNTy) with ⟨zn, hEvalN⟩
    rcases int_value_canonical (by simpa [hInt.2] using hEvalMTy) with ⟨zm, hEvalM⟩
    have hDiffQ :
        native_to_real (native_zplus zn (native_zneg zm)) = q := by
      have h :
          SmtValue.Rational (native_to_real (native_zplus zn (native_zneg zm))) =
            SmtValue.Rational q := by
        have hDen := hDiffDen
        change
          __smtx_to_real_coerce
              (__smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m))) =
            SmtValue.Rational q at hDen
        rw [__smtx_model_eval.eq_15, hEvalN, hEvalM] at hDen
        simpa [__smtx_to_real_coerce, __smtx_model_eval__, native_to_real_sub] using hDen
      simpa using h
    have hSubNonneg : (0 : Int) ≤ native_zplus zn (native_zneg zm) := by
      have hRat : (0 : Rat) ≤ native_to_real (native_zplus zn (native_zneg zm)) := by
        simpa [hDiffQ] using hq
      dsimp [native_to_real, native_mk_rational] at hRat
      rw [rat_div_one_intCast] at hRat
      exact_mod_cast hRat
    have hLe : zm ≤ zn := by
      have hSubNonneg' : (0 : Int) ≤ zn - zm := by
        change (0 : Int) ≤ zn + -zm
        simpa [native_zplus, native_zneg] using hSubNonneg
      exact Int.sub_nonneg.mp hSubNonneg'
    have hZle : native_zleq zm zn = true := by
      simpa [native_zleq, SmtEval.native_zleq] using hLe
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
          SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl]
    rw [__smtx_model_eval.eq_20, hEvalN, hEvalM]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hZle]
  · have hEvalNTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
          __smtx_typeof (__eo_to_smt n) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simp [term_has_non_none_type, hReal.1])
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical (by simpa [hReal.1] using hEvalNTy) with ⟨qn, hEvalN⟩
    rcases real_value_canonical (by simpa [hReal.2] using hEvalMTy) with ⟨qm, hEvalM⟩
    have hDiffQ :
        native_qplus qn (native_qneg qm) = q := by
      have h :
          SmtValue.Rational (native_qplus qn (native_qneg qm)) =
            SmtValue.Rational q := by
        have hDen := hDiffDen
        change
          __smtx_to_real_coerce
              (__smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m))) =
            SmtValue.Rational q at hDen
        rw [__smtx_model_eval.eq_15, hEvalN, hEvalM] at hDen
        simpa [__smtx_to_real_coerce, __smtx_model_eval__] using hDen
      simpa using h
    have hLe : qm ≤ qn := by
      have hSub : (0 : Rat) ≤ native_qplus qn (native_qneg qm) := by
        simpa [hDiffQ] using hq
      have hSub' : (0 : Rat) ≤ qn + -qm := by
        simpa [native_qplus, native_qneg] using hSub
      grind
    have hQle : native_qleq qm qn = true := by
      simpa [native_qleq] using hLe
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
          SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl]
    rw [__smtx_model_eval.eq_20, hEvalN, hEvalM]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hQle]

theorem arith_string_pred_simple_geq_true
    (M : SmtModel) (hM : model_wf M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) = Term.Boolean true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) true := by
  intro hGeqBool hSimple
  let diff := Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m
  have hGeqTy :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Bool := by
    exact hGeqBool
  have hGeqNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hGeqTy]
    simp
  have hDiffTy :
      __smtx_typeof (__eo_to_smt diff) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt diff) = SmtType.Real := by
    rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
        (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hGeqNN with
      hInt | hReal
    · left
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hInt.1, hInt.2]
    · right
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm diff) =
        arith_poly_norm_atom_denote_real M diff :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM diff hDiffTy
  rcases arith_poly_norm_atom_denote_real_rational_of_smt_arith_type
      M hM diff hDiffTy with
    ⟨q, hAtomDenote⟩
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm diff) =
        SmtValue.Rational q := by
    rw [hDenote, hAtomDenote]
  have hSimpleRec :
      __str_arith_entail_simple_rec (__get_arith_poly_norm diff) =
        Term.Boolean true := by
    simpa [diff, __str_arith_entail_simple_pred] using hSimple
  have hqNonneg : 0 ≤ q :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm diff) q hSimpleRec hPolyDenote
  have hGeqEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) =
        SmtValue.Boolean true :=
    geq_eval_true_of_diff_denote_nonneg M hM n m q hGeqBool hAtomDenote hqNonneg
  exact RuleProofs.eo_interprets_of_bool_eval M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) true hGeqBool hGeqEval

private theorem geq_has_bool_type_of_non_none (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) ≠
      SmtType.None ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) := by
  intro hNN
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) = SmtType.Bool
  have hTerm : term_has_non_none_type (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hTerm with
    hInt | hReal
  · rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem int_eval_of_int_type
    (M : SmtModel) (hM : model_wf M) (t : Term) :
  __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
  ∃ z : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem arith_poly_norm_atom_denote_real_eq_of_int_eval
    (M : SmtModel) (t : Term) (z : native_Int) :
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z ->
  arith_poly_norm_atom_denote_real M t = SmtValue.Rational (native_to_real z) := by
  intro hEval
  simp [arith_poly_norm_atom_denote_real, hEval, __smtx_to_real_coerce]

private theorem native_to_real_le_iff (a b : native_Int) :
    native_to_real a ≤ native_to_real b ↔ a ≤ b := by
  dsimp [native_to_real, native_mk_rational]
  rw [rat_div_one_intCast a, rat_div_one_intCast b]
  exact_mod_cast Iff.rfl

private theorem native_seq_indexof_rec_ge_neg_one
    (xs pat : List SmtValue) (i fuel : Nat) :
    (-1 : Int) ≤ native_seq_indexof_rec xs pat i fuel := by
  induction fuel generalizing xs i with
  | zero =>
      simp [native_seq_indexof_rec]
  | succ fuel ih =>
      unfold native_seq_indexof_rec
      split
      · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg i)
      · cases xs with
        | nil => simp
        | cons _ xs => exact ih xs (i + 1)

private theorem native_seq_indexof_ge_neg_one
    (xs pat : List SmtValue) (i : native_Int) :
    (-1 : Int) ≤ native_seq_indexof xs pat i := by
  rw [native_seq_indexof_eq_rec]
  split
  · simp
  · dsimp
    split
    · exact native_seq_indexof_rec_ge_neg_one _ _ _ _
    · simp

private theorem native_str_to_int_ge_neg_one
    (s : native_String) :
    (-1 : Int) ≤ native_str_to_int s := by
  unfold native_str_to_int
  cases s with
  | nil =>
      simp
  | cons c cs =>
      by_cases hDigits : (c :: cs).all impl_native_char_is_digit = true
      · simp [hDigits]
      · simp [hDigits]

private theorem int_le_of_simple_geq_true
    (M : SmtModel) (hM : model_wf M)
    (n m : Term) (zn zm : native_Int) :
  __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
  __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
  __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
  __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
    Term.Boolean true ->
  zm ≤ zn := by
  intro hNInt hMInt hNEval hMEval hSimple
  let geqTerm := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m
  have hGeqBool : RuleProofs.eo_has_bool_type geqTerm := by
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
      SmtType.Bool
    rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hNInt, hMInt]
  have hTrue : eo_interprets M geqTerm true := by
    simpa [geqTerm] using
      arith_string_pred_simple_geq_true M hM n m hGeqBool hSimple
  have hEval :
      __smtx_model_eval M (__eo_to_smt geqTerm) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqTerm true).mp hTrue with
    | intro_true _ hEval => exact hEval
  rw [show __eo_to_smt geqTerm =
        SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_20, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_geq, __smtx_model_eval_leq, native_zleq,
    SmtEval.native_zleq] using hEval

private theorem native_seq_indexof_le_len_sub_pat_of_pat_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    pat.length ≤ xs.length ->
    native_seq_indexof xs pat i ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
  intro hPatLe
  rw [native_seq_indexof_eq_rec]
  split
  · have hNonneg :
        (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
      exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
    exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          have hNonneg :
              (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
            exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          have hjle : j ≤ xs.length - (Int.toNat i + pat.length) := by
            omega
          have hNat :
              Int.toNat i + j ≤ xs.length - pat.length := by
            omega
          calc
            Int.ofNat (Int.toNat i + j) ≤ Int.ofNat (xs.length - pat.length) :=
              Int.ofNat_le.mpr hNat
            _ = Int.ofNat xs.length - Int.ofNat pat.length :=
              Int.ofNat_sub hPatLe
    · have hNonneg :
          (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
        exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
      exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg

private theorem int_eval_eq_of_term_eq
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    n = m ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    zn = zm := by
  intro hEq hNEval hMEval
  subst m
  have h : SmtValue.Numeral zn = SmtValue.Numeral zm := by
    rw [← hNEval, ← hMEval]
  simpa using h

private theorem plus_int_args_of_int_type (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Int := by
    exact hTy
  have hNN :
      term_has_non_none_type (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
      (typeof_plus_eq (__eo_to_smt n) (__eo_to_smt m)) hNN with hInt | hReal
  · exact hInt
  · have hRet :
        __smtx_typeof
            (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) =
          SmtType.Real := by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m) =
          SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m) by rfl] at hTy
    rw [hTy] at hRet
    cases hRet

private theorem mult_int_args_of_int_type (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Int := by
    exact hTy
  have hNN :
      term_has_non_none_type (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt n) (__eo_to_smt m)) hNN with hInt | hReal
  · exact hInt
  · have hRet :
        __smtx_typeof
            (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) =
          SmtType.Real := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m) =
          SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m) by rfl] at hTy
    rw [hTy] at hRet
    cases hRet

private theorem plus_int_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (n m : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtValue.Numeral z ->
    ∃ zn zm,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ∧
      z = zn + zm := by
  intro hTy hEval
  rcases plus_int_args_of_int_type n m hTy with ⟨hNInt, hMInt⟩
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
  refine ⟨zn, zm, hNInt, hMInt, hNEval, hMEval, ?_⟩
  rw [show
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m) =
        SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_14, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_plus, native_zplus] using hEval.symm

private theorem mult_int_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (n m : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtValue.Numeral z ->
    ∃ zn zm,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ∧
      z = zn * zm := by
  intro hTy hEval
  rcases mult_int_args_of_int_type n m hTy with ⟨hNInt, hMInt⟩
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
  refine ⟨zn, zm, hNInt, hMInt, hNEval, hMEval, ?_⟩
  rw [show
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m) =
        SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_16, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_mult, native_zmult] using hEval.symm

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_wf M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem str_len_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (z : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral z ->
    ∃ T ss,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      z = Int.ofNat (native_unpack_seq ss).length := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int := by
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt s)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt s)) hNN with ⟨T, hSTy⟩
  rcases seq_eval_of_seq_type M hM s T hSTy with ⟨ss, hSEval⟩
  refine ⟨T, ss, hSTy, hSEval, ?_⟩
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s) =
        SmtTerm.str_len (__eo_to_smt s) by rfl] at hEval
  rw [smtx_eval_str_len_term_eq, hSEval] at hEval
  simpa [__smtx_model_eval_str_len, native_seq_len] using hEval.symm

private theorem native_unpack_pack_string_len
    (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

private theorem str_to_int_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (s : Term) (z : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtValue.Numeral z ->
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      z = native_str_to_int (native_unpack_string ss) := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt s)) = SmtType.Int := by
    exact hTy
  have hNN : term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt s)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  have hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq (__eo_to_smt s)) hNN
  rcases seq_eval_of_seq_type M hM s SmtType.Char hSTy with ⟨ss, hSEval⟩
  refine ⟨ss, hSEval, ?_⟩
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s) =
        SmtTerm.str_to_int (__eo_to_smt s) by rfl] at hEval
  rw [__smtx_model_eval.eq_96, hSEval] at hEval
  simpa [__smtx_model_eval_str_to_int] using hEval.symm

private theorem str_indexof_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (s t n : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n)) =
      SmtValue.Numeral z ->
    ∃ T ss tt zn,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      z = native_seq_indexof (native_unpack_seq ss) (native_unpack_seq tt) zn := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n)) =
        SmtType.Int := by
    exact hTy
  have hNN :
      term_has_non_none_type
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases str_indexof_args_of_non_none hNN with ⟨T, hSTy, hTTy, hNTy⟩
  rcases seq_eval_of_seq_type M hM s T hSTy with ⟨ss, hSEval⟩
  rcases seq_eval_of_seq_type M hM t T hTTy with ⟨tt, hTEval⟩
  rcases int_eval_of_int_type M hM n hNTy with ⟨zn, hNEval⟩
  refine ⟨T, ss, tt, zn, hSTy, hTTy, hNTy, hSEval, hTEval, hNEval, ?_⟩
  rw [show
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n) =
        SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n) by rfl] at hEval
  rw [__smtx_model_eval.eq_85, hSEval, hTEval, hNEval] at hEval
  simpa [__smtx_model_eval_str_indexof] using hEval.symm

private theorem str_substr_len_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (s n1 n2 : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))) =
      SmtValue.Numeral z ->
    ∃ T ss z1 z2,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt n1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt n2) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt n1) = SmtValue.Numeral z1 ∧
      __smtx_model_eval M (__eo_to_smt n2) = SmtValue.Numeral z2 ∧
      z = Int.ofNat (native_seq_extract (native_unpack_seq ss) z1 z2).length := by
  intro hTy hEval
  let sub :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2
  rcases str_len_eval_decomp M hM sub z (by simpa [sub] using hTy)
      (by simpa [sub] using hEval) with ⟨T, subSeq, hSubTy, hSubEval, hzLen⟩
  have hSubTy' :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2)) =
        SmtType.Seq T := by
    exact hSubTy
  have hSubNN :
      term_has_non_none_type
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2)) := by
    unfold term_has_non_none_type
    rw [hSubTy']
    simp
  rcases str_substr_args_of_non_none hSubNN with ⟨T', hSTy, hN1Ty, hN2Ty⟩
  rcases seq_eval_of_seq_type M hM s T' hSTy with ⟨ss, hSEval⟩
  rcases int_eval_of_int_type M hM n1 hN1Ty with ⟨z1, hN1Eval⟩
  rcases int_eval_of_int_type M hM n2 hN2Ty with ⟨z2, hN2Eval⟩
  have hSubEval' :
      native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) z1 z2) =
        subSeq := by
    rw [show __eo_to_smt sub =
          SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2) by rfl]
        at hSubEval
    rw [__smtx_model_eval.eq_82, hSEval, hN1Eval, hN2Eval] at hSubEval
    simpa [__smtx_model_eval_str_substr] using hSubEval
  have hLenEq :
      (native_unpack_seq subSeq).length =
        (native_seq_extract (native_unpack_seq ss) z1 z2).length := by
    rw [← hSubEval']
    simp [Smtm.native_unpack_pack_seq]
  refine ⟨T', ss, z1, z2, hSTy, hN1Ty, hN2Ty, hSEval, hN1Eval, hN2Eval, ?_⟩
  rw [hzLen, hLenEq]

private theorem str_replace_len_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (s t r : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral z ->
    ∃ T ss tt rr,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.Seq T ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.Seq rr ∧
      z = Int.ofNat
        (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
          (native_unpack_seq rr)).length := by
  intro hTy hEval
  let rep :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r
  rcases str_len_eval_decomp M hM rep z (by simpa [rep] using hTy)
      (by simpa [rep] using hEval) with ⟨T, repSeq, hRepTy, hRepEval, hzLen⟩
  have hRepTy' :
      __smtx_typeof
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r)) =
        SmtType.Seq T := by
    exact hRepTy
  have hRepNN :
      term_has_non_none_type
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    rw [hRepTy']
    simp
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
      (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r))
      hRepNN with ⟨T', hSTy, hTTy, hRTy⟩
  rcases seq_eval_of_seq_type M hM s T' hSTy with ⟨ss, hSEval⟩
  rcases seq_eval_of_seq_type M hM t T' hTTy with ⟨tt, hTEval⟩
  rcases seq_eval_of_seq_type M hM r T' hRTy with ⟨rr, hREval⟩
  have hRepEval' :
      native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
            (native_unpack_seq rr)) =
        repSeq := by
    rw [show __eo_to_smt rep =
          SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r) by rfl]
        at hRepEval
    rw [__smtx_model_eval.eq_84, hSEval, hTEval, hREval] at hRepEval
    simpa [__smtx_model_eval_str_replace] using hRepEval
  have hLenEq :
      (native_unpack_seq repSeq).length =
        (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
          (native_unpack_seq rr)).length := by
    rw [← hRepEval']
    simp [Smtm.native_unpack_pack_seq]
  refine ⟨T', ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, ?_⟩
  rw [hzLen, hLenEq]

private theorem str_from_int_len_eval_decomp
    (M : SmtModel) (hM : model_wf M)
    (n : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n))) =
      SmtValue.Numeral z ->
    ∃ zn,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      z = Int.ofNat (native_str_from_int zn).length := by
  intro hTy hEval
  let fromInt := Term.Apply (Term.UOp UserOp.str_from_int) n
  rcases str_len_eval_decomp M hM fromInt z (by simpa [fromInt] using hTy)
      (by simpa [fromInt] using hEval) with ⟨T, seq, hFromTy, hFromEval, hzLen⟩
  have hFromTy' :
      __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) = SmtType.Seq T := by
    exact hFromTy
  have hFromNN : term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    rw [hFromTy']
    simp
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (typeof_str_from_int_eq (__eo_to_smt n)) hFromNN
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  have hFromEval' :
      native_pack_string (native_str_from_int zn) = seq := by
    rw [show __eo_to_smt fromInt = SmtTerm.str_from_int (__eo_to_smt n) by rfl]
        at hFromEval
    rw [__smtx_model_eval.eq_97, hNEval] at hFromEval
    simpa [__smtx_model_eval_str_from_int] using hFromEval
  have hLenEq :
      (native_unpack_seq seq).length = (native_str_from_int zn).length := by
    rw [← hFromEval']
    exact native_unpack_pack_string_len (native_str_from_int zn)
  refine ⟨zn, hNInt, hNEval, ?_⟩
  rw [hzLen, hLenEq]

private theorem int_nonneg_of_simple_rec_true
    (M : SmtModel) (hM : model_wf M) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __str_arith_entail_simple_rec (__get_arith_poly_norm n) = Term.Boolean true ->
    0 ≤ zn := by
  intro hTy hEval hSimple
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        arith_poly_norm_atom_denote_real M n :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM n (Or.inl hTy)
  have hAtomDenote :
      arith_poly_norm_atom_denote_real M n = SmtValue.Rational (native_to_real zn) :=
    arith_poly_norm_atom_denote_real_eq_of_int_eval M n zn hEval
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        SmtValue.Rational (native_to_real zn) := by
    rw [hDenote, hAtomDenote]
  have hNonnegRat : (0 : Rat) ≤ native_to_real zn :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm n) (native_to_real zn) hSimple hPolyDenote
  dsimp [native_to_real, native_mk_rational] at hNonnegRat
  rw [rat_div_one_intCast zn] at hNonnegRat
  exact_mod_cast hNonnegRat

private theorem int_pos_of_simple_gt_zero_true
    (M : SmtModel) (hM : model_wf M) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __str_arith_entail_simple_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n) (Term.Numeral 0)) =
      Term.Boolean true ->
    0 < zn := by
  intro hNInt hNEval hSimple
  let oneTerm :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 0))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0))
  have hOneInt : __smtx_typeof (__eo_to_smt oneTerm) = SmtType.Int := by
    change
      __smtx_typeof
        (SmtTerm.plus (SmtTerm.Numeral 0)
          (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) = SmtType.Int
    rw [typeof_plus_eq, typeof_plus_eq]
    simp [__smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt oneTerm) = SmtValue.Numeral 1 := by
    change
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral 0)
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) =
        SmtValue.Numeral 1
    rw [__smtx_model_eval.eq_14, __smtx_model_eval.eq_14]
    simp [__smtx_model_eval.eq_2, __smtx_model_eval_plus, native_zplus]
  have hSimpleGeq :
      __str_arith_entail_simple_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) oneTerm) =
        Term.Boolean true := by
    simpa [oneTerm, __str_arith_entail_simple_pred] using hSimple
  have hOneLe :
      (1 : Int) ≤ zn :=
    int_le_of_simple_geq_true M hM n oneTerm zn 1 hNInt hOneInt hNEval hOneEval
      hSimpleGeq
  exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hOneLe

private theorem numeral_int_eval (M : SmtModel) (z : native_Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral z)) = SmtValue.Numeral z := by
  change __smtx_model_eval M (SmtTerm.Numeral z) = SmtValue.Numeral z
  rw [__smtx_model_eval.eq_2]

private theorem numeral_eval_value_eq (M : SmtModel) {z w : native_Int} :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral z)) = SmtValue.Numeral w ->
    w = z := by
  intro hEval
  have hVal : SmtValue.Numeral w = SmtValue.Numeral z := by
    rw [← hEval]
    exact numeral_int_eval M z
  simpa using hVal

private theorem plus_trailing_zero_int_type (n m : Term) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m) (Term.Numeral 0)))) =
      SmtType.Int := by
  intro hNInt hMInt
  change
    __smtx_typeof
      (SmtTerm.plus (__eo_to_smt n)
        (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))) = SmtType.Int
  rw [typeof_plus_eq, typeof_plus_eq]
  simp [__smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2, hNInt, hMInt]

private theorem plus_trailing_zero_int_eval
    (M : SmtModel) (n m : Term) (zn zm : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m) (Term.Numeral 0)))) =
      SmtValue.Numeral (zn + zm) := by
  intro hNEval hMEval
  change
    __smtx_model_eval M
      (SmtTerm.plus (__eo_to_smt n)
        (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))) =
      SmtValue.Numeral (zn + zm)
  rw [__smtx_model_eval.eq_14, __smtx_model_eval.eq_14, hNEval, hMEval,
    __smtx_model_eval.eq_2]
  simp [__smtx_model_eval_plus, native_zplus]

private theorem neg_int_eval_of_args
    (M : SmtModel) (n m : Term) (zn zm : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtValue.Numeral (zn - zm) := by
  intro hNEval hMEval
  change __smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) =
    SmtValue.Numeral (zn - zm)
  rw [__smtx_model_eval.eq_15, hNEval, hMEval]
  simp [__smtx_model_eval__, native_zplus, native_zneg, Int.sub_eq_add_neg]

private theorem str_len_int_type_of_seq_type (s : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int := by
  intro hSTy
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int
  rw [typeof_str_len_eq]
  simp [__smtx_typeof_seq_op_1_ret, hSTy]

private theorem str_len_int_eval_of_seq_eval
    (M : SmtModel) (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
  intro hSEval
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length)
  rw [smtx_eval_str_len_term_eq, hSEval]
  simp [__smtx_model_eval_str_len, native_seq_len]

private theorem eo_requires_true
    {x y z : Term} :
    __eo_requires x y z = Term.Boolean true ->
    x = y ∧ z = Term.Boolean true := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      exfalso
      simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at h
    · have hReq : __eo_requires x x z = z := by
        simp [__eo_requires, native_teq, hx, native_ite, native_not, SmtEval.native_not]
      rw [hReq] at h
      exact ⟨rfl, h⟩
  · have hReq : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, hxy, native_ite]
    rw [hReq] at h
    cases h

private theorem int_eval_lt_zero_of_eo_is_neg_true
    (M : SmtModel) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __eo_is_neg n = Term.Boolean true ->
    zn < 0 := by
  intro hNInt hNEval hNeg
  cases n <;> simp [__eo_is_neg] at hNeg
  case Numeral z =>
    have hZEval : z = zn := by
      have hVal :
          SmtValue.Numeral z = SmtValue.Numeral zn := by
        rw [← hNEval]
        exact (numeral_int_eval M z).symm
      simpa using hVal
    subst zn
    simpa [native_zlt, SmtEval.native_zlt] using hNeg
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hNInt
    rw [__smtx_typeof.eq_3] at hNInt
    cases hNInt

private theorem int_eval_nonneg_of_eo_is_neg_false
    (M : SmtModel) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __eo_is_neg n = Term.Boolean false ->
    0 <= zn := by
  intro hNInt hNEval hNeg
  cases n <;> simp [__eo_is_neg] at hNeg
  case Numeral z =>
    have hZEval : z = zn := by
      have hVal :
          SmtValue.Numeral z = SmtValue.Numeral zn := by
        rw [← hNEval]
        exact (numeral_int_eval M z).symm
      simpa using hVal
    subst zn
    have hNotLt : ¬ z < 0 := by
      simpa [native_zlt, SmtEval.native_zlt] using hNeg
    exact Int.le_of_not_gt hNotLt
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hNInt
    rw [__smtx_typeof.eq_3] at hNInt
    cases hNInt

private theorem arith_string_eo_ite_true
    {c t e : Term} :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢ <;> exact h

local notation "eo_ite_true" => arith_string_eo_ite_true

private theorem eo_and_true
    {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

private theorem eo_or_true
    {x y : Term} :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_or, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_or] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

private theorem eo_eq_true_eq
    {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    x = y := by
  intro h
  by_cases hxSt : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  by_cases hySt : y = Term.Stuck
  · subst y
    simp [__eo_eq] at h
  have hyx : y = x := by
    simpa [__eo_eq, hxSt, hySt, native_teq] using h
  exact hyx.symm

private theorem str_arith_entail_is_approx_bool_top
    {n m : Term} {b : Bool} :
    __str_arith_entail_is_approx n m (Term.Boolean b) = Term.Boolean true ->
    __eo_eq n m = Term.Boolean true ∨
      __eo_l_1___str_arith_entail_is_approx n m (Term.Boolean b) = Term.Boolean true := by
  intro h
  cases n <;> cases m <;>
    simp [__str_arith_entail_is_approx] at h
  all_goals
    rcases eo_ite_true h with hEq | hRest
    · exact Or.inl hEq.1
    · exact Or.inr hRest.2

private theorem int_eval_le_of_eo_eq_true
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_eq n m = Term.Boolean true ->
    zm <= zn := by
  intro hNEval hMEval hEq
  have hEqTerms := eo_eq_true_eq hEq
  have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
  rw [hZEq]
  exact Int.le_refl zm

private theorem int_eval_ge_of_eo_eq_true
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_eq n m = Term.Boolean true ->
    zn <= zm := by
  intro hNEval hMEval hEq
  have hEqTerms := eo_eq_true_eq hEq
  have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
  rw [hZEq]
  exact Int.le_refl zm

private theorem l1_str_to_int_true
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true) (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases m <;> simp [__eo_l_1___str_arith_entail_is_approx] at h ⊢ <;> exact h

private theorem l1_str_to_int_false
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
        (Term.Boolean false) (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases m <;> simp [__eo_l_1___str_arith_entail_is_approx] at h ⊢ <;> exact h

private theorem l1_str_indexof_true
    (s t n0 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (__eo_ite (__eo_eq m (Term.Apply (Term.UOp UserOp.str_len) s))
          (Term.Boolean false)
          (__eo_ite
            (__eo_eq m
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp.str_len) s))
                (Term.Apply (Term.UOp UserOp.str_len) t)))
            (__eo_and (Term.Boolean false)
              (__str_arith_entail_simple_pred
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.geq)
                    (Term.Apply (Term.UOp UserOp.str_len) s))
                  (Term.Apply (Term.UOp UserOp.str_len) t))))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
      SmtEval.native_not] at h ⊢ <;>
    exact h

private theorem l1_str_indexof_false
    (s t n0 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int))) (Term.Boolean false)
        (__eo_ite (__eo_eq m (Term.Apply (Term.UOp UserOp.str_len) s))
          (Term.Boolean true)
          (__eo_ite
            (__eo_eq m
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp.str_len) s))
                (Term.Apply (Term.UOp UserOp.str_len) t)))
            (__eo_and (Term.Boolean true)
              (__str_arith_entail_simple_pred
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.geq)
                    (Term.Apply (Term.UOp UserOp.str_len) s))
                  (Term.Apply (Term.UOp UserOp.str_len) t))))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
      SmtEval.native_not] at h ⊢ <;>
    exact h

private theorem l1_str_from_int_len_true
    (n1 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite
        (__eo_eq m
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Numeral 0))))
        (__eo_and (__eo_not (Term.Boolean true))
          (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
        (__eo_ite (__eo_eq m n1)
          (__eo_and (__eo_not (Term.Boolean true))
            (__str_arith_entail_simple_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n1) (Term.Numeral 0))))
          (__eo_ite (__eo_eq m (Term.Numeral 1))
            (__eo_and (Term.Boolean true)
              (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_from_int_len_false
    (n1 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite
        (__eo_eq m
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Numeral 0))))
        (__eo_and (__eo_not (Term.Boolean false))
          (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
        (__eo_ite (__eo_eq m n1)
          (__eo_and (__eo_not (Term.Boolean false))
            (__str_arith_entail_simple_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n1) (Term.Numeral 0))))
          (__eo_ite (__eo_eq m (Term.Numeral 1))
            (__eo_and (Term.Boolean false)
              (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_substr_len_true
    (s n1 n2 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean true) =
      Term.Boolean true ->
    (let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let sumN :=
       Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
         (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
     let n1Nonneg := __str_arith_entail_simple_rec (__get_arith_poly_norm n1)
     __eo_ite (__eo_eq m n2)
       (__eo_ite (Term.Boolean true)
         (__eo_and n1Nonneg
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) sumN)))
         (__str_arith_entail_simple_rec (__get_arith_poly_norm n2)))
       (__eo_ite (__eo_eq m lenS) (__eo_not (Term.Boolean true))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1))
           (__eo_ite (Term.Boolean true)
             (__eo_and n1Nonneg
               (__str_arith_entail_simple_pred
                 (Term.Apply (Term.Apply (Term.UOp UserOp.geq) sumN) lenS)))
             (__str_arith_entail_simple_pred
               (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) n1)))
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_substr_len_false
    (s n1 n2 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean false) =
      Term.Boolean true ->
    (let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let sumN :=
       Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
         (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
     let n1Nonneg := __str_arith_entail_simple_rec (__get_arith_poly_norm n1)
     __eo_ite (__eo_eq m n2)
       (__eo_ite (Term.Boolean false)
         (__eo_and n1Nonneg
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) sumN)))
         (__str_arith_entail_simple_rec (__get_arith_poly_norm n2)))
       (__eo_ite (__eo_eq m lenS) (__eo_not (Term.Boolean false))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1))
           (__eo_ite (Term.Boolean false)
             (__eo_and n1Nonneg
               (__str_arith_entail_simple_pred
                 (Term.Apply (Term.Apply (Term.UOp UserOp.geq) sumN) lenS)))
             (__str_arith_entail_simple_pred
               (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) n1)))
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_replace_len_true
    (s t r m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean true) =
      Term.Boolean true ->
    (let lenT := Term.Apply (Term.UOp UserOp.str_len) t
     let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let lenR := Term.Apply (Term.UOp UserOp.str_len) r
     __eo_ite (__eo_eq m lenS)
       (__eo_ite (Term.Boolean true)
         (__eo_or
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenT))
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenS)))
         (__str_arith_entail_simple_pred
           (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenT) lenR)))
       (__eo_ite
         (__eo_eq m
           (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
             (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))))
         (__eo_not (Term.Boolean true))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT))
           (Term.Boolean true)
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_replace_len_false
    (s t r m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean false) =
      Term.Boolean true ->
    (let lenT := Term.Apply (Term.UOp UserOp.str_len) t
     let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let lenR := Term.Apply (Term.UOp UserOp.str_len) r
     __eo_ite (__eo_eq m lenS)
       (__eo_ite (Term.Boolean false)
         (__eo_or
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenT))
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenS)))
         (__str_arith_entail_simple_pred
           (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenT) lenR)))
       (__eo_ite
         (__eo_eq m
           (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
             (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))))
         (__eo_not (Term.Boolean false))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT))
           (Term.Boolean false)
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem native_seq_extract_len_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    (0 : Int) ≤ Int.ofNat (native_seq_extract xs i n).length := by
  exact Int.natCast_nonneg _

private theorem native_seq_extract_len_le_len
    (xs : List SmtValue) (i n : native_Int) :
    Int.ofNat (native_seq_extract xs i n).length <= Int.ofNat xs.length := by
  simp only [native_seq_extract]
  split
  · simp
  · have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          (xs.drop (Int.toNat i)).length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    have hDrop : (xs.drop (Int.toNat i)).length <= xs.length := by
      rw [List.length_drop]
      exact Nat.sub_le _ _
    exact Int.ofNat_le.mpr (Nat.le_trans hTake hDrop)

private theorem native_seq_extract_len_le_arg_of_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    0 <= n -> Int.ofNat (native_seq_extract xs i n).length <= n := by
  intro hn
  simp only [native_seq_extract]
  split
  · simp [hn]
  · rename_i h
    have hProp : ¬ ((i < 0 ∨ n <= 0) ∨ Int.ofNat xs.length <= i) := by
      simpa [Bool.or_eq_true, decide_eq_true_eq] using h
    have hiNonneg : 0 <= i := by
      have hiNot : ¬ i < 0 := by
        intro hi
        exact hProp (Or.inl (Or.inl hi))
      exact Int.le_of_not_gt hiNot
    have hnPos : 0 < n := by
      have hnNot : ¬ n <= 0 := by
        intro hnle
        exact hProp (Or.inl (Or.inr hnle))
      exact Int.lt_of_not_ge hnNot
    have hiLt : i < Int.ofNat xs.length := by
      have hiNot : ¬ Int.ofNat xs.length <= i := by
        intro hle
        exact hProp (Or.inr hle)
      exact Int.lt_of_not_ge hiNot
    have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.toNat (min n (Int.ofNat xs.length - i)) := by
      exact List.length_take_le _ _
    have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by omega
    have hMinNonneg : 0 <= min n (Int.ofNat xs.length - i) := by
      exact (Int.le_min).2 ⟨hn, hDiffNonneg⟩
    have hCast :
        Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) =
          min n (Int.ofNat xs.length - i) := by
      exact Int.toNat_of_nonneg hMinNonneg
    have hLenLe :
        Int.ofNat
            ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) := by
      exact Int.ofNat_le.mpr hTake
    have hMinLe : min n (Int.ofNat xs.length - i) <= n := Int.min_le_left _ _
    omega

private theorem native_seq_extract_len_ge_arg_of_in_range
    (xs : List SmtValue) (i n : native_Int) :
    0 <= i -> 0 <= n -> i + n <= Int.ofNat xs.length ->
    n <= Int.ofNat (native_seq_extract xs i n).length := by
  intro hi hn hle
  simp only [native_seq_extract]
  by_cases hnZero : n = 0
  · subst n
    simp
  · have hnPos : 0 < n := by grind
    have hiLt : i < Int.ofNat xs.length := by grind
    have hCondFalse :
        ¬ (decide (i < 0) || decide (n <= 0) ||
              decide (i >= Int.ofNat xs.length)) = true := by
      simp [Bool.or_eq_true, decide_eq_true_eq]
      grind
    split
    · rename_i h
      exact False.elim (hCondFalse h)
    · have hMin : min n (Int.ofNat xs.length - i) = n := by
        apply Int.min_eq_left
        grind
      have hTakeNat :
          Int.toNat (min n (Int.ofNat xs.length - i)) = Int.toNat n := by
        rw [hMin]
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hi
      have hnCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hn
      have hDropLen :
          (xs.drop (Int.toNat i)).length = xs.length - Int.toNat i :=
        List.length_drop
      have hNLeDrop : Int.toNat n <= (xs.drop (Int.toNat i)).length := by
        rw [hDropLen]
        have hNat : Int.toNat n + Int.toNat i <= xs.length := by
          rw [← Int.ofNat_le]
          rw [Int.natCast_add]
          change
            Int.ofNat (Int.toNat n) + Int.ofNat (Int.toNat i) <=
              Int.ofNat xs.length
          rw [hnCast, hiCast]
          grind
        omega
      rw [hTakeNat, List.length_take, Nat.min_eq_left hNLeDrop]
      rw [hnCast]
      exact Int.le_refl _

private theorem native_seq_extract_len_ge_len_sub_start_of_covers_end
    (xs : List SmtValue) (i n : native_Int) :
    0 <= i -> Int.ofNat xs.length <= i + n ->
    Int.ofNat xs.length - i <= Int.ofNat (native_seq_extract xs i n).length := by
  intro hi hle
  simp only [native_seq_extract]
  by_cases hiEnd : Int.ofNat xs.length <= i
  · split
    · simp
      grind
    · simp
      grind
  · have hiLt : i < Int.ofNat xs.length := by exact Int.lt_of_not_ge hiEnd
    have hnPos : 0 < n := by grind
    have hCondFalse :
        ¬ (decide (i < 0) || decide (n <= 0) ||
              decide (i >= Int.ofNat xs.length)) = true := by
      simp [Bool.or_eq_true, decide_eq_true_eq]
      grind
    split
    · rename_i h
      exact False.elim (hCondFalse h)
    · have hMin :
          min n (Int.ofNat xs.length - i) = Int.ofNat xs.length - i := by
        apply Int.min_eq_right
        grind
      have hTakeNat :
          Int.toNat (min n (Int.ofNat xs.length - i)) =
            Int.toNat (Int.ofNat xs.length - i) := by
        rw [hMin]
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hi
      have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by grind
      have hDiffCast :
          Int.ofNat (Int.toNat (Int.ofNat xs.length - i)) =
            Int.ofNat xs.length - i :=
        Int.toNat_of_nonneg hDiffNonneg
      have hDropLen :
          (xs.drop (Int.toNat i)).length = xs.length - Int.toNat i :=
        List.length_drop
      have hILeLenNat : Int.toNat i <= xs.length := by
        rw [← Int.ofNat_le]
        change Int.ofNat (Int.toNat i) <= Int.ofNat xs.length
        rw [hiCast]
        exact Int.le_of_lt hiLt
      have hSubCast :
          Int.ofNat (xs.length - Int.toNat i) =
            Int.ofNat xs.length - Int.ofNat (Int.toNat i) :=
        Int.ofNat_sub hILeLenNat
      have hDropLenCast :
          Int.ofNat (xs.drop (Int.toNat i)).length = Int.ofNat xs.length - i := by
        rw [hDropLen, hSubCast, hiCast]
      have hTakeEq :
          (xs.drop (Int.toNat i)).take
              (Int.toNat (Int.ofNat xs.length - i)) =
            xs.drop (Int.toNat i) := by
        apply List.take_of_length_le
        exact Int.ofNat_le.mp (by
          change
            Int.ofNat (xs.drop (Int.toNat i)).length <=
              Int.ofNat (Int.toNat (Int.ofNat xs.length - i))
          rw [hDropLenCast, hDiffCast]
          exact Int.le_refl _)
      rw [hTakeNat, hTakeEq]
      rw [hDropLen, hSubCast, hiCast]
      exact Int.le_refl _

private theorem native_seq_extract_len_le_len_sub_start_of_start_le_len
    (xs : List SmtValue) (i n : native_Int) :
    i <= Int.ofNat xs.length ->
    Int.ofNat (native_seq_extract xs i n).length <= Int.ofNat xs.length - i := by
  intro hiLe
  by_cases hiNeg : i < 0
  · simp [native_seq_extract, hiNeg]
    have hLenNonneg : (0 : Int) <= Int.ofNat xs.length := Int.natCast_nonneg _
    omega
  · have hiNonneg : 0 <= i := Int.le_of_not_gt hiNeg
    simp only [native_seq_extract]
    split
    · simp
      omega
    · have hTake :
          ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
            (xs.drop (Int.toNat i)).length := by
        rw [List.length_take]
        exact Nat.min_le_right _ _
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hiNonneg
      have hILeLenNat : Int.toNat i <= xs.length := by
        rw [← Int.ofNat_le]
        change Int.ofNat (Int.toNat i) <= Int.ofNat xs.length
        rw [hiCast]
        exact hiLe
      have hSubCast :
          Int.ofNat (xs.length - Int.toNat i) =
            Int.ofNat xs.length - Int.ofNat (Int.toNat i) :=
        Int.ofNat_sub hILeLenNat
      have hDropLen :
          Int.ofNat (xs.drop (Int.toNat i)).length =
            Int.ofNat xs.length - i := by
        rw [List.length_drop, hSubCast, hiCast]
      have hLenLe :
          Int.ofNat
              ((xs.drop (Int.toNat i)).take
                (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
            Int.ofNat (xs.drop (Int.toNat i)).length :=
        Int.ofNat_le.mpr hTake
      rw [hDropLen] at hLenLe
      exact hLenLe

private theorem native_seq_indexof_zero_nonneg_pat_le_len
    (xs pat : List SmtValue) :
    0 <= native_seq_indexof xs pat 0 ->
    pat.length <= xs.length := by
  intro hIdx
  rw [native_seq_indexof_eq_rec] at hIdx
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add] at hIdx
  split at hIdx
  · assumption
  · have hContr : ¬ ((0 : Int) <= -1) := by decide
    exact False.elim (hContr hIdx)

private theorem native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
    (xs pat : List SmtValue) :
    0 <= native_seq_indexof xs pat 0 ->
    Int.toNat (native_seq_indexof xs pat 0) + pat.length <= xs.length := by
  intro hIdxNonneg
  have hPatLe : pat.length <= xs.length :=
    native_seq_indexof_zero_nonneg_pat_le_len xs pat hIdxNonneg
  have hIdxLe :=
    native_seq_indexof_le_len_sub_pat_of_pat_le_len xs pat 0 hPatLe
  rw [← Int.ofNat_le]
  have hAdd :=
    Int.add_le_of_le_sub_right hIdxLe
  have hMax :
      max (native_seq_indexof xs pat 0) 0 =
        native_seq_indexof xs pat 0 :=
    Int.max_eq_left hIdxNonneg
  simpa [Int.ofNat_toNat, hMax] using hAdd

private theorem native_seq_replace_len_le_len_add_repl
    (xs pat repl : List SmtValue) :
    Int.ofNat (native_seq_replace xs pat repl).length <=
      Int.ofNat xs.length + Int.ofNat repl.length := by
  cases pat with
  | nil =>
      simp [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero, List.length_append]
      omega
  | cons p ps =>
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
        omega
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        omega

private theorem native_seq_replace_len_ge_len_sub_pat
    (xs pat repl : List SmtValue) :
    Int.ofNat xs.length - Int.ofNat pat.length <=
      Int.ofNat (native_seq_replace xs pat repl).length := by
  cases pat with
  | nil =>
      simp [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero, List.length_append]
      omega
  | cons p ps =>
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
        omega
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        omega

private theorem native_seq_replace_len_le_len_of_repl_le_pat
    (xs pat repl : List SmtValue) :
    repl.length <= pat.length ->
    Int.ofNat (native_seq_replace xs pat repl).length <= Int.ofNat xs.length := by
  intro hReplLe
  cases pat with
  | nil =>
      have hReplZero : repl.length = 0 := Nat.eq_zero_of_le_zero hReplLe
      simp [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero, List.length_append, hReplZero]
  | cons p ps =>
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        let j := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hBoundJ : j + (ps.length + 1) <= xs.length := by
          simpa [j] using hBound'
        have hReplLe' : repl.length <= ps.length + 1 := by
          simpa using hReplLe
        have hSplit :
            j + (ps.length + 1) + (xs.length - (j + (ps.length + 1))) =
              xs.length :=
          Nat.add_sub_of_le hBoundJ
        apply Int.ofNat_le.mpr
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        change
          j + (repl.length + (xs.length - (j + (ps.length + 1)))) <= xs.length
        calc
          j + (repl.length + (xs.length - (j + (ps.length + 1)))) <=
              j + ((ps.length + 1) + (xs.length - (j + (ps.length + 1)))) := by
            omega
          _ = xs.length := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSplit

private theorem native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
    (xs pat repl : List SmtValue) :
    pat.length <= repl.length ∨ xs.length <= repl.length ->
    Int.ofNat xs.length <= Int.ofNat (native_seq_replace xs pat repl).length := by
  intro hLe
  cases pat with
  | nil =>
      simp [StrEqReplSupport.native_seq_replace_eq_indexof,
        StrEqReplSupport.native_seq_indexof_nil_zero, List.length_append]
      omega
  | cons p ps =>
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hPatLeRepl : (p :: ps).length <= repl.length := by
          rcases hLe with hPatLe | hLenLe
          · exact hPatLe
          · omega
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        let j := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hBoundJ : j + (ps.length + 1) <= xs.length := by
          simpa [j] using hBound'
        have hPatLeRepl' : ps.length + 1 <= repl.length := by
          simpa using hPatLeRepl
        have hSplit :
            j + (ps.length + 1) + (xs.length - (j + (ps.length + 1))) =
              xs.length :=
          Nat.add_sub_of_le hBoundJ
        apply Int.ofNat_le.mpr
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        change
          xs.length <=
            j + (repl.length + (xs.length - (j + (ps.length + 1))))
        calc
          xs.length =
              j + ((ps.length + 1) + (xs.length - (j + (ps.length + 1)))) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSplit.symm
          _ <= j + (repl.length + (xs.length - (j + (ps.length + 1)))) := by
            omega

private theorem nat_toDigitsCore_len_le_fuel
    (base fuel n : Nat) (ds : List Char) :
    (Nat.toDigitsCore base fuel n ds).length <= fuel + ds.length := by
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
        omega
      · have h := ih (n / base) ((n % base).digitChar :: ds)
        simp at h
        omega

private theorem nat_toDigitsCore_len_le_value
    (base fuel n : Nat) (ds : List Char) :
    1 < base -> 0 < n ->
    (Nat.toDigitsCore base fuel n ds).length <= n + ds.length := by
  intro hbase hn
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
        omega
      · rename_i hnot
        have hnbase : base <= n := by
          have hlt : ¬ n < base := by
            intro hlt
            exact hnot (Or.inr hlt)
          exact Nat.le_of_not_gt hlt
        have hdivpos : 0 < n / base := Nat.div_pos hnbase (by omega)
        have h := ih (n / base) ((n % base).digitChar :: ds) hdivpos
        simp at h
        have hdivlt : n / base < n := Nat.div_lt_self hn hbase
        omega

private theorem nat_toDigitsCore_len_gt_acc
    (base fuel n : Nat) (ds : List Char) :
    ds.length < (Nat.toDigitsCore base (fuel + 1) n ds).length := by
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
      · have hcons : ds.length < ((n % base).digitChar :: ds).length := by simp
        have hrec :
            ((n % base).digitChar :: ds).length <
              (if base = 0 ∨ n / base < base then
                  (n / base % base).digitChar :: (n % base).digitChar :: ds
                else
                  Nat.toDigitsCore base fuel (n / base / base)
                    ((n / base % base).digitChar :: (n % base).digitChar :: ds)).length := by
          simpa [Nat.toDigitsCore] using
            ih (n / base) ((n % base).digitChar :: ds)
        exact Nat.lt_trans hcons hrec

private theorem nat_toString_len_le_succ
    (n : Nat) :
    (toString n).length <= n + 1 := by
  change (Nat.repr n).length <= n + 1
  simp [Nat.repr, Nat.toDigits]
  exact nat_toDigitsCore_len_le_fuel 10 (n + 1) n []

private theorem nat_toString_len_le_self_of_pos
    (n : Nat) :
    0 < n -> (toString n).length <= n := by
  intro hn
  change (Nat.repr n).length <= n
  simp [Nat.repr, Nat.toDigits]
  simpa using nat_toDigitsCore_len_le_value 10 (n + 1) n [] (by decide) hn

private theorem nat_toString_len_pos
    (n : Nat) :
    0 < (toString n).length := by
  change 0 < (Nat.repr n).length
  simp [Nat.repr, Nat.toDigits]
  simpa using nat_toDigitsCore_len_gt_acc 10 n n []

/-- `List.length (native_string_lit (toString (Int.ofNat n)))` is the decimal
length of `n`.  This used to close by `rfl` inside `exact`; under v4.33 the
`String.length`/`List.map` layers no longer reduce, so it needs `simp`. -/
private theorem native_string_lit_toString_ofNat_length (n : Nat) :
    List.length (native_string_lit (toString (Int.ofNat n))) =
      (toString n).length := by
  simp [native_string_lit, String.length, Int.repr]

private theorem native_str_from_int_len_pos_of_nonneg
    (z : native_Int) :
    0 <= z ->
    (0 : Int) < Int.ofNat (native_str_from_int z).length := by
  intro hz
  cases z with
  | ofNat n =>
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.natCast_nonneg n)
      rw [native_str_from_int, if_neg hlt,
        native_string_lit_toString_ofNat_length]
      exact Int.ofNat_lt.mpr (nat_toString_len_pos n)
  | negSucc n =>
      have hFalse : False := (Int.negSucc_not_nonneg n).mp hz
      exact False.elim hFalse

private theorem native_str_from_int_len_le_succ
    (z : native_Int) :
    0 <= z ->
    Int.ofNat (native_str_from_int z).length <= z + 1 := by
  intro hz
  cases z with
  | ofNat n =>
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.natCast_nonneg n)
      rw [native_str_from_int, if_neg hlt,
        native_string_lit_toString_ofNat_length]
      exact Int.ofNat_le.mpr (nat_toString_len_le_succ n)
  | negSucc n =>
      have hFalse : False := (Int.negSucc_not_nonneg n).mp hz
      exact False.elim hFalse

private theorem native_str_from_int_len_le_self_of_pos
    (z : native_Int) :
    0 < z ->
    Int.ofNat (native_str_from_int z).length <= z := by
  intro hz
  cases z with
  | ofNat n =>
      have hn : 0 < n := by
        exact Int.ofNat_lt.mp hz
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.natCast_nonneg n)
      rw [native_str_from_int, if_neg hlt,
        native_string_lit_toString_ofNat_length]
      exact Int.ofNat_le.mpr (nat_toString_len_le_self_of_pos n hn)
    | negSucc n =>
        have hFalse : False := by
          have hneg : Int.negSucc n < 0 := Int.negSucc_lt_zero n
          exact (Int.lt_asymm hneg hz).elim
        exact False.elim hFalse

private theorem str_from_int_len_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (n1 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_from_int_len_true n1 m hL1Branch
  rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
    ⟨z1, hN1Int, hN1Eval, hZn⟩
  rcases eo_ite_true hIte with hSuccBranch | hRest
  · rcases hSuccBranch with ⟨_, hAnd⟩
    rcases eo_and_true hAnd with ⟨hFalse, _⟩
    simp [__eo_not, native_not, SmtEval.native_not] at hFalse
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hNBranch | hRest2
    · rcases hNBranch with ⟨_, hAnd⟩
      rcases eo_and_true hAnd with ⟨hFalse, _⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hFalse
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
      · rcases hOneBranch with ⟨hOneEq, hAnd⟩
        rcases eo_and_true hAnd with ⟨_, hSimple⟩
        have hN1Nonneg : 0 <= z1 :=
          int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
        have hZMEq :
            zm = (1 : native_Int) :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hOneEq) hMEval
            (numeral_int_eval M 1)
        rw [hZn, hZMEq]
        have hPos := native_str_from_int_len_pos_of_nonneg z1 hN1Nonneg
        have hNatPos : 0 < (native_str_from_int z1).length :=
          Int.ofNat_lt.mp hPos
        exact Int.ofNat_le.mpr hNatPos
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_from_int_len_l1_false_order
    (M : SmtModel) (hM : model_wf M)
    (n1 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_from_int_len_false n1 m hL1Branch
  rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
    ⟨z1, hN1Int, hN1Eval, hZn⟩
  let succN :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0))
  have hSuccEval :
      __smtx_model_eval M (__eo_to_smt succN) =
        SmtValue.Numeral (z1 + 1) := by
    simpa [succN] using
      plus_trailing_zero_int_eval M n1 (Term.Numeral 1) z1 1
        hN1Eval (numeral_int_eval M 1)
  rcases eo_ite_true hIte with hSuccBranch | hRest
  · rcases hSuccBranch with ⟨hSuccEq, hAnd⟩
    rcases eo_and_true hAnd with ⟨_, hSimple⟩
    have hN1Nonneg : 0 <= z1 :=
      int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
    have hZMEq :
        zm = z1 + 1 :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hSuccEq) hMEval hSuccEval
    rw [hZn, hZMEq]
    exact native_str_from_int_len_le_succ z1 hN1Nonneg
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hNBranch | hRest2
    · rcases hNBranch with ⟨hNEq, hAnd⟩
      rcases eo_and_true hAnd with ⟨_, hPred⟩
      have hN1Pos : 0 < z1 :=
        int_pos_of_simple_gt_zero_true M hM n1 z1 hN1Int hN1Eval hPred
      have hZMEq :
          zm = z1 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hNEq) hMEval hN1Eval
      rw [hZn, hZMEq]
      exact native_str_from_int_len_le_self_of_pos z1 hN1Pos
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
      · rcases hOneBranch with ⟨_, hAnd⟩
        rcases eo_and_true hAnd with ⟨hFalse, _⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_substr_len_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (s n1 n2 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_substr_len_true s n1 n2 m hL1Branch
  dsimp only at hIte
  rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
    ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
      hN2Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let sumN :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
  let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hSumInt : __smtx_typeof (__eo_to_smt sumN) = SmtType.Int := by
    simpa [sumN] using plus_trailing_zero_int_type n1 n2 hN1Int hN2Int
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumN) =
        SmtValue.Numeral (z1 + z2) := by
    simpa [sumN] using plus_trailing_zero_int_eval M n1 n2 z1 z2 hN1Eval hN2Eval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLenStart) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
    simpa [negLenStart] using
      neg_int_eval_of_args M lenS n1
        (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
  rcases eo_ite_true hIte with hN2Branch | hRest
  · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨_, hAnd⟩
      rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
      have hN1Nonneg : 0 <= z1 :=
        int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hN1Simple
      have hLenSGeSum :
          z1 + z2 <= Int.ofNat (native_unpack_seq ss).length :=
        int_le_of_simple_geq_true M hM lenS sumN
          (Int.ofNat (native_unpack_seq ss).length) (z1 + z2)
          hLenSInt hSumInt hLenSEval hSumEval
          (by simpa [lenS, sumN] using hPred)
      have hZMEq :
          zm = z2 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
      rw [hZn, hZMEq]
      by_cases hN2Nonneg : 0 <= z2
      · exact native_seq_extract_len_ge_arg_of_in_range
          (native_unpack_seq ss) z1 z2 hN1Nonneg hN2Nonneg hLenSGeSum
      · have hLenNonneg :=
          native_seq_extract_len_nonneg (native_unpack_seq ss) z1 z2
        exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge hN2Nonneg))
          hLenNonneg
    · rcases hElse with ⟨hContr, _⟩
      cases hContr
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨_, hNot⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hNot
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
        rcases eo_ite_true hUnderIte with hThen | hElse
        · rcases hThen with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
          have hN1Nonneg : 0 <= z1 :=
            int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval
              hN1Simple
          have hLenSLeSum :
              Int.ofNat (native_unpack_seq ss).length <= z1 + z2 :=
            int_le_of_simple_geq_true M hM sumN lenS (z1 + z2)
              (Int.ofNat (native_unpack_seq ss).length)
              hSumInt hLenSInt hSumEval hLenSEval
              (by simpa [lenS, sumN] using hPred)
          have hZMEq :
              zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
            int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
          rw [hZn, hZMEq]
          exact native_seq_extract_len_ge_len_sub_start_of_covers_end
            (native_unpack_seq ss) z1 z2 hN1Nonneg hLenSLeSum
        · rcases hElse with ⟨hContr, _⟩
          cases hContr
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_substr_len_l1_false_order
    (M : SmtModel) (hM : model_wf M)
    (s n1 n2 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_substr_len_false s n1 n2 m hL1Branch
  dsimp only at hIte
  rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
    ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
      hN2Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLenStart) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
    simpa [negLenStart] using
      neg_int_eval_of_args M lenS n1
        (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
  rcases eo_ite_true hIte with hN2Branch | hRest
  · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨hContr, _⟩
      cases hContr
    · rcases hElse with ⟨_, hN2Simple⟩
      have hN2Nonneg : 0 <= z2 :=
        int_nonneg_of_simple_rec_true M hM n2 z2 hN2Int hN2Eval hN2Simple
      have hZMEq :
          zm = z2 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
      rw [hZn, hZMEq]
      exact native_seq_extract_len_le_arg_of_nonneg
        (native_unpack_seq ss) z1 z2 hN2Nonneg
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨hLenEq, _⟩
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_extract_len_le_len (native_unpack_seq ss) z1 z2
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
        rcases eo_ite_true hUnderIte with hThen | hElse
        · rcases hThen with ⟨hContr, _⟩
          cases hContr
        · rcases hElse with ⟨_, hPred⟩
          have hN1LeLenS :
              z1 <= Int.ofNat (native_unpack_seq ss).length :=
            int_le_of_simple_geq_true M hM lenS n1
              (Int.ofNat (native_unpack_seq ss).length) z1
              hLenSInt hN1Int hLenSEval hN1Eval
              (by simpa [lenS] using hPred)
          have hZMEq :
              zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
            int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
          rw [hZn, hZMEq]
          exact native_seq_extract_len_le_len_sub_start_of_start_le_len
            (native_unpack_seq ss) z1 z2 hN1LeLenS
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_replace_len_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (s t r m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_replace_len_true s t r m hL1Branch
  dsimp only at hIte
  rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
    ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  let lenR := Term.Apply (Term.UOp UserOp.str_len) r
  let sumLen :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
  let negLen := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
    simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  have hLenREval :
      __smtx_model_eval M (__eo_to_smt lenR) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
    simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length +
            Int.ofNat (native_unpack_seq rr).length) := by
    simpa [sumLen] using
      plus_trailing_zero_int_eval M lenS lenR
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length -
            Int.ofNat (native_unpack_seq tt).length) := by
    simpa [negLen] using
      neg_int_eval_of_args M lenS lenT
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq tt).length) hLenSEval hLenTEval
  rcases eo_ite_true hIte with hLenBranch | hRest
  · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨_, hOr⟩
      have hLe :
          (native_unpack_seq tt).length <= (native_unpack_seq rr).length ∨
            (native_unpack_seq ss).length <= (native_unpack_seq rr).length := by
        rcases eo_or_true hOr with hPred | hPred
        · have hLenTLeLenR :
              Int.ofNat (native_unpack_seq tt).length <=
                Int.ofNat (native_unpack_seq rr).length :=
            int_le_of_simple_geq_true M hM lenR lenT
              (Int.ofNat (native_unpack_seq rr).length)
              (Int.ofNat (native_unpack_seq tt).length)
              hLenRInt hLenTInt hLenREval hLenTEval
              (by simpa [lenR, lenT] using hPred)
          exact Or.inl (Int.ofNat_le.mp hLenTLeLenR)
        · have hLenSLeLenR :
              Int.ofNat (native_unpack_seq ss).length <=
                Int.ofNat (native_unpack_seq rr).length :=
            int_le_of_simple_geq_true M hM lenR lenS
              (Int.ofNat (native_unpack_seq rr).length)
              (Int.ofNat (native_unpack_seq ss).length)
              hLenRInt hLenSInt hLenREval hLenSEval
              (by simpa [lenR, lenS] using hPred)
          exact Or.inr (Int.ofNat_le.mp hLenSLeLenR)
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr) hLe
    · rcases hElse with ⟨hContr, _⟩
      cases hContr
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hSumBranch | hRest2
    · rcases hSumBranch with ⟨_, hNot⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hNot
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, _⟩
        have hZMEq :
            zm =
              Int.ofNat (native_unpack_seq ss).length -
                Int.ofNat (native_unpack_seq tt).length :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
        rw [hZn, hZMEq]
        exact native_seq_replace_len_ge_len_sub_pat
          (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_replace_len_l1_false_order
    (M : SmtModel) (hM : model_wf M)
    (s t r m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_replace_len_false s t r m hL1Branch
  dsimp only at hIte
  rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
    ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  let lenR := Term.Apply (Term.UOp UserOp.str_len) r
  let sumLen :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
    simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  have hLenREval :
      __smtx_model_eval M (__eo_to_smt lenR) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
    simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length +
            Int.ofNat (native_unpack_seq rr).length) := by
    simpa [sumLen] using
      plus_trailing_zero_int_eval M lenS lenR
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
  rcases eo_ite_true hIte with hLenBranch | hRest
  · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨hContr, _⟩
      cases hContr
    · rcases hElse with ⟨_, hPred⟩
      have hLenRLeLenT :
          Int.ofNat (native_unpack_seq rr).length <=
            Int.ofNat (native_unpack_seq tt).length :=
        int_le_of_simple_geq_true M hM lenT lenR
          (Int.ofNat (native_unpack_seq tt).length)
          (Int.ofNat (native_unpack_seq rr).length)
          hLenTInt hLenRInt hLenTEval hLenREval
          (by simpa [lenT, lenR] using hPred)
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_le_len_of_repl_le_pat
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
        (Int.ofNat_le.mp hLenRLeLenT)
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hSumBranch | hRest2
    · rcases hSumBranch with ⟨hSumEq, _⟩
      have hZMEq :
          zm =
            Int.ofNat (native_unpack_seq ss).length +
              Int.ofNat (native_unpack_seq rr).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hSumEq) hMEval hSumEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_le_len_add_repl
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨_, hFalse⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_to_int_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte :
      __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean true :=
    l1_str_to_int_true s m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
  · rcases hMinusBranch with ⟨hMinusEq, _⟩
    have hMEq :
        zm = (-1 : native_Int) :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
        (numeral_int_eval M (-1))
    rcases str_to_int_eval_decomp M hM s zn hNInt hNEval with
      ⟨ss, _hSEval, hZn⟩
    rw [hMEq, hZn]
    exact native_str_to_int_ge_neg_one (native_unpack_string ss)
  · rcases hFalseBranch with ⟨_, hFalse⟩
    cases hFalse

private theorem str_to_int_l1_false_order
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean false) =
      Term.Boolean true ->
    False := by
  intro hL1Branch
  have hIte :
      __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
          (Term.Boolean false) (Term.Boolean false) =
        Term.Boolean true :=
    l1_str_to_int_false s m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
  · rcases hMinusBranch with ⟨_, hFalse⟩
    cases hFalse
  · rcases hFalseBranch with ⟨_, hFalse⟩
    cases hFalse

private theorem str_indexof_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (s t n0 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_indexof_true s t n0 m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hRest
  · rcases hMinusBranch with ⟨hMinusEq, _⟩
    have hMEq :
        zm = (-1 : native_Int) :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
        (numeral_int_eval M (-1))
    rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
      ⟨_T, ss, tt, z0, _hSTy, _hTTy, _hN0Ty, _hSEval, _hTEval,
        _hN0Eval, hZn⟩
    rw [hMEq, hZn]
    exact native_seq_indexof_ge_neg_one (native_unpack_seq ss)
      (native_unpack_seq tt) z0
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨_, hFalse⟩
      cases hFalse
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨_, hAnd⟩
        rcases eo_and_true hAnd with ⟨hFalse, _⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_indexof_l1_false_order
    (M : SmtModel) (hM : model_wf M)
    (s t n0 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_indexof_false s t n0 m hL1Branch
  rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
    ⟨T, ss, tt, z0, hSTy, hTTy, _hN0Ty, hSEval, hTEval, _hN0Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  rcases eo_ite_true hIte with hMinusBranch | hRest
  · rcases hMinusBranch with ⟨_, hFalse⟩
    cases hFalse
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨hLenEq, _⟩
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_indexof_le_len (native_unpack_seq ss)
        (native_unpack_seq tt) z0
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hAnd⟩
        rcases eo_and_true hAnd with ⟨_, hPred⟩
        have hLenTLeLenS :
            Int.ofNat (native_unpack_seq tt).length <=
              Int.ofNat (native_unpack_seq ss).length :=
          int_le_of_simple_geq_true M hM lenS lenT
            (Int.ofNat (native_unpack_seq ss).length)
            (Int.ofNat (native_unpack_seq tt).length)
            hLenSInt hLenTInt hLenSEval hLenTEval
            (by simpa [lenS, lenT] using hPred)
        have hLenTLeLenSNat :
            (native_unpack_seq tt).length <= (native_unpack_seq ss).length :=
          Int.ofNat_le.mp hLenTLeLenS
        have hNegEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT)) =
              SmtValue.Numeral
                (Int.ofNat (native_unpack_seq ss).length -
                  Int.ofNat (native_unpack_seq tt).length) :=
          neg_int_eval_of_args M lenS lenT
            (Int.ofNat (native_unpack_seq ss).length)
            (Int.ofNat (native_unpack_seq tt).length)
            hLenSEval hLenTEval
        have hZMEq :
            zm =
              Int.ofNat (native_unpack_seq ss).length -
                Int.ofNat (native_unpack_seq tt).length :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval
            (by simpa [lenS, lenT] using hNegEval)
        rw [hZn, hZMEq]
        exact native_seq_indexof_le_len_sub_pat_of_pat_le_len
          (native_unpack_seq ss) (native_unpack_seq tt) z0 hLenTLeLenSNat
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_len_l1_true_order
    (M : SmtModel) (hM : model_wf M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len) s) m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hMInt hNEval hMEval hL1Branch
  have hMNe : m ≠ Term.Stuck := by
    intro hSt
    subst m
    exact (by native_decide :
      __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
  cases s with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try
            simp [__eo_l_1___str_arith_entail_is_approx,
              __str_arith_entail_is_approx_len, __eo_not, native_not,
              SmtEval.native_not] at hL1Branch
          case str_from_int =>
            exact str_from_int_len_l1_true_order M hM x m zn zm
              hNInt hNEval hMEval
              (by
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len, __eo_not, native_not,
                  SmtEval.native_not]
                exact hL1Branch)
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len] at hL1Branch
          | Apply h z =>
              cases h with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not] at hL1Branch
                  case str_substr =>
                    exact str_substr_len_l1_true_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not]
                        exact hL1Branch)
                  case str_replace =>
                    exact str_replace_len_l1_true_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not]
                        exact hL1Branch)
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len] at hL1Branch
      | _ =>
          simp [__eo_l_1___str_arith_entail_is_approx,
            __str_arith_entail_is_approx_len] at hL1Branch
  | _ =>
      simp [__eo_l_1___str_arith_entail_is_approx,
        __str_arith_entail_is_approx_len] at hL1Branch

private theorem str_len_l1_false_order
    (M : SmtModel) (hM : model_wf M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len) s) m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hMInt hNEval hMEval hL1Branch
  have hMNe : m ≠ Term.Stuck := by
    intro hSt
    subst m
    exact (by native_decide :
      __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
  cases s with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try
            simp [__eo_l_1___str_arith_entail_is_approx,
              __str_arith_entail_is_approx_len, __eo_not, native_not,
              SmtEval.native_not] at hL1Branch
          case str_from_int =>
            exact str_from_int_len_l1_false_order M hM x m zn zm
              hNInt hNEval hMEval
              (by
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len, __eo_not, native_not,
                  SmtEval.native_not]
                exact hL1Branch)
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len] at hL1Branch
          | Apply h z =>
              cases h with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not] at hL1Branch
                  case str_substr =>
                    exact str_substr_len_l1_false_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not]
                        exact hL1Branch)
                  case str_replace =>
                    exact str_replace_len_l1_false_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not]
                        exact hL1Branch)
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len] at hL1Branch
      | _ =>
          simp [__eo_l_1___str_arith_entail_is_approx,
            __str_arith_entail_is_approx_len] at hL1Branch
  | _ =>
      simp [__eo_l_1___str_arith_entail_is_approx,
        __str_arith_entail_is_approx_len] at hL1Branch

private theorem str_arith_entail_is_approx_int_eval_order_bool
    (M : SmtModel) (hM : model_wf M) :
    (n m : Term) -> (zn zm : native_Int) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
      (__str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
        zm ≤ zn) ∧
      (__str_arith_entail_is_approx n m (Term.Boolean false) = Term.Boolean true ->
        zn ≤ zm)
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2,
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        have hApprox' :
            __eo_ite
                (__eo_eq
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4))
                (Term.Boolean true)
                (__eo_and (__str_arith_entail_is_approx n1 n3 (Term.Boolean true))
                  (__str_arith_entail_is_approx n2 n4 (Term.Boolean true))) =
              Term.Boolean true := by
          simpa [__str_arith_entail_is_approx, __eo_l_1___str_arith_entail_is_approx] using
            hApprox
        rcases eo_ite_true hApprox' with hEqBranch | hL1Branch
        · rcases hEqBranch with ⟨hEqCond, _⟩
          have hEqTerms := eo_eq_true_eq hEqCond
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · rcases hL1Branch with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hA, hB⟩
          rcases plus_int_eval_decomp M hM n1 n2 zn hNInt hNEval with
            ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
          rcases plus_int_eval_decomp M hM n3 n4 zm hMInt hMEval with
            ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
          have h13 :
              z3 ≤ z1 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n1 n3 z1 z3
              hN1Int hN3Int hN1Eval hN3Eval).1 hA
          have h24 :
              z4 ≤ z2 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n2 n4 z2 z4
              hN2Int hN4Int hN2Eval hN4Eval).1 hB
          rw [hZn, hZm]
          calc
            z3 + z4 ≤ z1 + z4 := Int.add_le_add_right h13 z4
            _ ≤ z1 + z2 := Int.add_le_add_left h24 z1
      · intro hApprox
        have hApprox' :
            __eo_ite
                (__eo_eq
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4))
                (Term.Boolean true)
                (__eo_and (__str_arith_entail_is_approx n1 n3 (Term.Boolean false))
                  (__str_arith_entail_is_approx n2 n4 (Term.Boolean false))) =
              Term.Boolean true := by
          simpa [__str_arith_entail_is_approx, __eo_l_1___str_arith_entail_is_approx] using
            hApprox
        rcases eo_ite_true hApprox' with hEqBranch | hL1Branch
        · rcases hEqBranch with ⟨hEqCond, _⟩
          have hEqTerms := eo_eq_true_eq hEqCond
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · rcases hL1Branch with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hA, hB⟩
          rcases plus_int_eval_decomp M hM n1 n2 zn hNInt hNEval with
            ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
          rcases plus_int_eval_decomp M hM n3 n4 zm hMInt hMEval with
            ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
          have h13 :
              z1 ≤ z3 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n1 n3 z1 z3
              hN1Int hN3Int hN1Eval hN3Eval).2 hA
          have h24 :
              z2 ≤ z4 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n2 n4 z2 z4
              hN2Int hN4Int hN2Eval hN4Eval).2 hB
          rw [hZn, hZm]
          calc
            z1 + z2 ≤ z3 + z2 := Int.add_le_add_right h13 z2
            _ ≤ z3 + z4 := Int.add_le_add_left h24 z3
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1)),
    Term.Apply (Term.Apply (Term.UOp UserOp.mult) n1')
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1)),
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · have hEqTerms := eo_eq_true_eq hEqBranch
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · have hReq :
              __eo_requires (__eo_eq n1 n1') (Term.Boolean true)
                  (__eo_ite (__eo_is_neg n1)
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean false))
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean true))) =
                Term.Boolean true := by
            simpa [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
              SmtEval.native_not] using hL1Branch
          rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
          have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
          rcases mult_int_eval_decomp M hM n1
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1))
              zn hNInt hNEval with
            ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
          rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1) zx1 hX1Int hX1Eval with
            ⟨zx, zOneX, hXInt, _hOneXInt, hXEval, hOneXEval, hZx1⟩
          have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
          have hZx1' : zx1 = zx := by
            simpa [hOneX] using hZx1
          rcases mult_int_eval_decomp M hM n1'
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1))
              zm hMInt hMEval with
            ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
          rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1) zy1 hY1Int hY1Eval with
            ⟨zy, zOneY, hYInt, _hOneYInt, hYEval, hOneYEval, hZy1⟩
          have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
          have hZy1' : zy1 = zy := by
            simpa [hOneY] using hZy1
          have hCoeffEq :
              zc = zc' :=
            int_eval_eq_of_term_eq M hCoeffEqTerms hCEval hC'Eval
          rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
          · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNeg : zc < 0 :=
              int_eval_lt_zero_of_eo_is_neg_true M n1 zc hCInt hCEval hNegCond
            have hXY :
                zx ≤ zy :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).2 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hCNeg) hXY
          · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNonneg : 0 <= zc :=
              int_eval_nonneg_of_eo_is_neg_false M n1 zc hCInt hCEval hNegCond
            have hXY :
                zy ≤ zx :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).1 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonneg_left hXY hCNonneg
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · have hEqTerms := eo_eq_true_eq hEqBranch
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · have hReq :
              __eo_requires (__eo_eq n1 n1') (Term.Boolean true)
                  (__eo_ite (__eo_is_neg n1)
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean true))
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean false))) =
                Term.Boolean true := by
            simpa [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
              SmtEval.native_not] using hL1Branch
          rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
          have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
          rcases mult_int_eval_decomp M hM n1
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1))
              zn hNInt hNEval with
            ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
          rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1) zx1 hX1Int hX1Eval with
            ⟨zx, zOneX, hXInt, _hOneXInt, hXEval, hOneXEval, hZx1⟩
          have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
          have hZx1' : zx1 = zx := by
            simpa [hOneX] using hZx1
          rcases mult_int_eval_decomp M hM n1'
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1))
              zm hMInt hMEval with
            ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
          rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1) zy1 hY1Int hY1Eval with
            ⟨zy, zOneY, hYInt, _hOneYInt, hYEval, hOneYEval, hZy1⟩
          have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
          have hZy1' : zy1 = zy := by
            simpa [hOneY] using hZy1
          have hCoeffEq :
              zc = zc' :=
            int_eval_eq_of_term_eq M hCoeffEqTerms hCEval hC'Eval
          rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
          · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNeg : zc < 0 :=
              int_eval_lt_zero_of_eo_is_neg_true M n1 zc hCInt hCEval hNegCond
            have hXY :
                zy ≤ zx :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).1 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hCNeg) hXY
          · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNonneg : 0 <= zc :=
              int_eval_nonneg_of_eo_is_neg_false M n1 zc hCInt hCEval hNegCond
            have hXY :
                zx ≤ zy :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).2 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonneg_left hXY hCNonneg
  | Term.Apply (Term.UOp UserOp.str_to_int) s, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte :
              __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
                  (Term.Boolean true) (Term.Boolean false) =
                Term.Boolean true :=
            l1_str_to_int_true s m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
          · rcases hMinusBranch with ⟨hMinusEq, _⟩
            have hMEq :
                zm = (-1 : native_Int) :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
                (numeral_int_eval M (-1))
            rcases str_to_int_eval_decomp M hM s zn hNInt hNEval with
              ⟨ss, _hSEval, hZn⟩
            rw [hMEq, hZn]
            exact native_str_to_int_ge_neg_one (native_unpack_string ss)
          · rcases hFalseBranch with ⟨_, hFalse⟩
            cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte :
              __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
                  (Term.Boolean false) (Term.Boolean false) =
                Term.Boolean true :=
            l1_str_to_int_false s m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
          · rcases hMinusBranch with ⟨_, hFalse⟩
            cases hFalse
          · rcases hFalseBranch with ⟨_, hFalse⟩
            cases hFalse
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_indexof_true s t n0 m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hRest
          · rcases hMinusBranch with ⟨hMinusEq, _⟩
            have hMEq :
                zm = (-1 : native_Int) :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
                (numeral_int_eval M (-1))
            rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
              ⟨T, ss, tt, z0, _hSTy, _hTTy, _hN0Ty, _hSEval, _hTEval,
                _hN0Eval, hZn⟩
            rw [hMEq, hZn]
            exact native_seq_indexof_ge_neg_one (native_unpack_seq ss)
              (native_unpack_seq tt) z0
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨_, hFalse⟩
              cases hFalse
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨_, hAnd⟩
                rcases eo_and_true hAnd with ⟨hFalse, _⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_indexof_false s t n0 m hL1Branch
          rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
            ⟨T, ss, tt, z0, hSTy, hTTy, _hN0Ty, hSEval, hTEval, _hN0Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          rcases eo_ite_true hIte with hMinusBranch | hRest
          · rcases hMinusBranch with ⟨_, hFalse⟩
            cases hFalse
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨hLenEq, _⟩
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_indexof_le_len (native_unpack_seq ss)
                (native_unpack_seq tt) z0
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hAnd⟩
                rcases eo_and_true hAnd with ⟨_, hPred⟩
                have hLenTLeLenS :
                    Int.ofNat (native_unpack_seq tt).length <=
                      Int.ofNat (native_unpack_seq ss).length :=
                  int_le_of_simple_geq_true M hM lenS lenT
                    (Int.ofNat (native_unpack_seq ss).length)
                    (Int.ofNat (native_unpack_seq tt).length)
                    hLenSInt hLenTInt hLenSEval hLenTEval
                    (by simpa [lenS, lenT] using hPred)
                have hLenTLeLenSNat :
                    (native_unpack_seq tt).length <= (native_unpack_seq ss).length :=
                  Int.ofNat_le.mp hLenTLeLenS
                have hNegEval :
                    __smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT)) =
                      SmtValue.Numeral
                        (Int.ofNat (native_unpack_seq ss).length -
                          Int.ofNat (native_unpack_seq tt).length) :=
                  neg_int_eval_of_args M lenS lenT
                    (Int.ofNat (native_unpack_seq ss).length)
                    (Int.ofNat (native_unpack_seq tt).length)
                    hLenSEval hLenTEval
                have hZMEq :
                    zm =
                      Int.ofNat (native_unpack_seq ss).length -
                        Int.ofNat (native_unpack_seq tt).length :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval
                    (by simpa [lenS, lenT] using hNegEval)
                rw [hZn, hZMEq]
                exact native_seq_indexof_le_len_sub_pat_of_pat_le_len
                  (native_unpack_seq ss) (native_unpack_seq tt) z0 hLenTLeLenSNat
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_substr_len_true s n1 n2 m hL1Branch
          dsimp only at hIte
          rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
            ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
              hN2Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let sumN :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
          let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hSumInt : __smtx_typeof (__eo_to_smt sumN) = SmtType.Int := by
            simpa [sumN] using plus_trailing_zero_int_type n1 n2 hN1Int hN2Int
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumN) =
                SmtValue.Numeral (z1 + z2) := by
            simpa [sumN] using plus_trailing_zero_int_eval M n1 n2 z1 z2 hN1Eval hN2Eval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLenStart) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
            simpa [negLenStart] using
              neg_int_eval_of_args M lenS n1
                (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
          rcases eo_ite_true hIte with hN2Branch | hRest
          · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨_, hAnd⟩
              rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
              have hN1Nonneg : 0 <= z1 :=
                int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hN1Simple
              have hLenSGeSum :
                  z1 + z2 <= Int.ofNat (native_unpack_seq ss).length :=
                int_le_of_simple_geq_true M hM lenS sumN
                  (Int.ofNat (native_unpack_seq ss).length) (z1 + z2)
                  hLenSInt hSumInt hLenSEval hSumEval
                  (by simpa [lenS, sumN] using hPred)
              have hZMEq :
                  zm = z2 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
              rw [hZn, hZMEq]
              by_cases hN2Nonneg : 0 <= z2
              · exact native_seq_extract_len_ge_arg_of_in_range
                  (native_unpack_seq ss) z1 z2 hN1Nonneg hN2Nonneg hLenSGeSum
              · have hLenNonneg :=
                  native_seq_extract_len_nonneg (native_unpack_seq ss) z1 z2
                exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge hN2Nonneg))
                  hLenNonneg
            · rcases hElse with ⟨hContr, _⟩
              cases hContr
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨_, hNot⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hNot
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
                rcases eo_ite_true hUnderIte with hThen | hElse
                · rcases hThen with ⟨_, hAnd⟩
                  rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
                  have hN1Nonneg : 0 <= z1 :=
                    int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval
                      hN1Simple
                  have hLenSLeSum :
                      Int.ofNat (native_unpack_seq ss).length <= z1 + z2 :=
                    int_le_of_simple_geq_true M hM sumN lenS (z1 + z2)
                      (Int.ofNat (native_unpack_seq ss).length)
                      hSumInt hLenSInt hSumEval hLenSEval
                      (by simpa [lenS, sumN] using hPred)
                  have hZMEq :
                      zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
                    int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                  rw [hZn, hZMEq]
                  exact native_seq_extract_len_ge_len_sub_start_of_covers_end
                    (native_unpack_seq ss) z1 z2 hN1Nonneg hLenSLeSum
                · rcases hElse with ⟨hContr, _⟩
                  cases hContr
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_substr_len_false s n1 n2 m hL1Branch
          dsimp only at hIte
          rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
            ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
              hN2Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLenStart) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
            simpa [negLenStart] using
              neg_int_eval_of_args M lenS n1
                (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
          rcases eo_ite_true hIte with hN2Branch | hRest
          · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨hContr, _⟩
              cases hContr
            · rcases hElse with ⟨_, hN2Simple⟩
              have hN2Nonneg : 0 <= z2 :=
                int_nonneg_of_simple_rec_true M hM n2 z2 hN2Int hN2Eval hN2Simple
              have hZMEq :
                  zm = z2 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
              rw [hZn, hZMEq]
              exact native_seq_extract_len_le_arg_of_nonneg
                (native_unpack_seq ss) z1 z2 hN2Nonneg
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨hLenEq, _⟩
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_extract_len_le_len (native_unpack_seq ss) z1 z2
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
                rcases eo_ite_true hUnderIte with hThen | hElse
                · rcases hThen with ⟨hContr, _⟩
                  cases hContr
                · rcases hElse with ⟨_, hPred⟩
                  have hN1LeLenS :
                      z1 <= Int.ofNat (native_unpack_seq ss).length :=
                    int_le_of_simple_geq_true M hM lenS n1
                      (Int.ofNat (native_unpack_seq ss).length) z1
                      hLenSInt hN1Int hLenSEval hN1Eval
                      (by simpa [lenS] using hPred)
                  have hZMEq :
                      zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
                    int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                  rw [hZn, hZMEq]
                  exact native_seq_extract_len_le_len_sub_start_of_start_le_len
                    (native_unpack_seq ss) z1 z2 hN1LeLenS
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_replace_len_true s t r m hL1Branch
          dsimp only at hIte
          rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
            ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          let lenR := Term.Apply (Term.UOp UserOp.str_len) r
          let sumLen :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
          let negLen := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
            simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          have hLenREval :
              __smtx_model_eval M (__eo_to_smt lenR) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
            simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length +
                    Int.ofNat (native_unpack_seq rr).length) := by
            simpa [sumLen] using
              plus_trailing_zero_int_eval M lenS lenR
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length -
                    Int.ofNat (native_unpack_seq tt).length) := by
            simpa [negLen] using
              neg_int_eval_of_args M lenS lenT
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq tt).length) hLenSEval hLenTEval
          rcases eo_ite_true hIte with hLenBranch | hRest
          · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨_, hOr⟩
              have hLe :
                  (native_unpack_seq tt).length <= (native_unpack_seq rr).length ∨
                    (native_unpack_seq ss).length <= (native_unpack_seq rr).length := by
                rcases eo_or_true hOr with hPred | hPred
                · have hLenTLeLenR :
                      Int.ofNat (native_unpack_seq tt).length <=
                        Int.ofNat (native_unpack_seq rr).length :=
                    int_le_of_simple_geq_true M hM lenR lenT
                      (Int.ofNat (native_unpack_seq rr).length)
                      (Int.ofNat (native_unpack_seq tt).length)
                      hLenRInt hLenTInt hLenREval hLenTEval
                      (by simpa [lenR, lenT] using hPred)
                  exact Or.inl (Int.ofNat_le.mp hLenTLeLenR)
                · have hLenSLeLenR :
                      Int.ofNat (native_unpack_seq ss).length <=
                        Int.ofNat (native_unpack_seq rr).length :=
                    int_le_of_simple_geq_true M hM lenR lenS
                      (Int.ofNat (native_unpack_seq rr).length)
                      (Int.ofNat (native_unpack_seq ss).length)
                      hLenRInt hLenSInt hLenREval hLenSEval
                      (by simpa [lenR, lenS] using hPred)
                  exact Or.inr (Int.ofNat_le.mp hLenSLeLenR)
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr) hLe
            · rcases hElse with ⟨hContr, _⟩
              cases hContr
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hSumBranch | hRest2
            · rcases hSumBranch with ⟨_, hNot⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hNot
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, _⟩
                have hZMEq :
                    zm =
                      Int.ofNat (native_unpack_seq ss).length -
                        Int.ofNat (native_unpack_seq tt).length :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                rw [hZn, hZMEq]
                exact native_seq_replace_len_ge_len_sub_pat
                  (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_replace_len_false s t r m hL1Branch
          dsimp only at hIte
          rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
            ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          let lenR := Term.Apply (Term.UOp UserOp.str_len) r
          let sumLen :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
            simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          have hLenREval :
              __smtx_model_eval M (__eo_to_smt lenR) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
            simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length +
                    Int.ofNat (native_unpack_seq rr).length) := by
            simpa [sumLen] using
              plus_trailing_zero_int_eval M lenS lenR
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
          rcases eo_ite_true hIte with hLenBranch | hRest
          · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨hContr, _⟩
              cases hContr
            · rcases hElse with ⟨_, hPred⟩
              have hLenRLeLenT :
                  Int.ofNat (native_unpack_seq rr).length <=
                    Int.ofNat (native_unpack_seq tt).length :=
                int_le_of_simple_geq_true M hM lenT lenR
                  (Int.ofNat (native_unpack_seq tt).length)
                  (Int.ofNat (native_unpack_seq rr).length)
                  hLenTInt hLenRInt hLenTEval hLenREval
                  (by simpa [lenT, lenR] using hPred)
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_le_len_of_repl_le_pat
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
                (Int.ofNat_le.mp hLenRLeLenT)
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hSumBranch | hRest2
            · rcases hSumBranch with ⟨hSumEq, _⟩
              have hZMEq :
                  zm =
                    Int.ofNat (native_unpack_seq ss).length +
                      Int.ofNat (native_unpack_seq rr).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hSumEq) hMEval hSumEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_le_len_add_repl
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨_, hFalse⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.UOp UserOp.str_from_int) n1), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_from_int_len_true n1 m hL1Branch
          rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
            ⟨z1, hN1Int, hN1Eval, hZn⟩
          rcases eo_ite_true hIte with hSuccBranch | hRest
          · rcases hSuccBranch with ⟨_, hAnd⟩
            rcases eo_and_true hAnd with ⟨hFalse, _⟩
            simp [__eo_not, native_not, SmtEval.native_not] at hFalse
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hNBranch | hRest2
            · rcases hNBranch with ⟨_, hAnd⟩
              rcases eo_and_true hAnd with ⟨hFalse, _⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hFalse
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
              · rcases hOneBranch with ⟨hOneEq, hAnd⟩
                rcases eo_and_true hAnd with ⟨_, hSimple⟩
                have hN1Nonneg : 0 <= z1 :=
                  int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
                have hZMEq :
                    zm = (1 : native_Int) :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hOneEq) hMEval
                    (numeral_int_eval M 1)
                rw [hZn, hZMEq]
                have hPos := native_str_from_int_len_pos_of_nonneg z1 hN1Nonneg
                have hNatPos : 0 < (native_str_from_int z1).length :=
                  Int.ofNat_lt.mp hPos
                exact Int.ofNat_le.mpr hNatPos
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_from_int_len_false n1 m hL1Branch
          rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
            ⟨z1, hN1Int, hN1Eval, hZn⟩
          let succN :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
                (Term.Numeral 0))
          have hSuccEval :
              __smtx_model_eval M (__eo_to_smt succN) =
                SmtValue.Numeral (z1 + 1) := by
            simpa [succN] using
              plus_trailing_zero_int_eval M n1 (Term.Numeral 1) z1 1
                hN1Eval (numeral_int_eval M 1)
          rcases eo_ite_true hIte with hSuccBranch | hRest
          · rcases hSuccBranch with ⟨hSuccEq, hAnd⟩
            rcases eo_and_true hAnd with ⟨_, hSimple⟩
            have hN1Nonneg : 0 <= z1 :=
              int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
            have hZMEq :
                zm = z1 + 1 :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hSuccEq) hMEval hSuccEval
            rw [hZn, hZMEq]
            exact native_str_from_int_len_le_succ z1 hN1Nonneg
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hNBranch | hRest2
            · rcases hNBranch with ⟨hNEq, hAnd⟩
              rcases eo_and_true hAnd with ⟨_, hPred⟩
              have hN1Pos : 0 < z1 :=
                int_pos_of_simple_gt_zero_true M hM n1 z1 hN1Int hN1Eval hPred
              have hZMEq :
                  zm = z1 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hNEq) hMEval hN1Eval
              rw [hZn, hZMEq]
              exact native_str_from_int_len_le_self_of_pos z1 hN1Pos
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
              · rcases hOneBranch with ⟨_, hAnd⟩
                rcases eo_and_true hAnd with ⟨hFalse, _⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len) s, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases s with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not] at hL1Branch
                  case str_from_int =>
                    exact str_from_int_len_l1_true_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not]
                        exact hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;>
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not] at hL1Branch
                          case str_substr =>
                            exact str_substr_len_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not, native_not]
                                exact hL1Branch)
                          case str_replace =>
                            exact str_replace_len_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not, native_not]
                                exact hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len] at hL1Branch
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases s with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not] at hL1Branch
                  case str_from_int =>
                    exact str_from_int_len_l1_false_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not]
                        exact hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;>
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not] at hL1Branch
                          case str_substr =>
                            exact str_substr_len_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not, native_not]
                                exact hL1Branch)
                          case str_replace =>
                            exact str_replace_len_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not, native_not]
                                exact hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len] at hL1Branch
  | n, m, zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases n with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not] at hL1Branch
                  case str_len =>
                    exact str_len_l1_true_order M hM x m zn zm
                      hNInt hMInt hNEval hMEval
                      (by
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not]
                        exact hL1Branch)
                  case str_to_int =>
                    exact str_to_int_l1_true_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx] using
                          hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;> try
                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                      case mult =>
                        cases x with
                        | Apply xf xArg =>
                            cases xf with
                            | Apply xg n3 =>
                                cases xg with
                                | UOp xop =>
                                    cases xop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx]
                                        at hL1Branch
                                    case mult =>
                                      cases xArg with
                                      | Numeral k =>
                                          by_cases hk : k = (1 : native_Int)
                                          · subst k
                                            cases m with
                                            | Apply mf mArg =>
                                                cases mf with
                                                | Apply mg n1' =>
                                                    cases mg with
                                                    | UOp mop =>
                                                        cases mop <;> try
                                                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                        next =>
                                                          cases mArg with
                                                          | Apply mf2 mArg2 =>
                                                              cases mf2 with
                                                              | Apply mg2 n5 =>
                                                                  cases mg2 with
                                                                  | UOp mop2 =>
                                                                      cases mop2 <;> try
                                                                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                                      next =>
                                                                        cases mArg2 with
                                                                        | Numeral k2 =>
                                                                            by_cases hk2 : k2 = (1 : native_Int)
                                                                            · subst k2
                                                                              have hReq :
                                                                                  __eo_requires (__eo_eq y n1')
                                                                                      (Term.Boolean true)
                                                                                      (__eo_ite (__eo_is_neg y)
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean false))
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean true))) =
                                                                                    Term.Boolean true := by
                                                                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                                                                  __eo_not, native_not, SmtEval.native_not]
                                                                                  using hL1Branch
                                                                              rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
                                                                              have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
                                                                              rcases mult_int_eval_decomp M hM y
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3)
                                                                                    (Term.Numeral 1))
                                                                                  zn hNInt hNEval with
                                                                                ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
                                                                              rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1)
                                                                                  zx1 hX1Int hX1Eval with
                                                                                ⟨zx, zOneX, hXInt, _hOneXInt, hXEval,
                                                                                  hOneXEval, hZx1⟩
                                                                              have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
                                                                              have hZx1' : zx1 = zx := by
                                                                                simpa [hOneX] using hZx1
                                                                              rcases mult_int_eval_decomp M hM n1'
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5)
                                                                                    (Term.Numeral 1))
                                                                                  zm hMInt hMEval with
                                                                                ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
                                                                              rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1)
                                                                                  zy1 hY1Int hY1Eval with
                                                                                ⟨zy, zOneY, hYInt, _hOneYInt, hYEval,
                                                                                  hOneYEval, hZy1⟩
                                                                              have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
                                                                              have hZy1' : zy1 = zy := by
                                                                                simpa [hOneY] using hZy1
                                                                              have hCoeffEq :
                                                                                  zc = zc' :=
                                                                                int_eval_eq_of_term_eq M hCoeffEqTerms hCEval
                                                                                  hC'Eval
                                                                              rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
                                                                              · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNeg : zc < 0 :=
                                                                                  int_eval_lt_zero_of_eo_is_neg_true M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zx ≤ zy :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).2 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonpos_left
                                                                                  (Int.le_of_lt hCNeg) hXY
                                                                              · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNonneg : 0 <= zc :=
                                                                                  int_eval_nonneg_of_eo_is_neg_false M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zy ≤ zx :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).1 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonneg_left hXY
                                                                                  hCNonneg
                                                                            · simp [__eo_l_1___str_arith_entail_is_approx,hk2]
                                                                                at hL1Branch
                                                                        | _ =>
                                                                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                                  | _ =>
                                                                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                              | _ =>
                                                                  simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                          | _ =>
                                                              simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                    | _ =>
                                                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                | _ =>
                                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                            | _ =>
                                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                          · simp [__eo_l_1___str_arith_entail_is_approx,hk] at hL1Branch
                                      | _ =>
                                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                      case plus =>
                        cases m with
                        | Apply mf mx =>
                            cases mf with
                            | Apply mg my =>
                                cases mg with
                                | UOp mop =>
                                    cases mop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                    case plus =>
                                      have hAnd :
                                          __eo_and
                                              (__str_arith_entail_is_approx y my
                                                (Term.Boolean true))
                                              (__str_arith_entail_is_approx x mx
                                                (Term.Boolean true)) =
                                            Term.Boolean true := by
                                        simpa [__eo_l_1___str_arith_entail_is_approx]
                                          using hL1Branch
                                      rcases eo_and_true hAnd with ⟨hA, hB⟩
                                      rcases plus_int_eval_decomp M hM y x zn hNInt hNEval with
                                        ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
                                      rcases plus_int_eval_decomp M hM my mx zm hMInt hMEval with
                                        ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
                                      have h13 :
                                          z3 ≤ z1 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM y my z1 z3 hN1Int hN3Int hN1Eval
                                          hN3Eval).1 hA
                                      have h24 :
                                          z4 ≤ z2 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM x mx z2 z4 hN2Int hN4Int hN2Eval
                                          hN4Eval).1 hB
                                      rw [hZn, hZm]
                                      calc
                                        z3 + z4 ≤ z1 + z4 :=
                                          Int.add_le_add_right h13 z4
                                        _ ≤ z1 + z2 := Int.add_le_add_left h24 z1
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __eo_not,SmtEval.native_not] at hL1Branch
                          case str_indexof =>
                            exact str_indexof_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __eo_not, native_not, SmtEval.native_not] using
                                  hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases n with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                  case str_len =>
                    exact str_len_l1_false_order M hM x m zn zm
                      hNInt hMInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
                  case str_to_int =>
                    exact False.elim
                      (str_to_int_l1_false_order x m
                        (by
                          simpa [__eo_l_1___str_arith_entail_is_approx] using
                            hL1Branch))
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;> try
                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                      case mult =>
                        cases x with
                        | Apply xf xArg =>
                            cases xf with
                            | Apply xg n3 =>
                                cases xg with
                                | UOp xop =>
                                    cases xop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx]
                                        at hL1Branch
                                    case mult =>
                                      cases xArg with
                                      | Numeral k =>
                                          by_cases hk : k = (1 : native_Int)
                                          · subst k
                                            cases m with
                                            | Apply mf mArg =>
                                                cases mf with
                                                | Apply mg n1' =>
                                                    cases mg with
                                                    | UOp mop =>
                                                        cases mop <;> try
                                                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                        next =>
                                                          cases mArg with
                                                          | Apply mf2 mArg2 =>
                                                              cases mf2 with
                                                              | Apply mg2 n5 =>
                                                                  cases mg2 with
                                                                  | UOp mop2 =>
                                                                      cases mop2 <;> try
                                                                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                                      next =>
                                                                        cases mArg2 with
                                                                        | Numeral k2 =>
                                                                            by_cases hk2 : k2 = (1 : native_Int)
                                                                            · subst k2
                                                                              have hReq :
                                                                                  __eo_requires (__eo_eq y n1')
                                                                                      (Term.Boolean true)
                                                                                      (__eo_ite (__eo_is_neg y)
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean true))
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean false))) =
                                                                                    Term.Boolean true := by
                                                                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                                                                  __eo_not, native_not, SmtEval.native_not]
                                                                                  using hL1Branch
                                                                              rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
                                                                              have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
                                                                              rcases mult_int_eval_decomp M hM y
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3)
                                                                                    (Term.Numeral 1))
                                                                                  zn hNInt hNEval with
                                                                                ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
                                                                              rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1)
                                                                                  zx1 hX1Int hX1Eval with
                                                                                ⟨zx, zOneX, hXInt, _hOneXInt, hXEval,
                                                                                  hOneXEval, hZx1⟩
                                                                              have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
                                                                              have hZx1' : zx1 = zx := by
                                                                                simpa [hOneX] using hZx1
                                                                              rcases mult_int_eval_decomp M hM n1'
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5)
                                                                                    (Term.Numeral 1))
                                                                                  zm hMInt hMEval with
                                                                                ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
                                                                              rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1)
                                                                                  zy1 hY1Int hY1Eval with
                                                                                ⟨zy, zOneY, hYInt, _hOneYInt, hYEval,
                                                                                  hOneYEval, hZy1⟩
                                                                              have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
                                                                              have hZy1' : zy1 = zy := by
                                                                                simpa [hOneY] using hZy1
                                                                              have hCoeffEq :
                                                                                  zc = zc' :=
                                                                                int_eval_eq_of_term_eq M hCoeffEqTerms hCEval
                                                                                  hC'Eval
                                                                              rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
                                                                              · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNeg : zc < 0 :=
                                                                                  int_eval_lt_zero_of_eo_is_neg_true M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zy ≤ zx :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).1 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonpos_left
                                                                                  (Int.le_of_lt hCNeg) hXY
                                                                              · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNonneg : 0 <= zc :=
                                                                                  int_eval_nonneg_of_eo_is_neg_false M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zx ≤ zy :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).2 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonneg_left hXY
                                                                                  hCNonneg
                                                                            · simp [__eo_l_1___str_arith_entail_is_approx,hk2]
                                                                                at hL1Branch
                                                                        | _ =>
                                                                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                                  | _ =>
                                                                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                              | _ =>
                                                                  simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                          | _ =>
                                                              simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                    | _ =>
                                                        simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                                | _ =>
                                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                            | _ =>
                                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                          · simp [__eo_l_1___str_arith_entail_is_approx,hk] at hL1Branch
                                      | _ =>
                                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                      case plus =>
                        cases m with
                        | Apply mf mx =>
                            cases mf with
                            | Apply mg my =>
                                cases mg with
                                | UOp mop =>
                                    cases mop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                                    case plus =>
                                      have hAnd :
                                          __eo_and
                                              (__str_arith_entail_is_approx y my
                                                (Term.Boolean false))
                                              (__str_arith_entail_is_approx x mx
                                                (Term.Boolean false)) =
                                            Term.Boolean true := by
                                        simpa [__eo_l_1___str_arith_entail_is_approx]
                                          using hL1Branch
                                      rcases eo_and_true hAnd with ⟨hA, hB⟩
                                      rcases plus_int_eval_decomp M hM y x zn hNInt hNEval with
                                        ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
                                      rcases plus_int_eval_decomp M hM my mx zm hMInt hMEval with
                                        ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
                                      have h13 :
                                          z1 ≤ z3 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM y my z1 z3 hN1Int hN3Int hN1Eval
                                          hN3Eval).2 hA
                                      have h24 :
                                          z2 ≤ z4 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM x mx z2 z4 hN2Int hN4Int hN2Eval
                                          hN4Eval).2 hB
                                      rw [hZn, hZm]
                                      calc
                                        z1 + z2 ≤ z3 + z2 :=
                                          Int.add_le_add_right h13 z2
                                        _ ≤ z3 + z4 := Int.add_le_add_left h24 z3
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __eo_not,SmtEval.native_not] at hL1Branch
                          case str_indexof =>
                            exact str_indexof_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __eo_not, native_not, SmtEval.native_not] using
                                  hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx] at hL1Branch

private theorem str_arith_entail_is_approx_int_eval_order
    (M : SmtModel) (hM : model_wf M) :
    (n m isUnder : Term) -> (zn zm : native_Int) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
      __str_arith_entail_is_approx n m isUnder = Term.Boolean true ->
      (isUnder = Term.Boolean true -> zm ≤ zn) ∧
        (isUnder = Term.Boolean false -> zn ≤ zm)
  | n, m, isUnder, zn, zm, hNInt, hMInt, hNEval, hMEval, hApprox => by
      constructor
      · intro hUnder
        subst isUnder
        exact (str_arith_entail_is_approx_int_eval_order_bool M hM n m zn zm
          hNInt hMInt hNEval hMEval).1 hApprox
      · intro hUnder
        subst isUnder
        exact (str_arith_entail_is_approx_int_eval_order_bool M hM n m zn zm
          hNInt hMInt hNEval hMEval).2 hApprox

private theorem str_arith_entail_is_approx_int_denote_order
    (M : SmtModel) (hM : model_wf M) :
    (n m isUnder : Term) -> (qn qm : native_Rat) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __str_arith_entail_is_approx n m isUnder = Term.Boolean true ->
      arith_poly_norm_atom_denote_real M n = SmtValue.Rational qn ->
      arith_poly_norm_atom_denote_real M m = SmtValue.Rational qm ->
      (isUnder = Term.Boolean true -> qm ≤ qn) ∧
        (isUnder = Term.Boolean false -> qn ≤ qm)
  | n, m, isUnder, qn, qm, hNInt, hMInt, hApprox, hNDen, hMDen => by
      rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
      rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
      have hQn : qn = native_to_real zn := by
        have h :
            SmtValue.Rational (native_to_real zn) = SmtValue.Rational qn := by
          simpa [arith_poly_norm_atom_denote_real, hNEval, __smtx_to_real_coerce] using hNDen
        simpa using h.symm
      have hQm : qm = native_to_real zm := by
        have h :
            SmtValue.Rational (native_to_real zm) = SmtValue.Rational qm := by
          simpa [arith_poly_norm_atom_denote_real, hMEval, __smtx_to_real_coerce] using hMDen
        simpa using h.symm
      have hOrder :=
        str_arith_entail_is_approx_int_eval_order M hM n m isUnder zn zm
          hNInt hMInt hNEval hMEval hApprox
      constructor
      · intro hUnder
        rw [hQm, hQn]
        exact (native_to_real_le_iff zm zn).2 (hOrder.1 hUnder)
      · intro hOver
        rw [hQn, hQm]
        exact (native_to_real_le_iff zn zm).2 (hOrder.2 hOver)

private theorem arith_string_pred_safe_approx_left_true
    (M : SmtModel) (hM : model_wf M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) ->
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) ->
  __str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
    Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) true := by
  intro hNBool hMBool hApprox hSimple
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type n hNBool
  have hMInt : __smtx_typeof (__eo_to_smt m) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type m hMBool
  rcases arith_poly_norm_atom_denote_real_rational_of_smt_arith_type
      M hM n (Or.inl hNInt) with
    ⟨qn, hNDen⟩
  rcases arith_poly_norm_atom_denote_real_rational_of_smt_arith_type
      M hM m (Or.inl hMInt) with
    ⟨qm, hMDen⟩
  have hMTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) true :=
    arith_string_pred_simple_geq_true M hM m (Term.Numeral 0) hMBool hSimple
  have hMEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) true).mp
        hMTrue with
    | intro_true _ hEval => exact hEval
  have hqmNonneg : 0 ≤ qm := by
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hMInt])
    rcases int_value_canonical (by simpa [hMInt] using hEvalMTy) with ⟨zm, hEvalM⟩
    have hDenEq : native_to_real zm = qm := by
      have h :
          SmtValue.Rational (native_to_real zm) = SmtValue.Rational qm := by
        simpa [arith_poly_norm_atom_denote_real, hEvalM, __smtx_to_real_coerce] using hMDen
      simpa using h
    have hZle : native_zleq 0 zm = true := by
      have hZeroEval :
          __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
        rw [__smtx_model_eval.eq_2]
      rw [show
          __eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
            SmtTerm.geq (__eo_to_smt m) (SmtTerm.Numeral 0) by rfl] at hMEval
      rw [__smtx_model_eval.eq_20, hEvalM, hZeroEval] at hMEval
      simpa [__smtx_model_eval_geq, __smtx_model_eval_leq] using hMEval
    have hzmNonneg : (0 : Int) ≤ zm := by
      simpa [native_zleq, SmtEval.native_zleq] using hZle
    have hqm' : (0 : Rat) ≤ native_to_real zm := by
      dsimp [native_to_real, native_mk_rational]
      rw [rat_div_one_intCast zm]
      exact_mod_cast hzmNonneg
    simpa [hDenEq] using hqm'
  have hOrder :=
    (str_arith_entail_is_approx_int_denote_order M hM n m (Term.Boolean true) qn qm
      hNInt hMInt hApprox hNDen hMDen).1 rfl
  have hqnNonneg : 0 ≤ qn := by
    calc
      (0 : Rat) ≤ qm := hqmNonneg
      _ ≤ qn := hOrder
  have hNEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) =
        SmtValue.Boolean true :=
    geq_zero_eval_true_of_int_denote_nonneg M hM n qn hNInt hNDen hqnNonneg
  exact RuleProofs.eo_interprets_of_bool_eval M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) true hNBool hNEval

theorem arith_string_pred_entail_formula_true
    (M : SmtModel) (hM : model_wf M) (n : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Boolean true)) ->
  __str_arith_entail_simple_rec (__get_arith_poly_norm n) = Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Boolean true)) true := by
  intro hEqBool hSimple
  let geqTerm := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)
  have hGeqBool : RuleProofs.eo_has_bool_type geqTerm := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        geqTerm (Term.Boolean true) (by simpa [geqTerm] using hEqBool) with
      ⟨hTy, _hNonNone⟩
    unfold RuleProofs.eo_has_bool_type
    rw [hTy]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_typeof.eq_1]
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type n hGeqBool
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        arith_poly_norm_atom_denote_real M n :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM n (Or.inl hNInt)
  rcases arith_poly_norm_atom_denote_real_rational_of_smt_arith_type
      M hM n (Or.inl hNInt) with
    ⟨q, hAtomDenote⟩
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        SmtValue.Rational q := by
    rw [hDenote, hAtomDenote]
  have hqNonneg : 0 ≤ q :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm n) q hSimple hPolyDenote
  have hGeqEval :
      __smtx_model_eval M (__eo_to_smt geqTerm) = SmtValue.Boolean true := by
    simpa [geqTerm] using
      geq_zero_eval_true_of_int_denote_nonneg M hM n q hNInt hAtomDenote hqNonneg
  apply RuleProofs.eo_interprets_eq_of_rel M geqTerm (Term.Boolean true)
    (by simpa [geqTerm] using hEqBool)
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hGeqEval]
  rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
  rw [__smtx_model_eval.eq_1]
  simp [__smtx_model_eval_eq, native_veq]

theorem arith_string_pred_safe_approx_formula_true
    (M : SmtModel) (hM : model_wf M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) ->
  __str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
    Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) true := by
  intro hFormulaBool hApprox hSimple
  let geqN := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)
  let geqM := Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type geqN geqM
      (by simpa [geqN, geqM] using hFormulaBool) with
    ⟨hSameTy, hGeqNNN⟩
  have hGeqMNN : __smtx_typeof (__eo_to_smt geqM) ≠ SmtType.None := by
    rw [← hSameTy]
    exact hGeqNNN
  have hGeqNBool : RuleProofs.eo_has_bool_type geqN := by
    exact geq_has_bool_type_of_non_none n (Term.Numeral 0)
      (by simpa [geqN] using hGeqNNN)
  have hGeqMBool : RuleProofs.eo_has_bool_type geqM := by
    exact geq_has_bool_type_of_non_none m (Term.Numeral 0)
      (by simpa [geqM] using hGeqMNN)
  have hNTrue : eo_interprets M geqN true := by
    simpa [geqN, geqM] using
      arith_string_pred_safe_approx_left_true M hM n m hGeqNBool hGeqMBool
        hApprox hSimple
  have hMTrue : eo_interprets M geqM true := by
    simpa [geqM] using
      arith_string_pred_simple_geq_true M hM m (Term.Numeral 0) hGeqMBool hSimple
  have hEvalN :
      __smtx_model_eval M (__eo_to_smt geqN) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqN true).mp hNTrue with
    | intro_true _ hEval => exact hEval
  have hEvalM :
      __smtx_model_eval M (__eo_to_smt geqM) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqM true).mp hMTrue with
    | intro_true _ hEval => exact hEval
  apply RuleProofs.eo_interprets_eq_of_rel M geqN geqM
    (by simpa [geqN, geqM] using hFormulaBool)
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hEvalN, hEvalM]
  simp [__smtx_model_eval_eq, native_veq]
