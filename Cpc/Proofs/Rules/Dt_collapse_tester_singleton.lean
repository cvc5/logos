module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_eq_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    T = U := by
  intro hReq
  by_cases hEq : native_teq T U = true
  · simpa [native_teq] using hEq
  · exfalso
    apply hReq
    simp [__eo_requires, native_ite, hEq]

private theorem eo_requires_eq_result_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    __eo_requires T U V = V := by
  intro hReq
  by_cases hEq : native_teq T U = true
  · by_cases hOk : native_not (native_teq T Term.Stuck) = true
    · simp [__eo_requires, native_ite, hEq, hOk]
    · simp [__eo_requires, native_ite, hEq, hOk] at hReq
  · simp [__eo_requires, native_ite, hEq] at hReq

private theorem eq_args_of_prog_dt_collapse_tester_singleton_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_collapse_tester_singleton a1 ≠ Term.Stuck ->
  ∃ c t,
    a1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true) ∧
    __eo_list_len Term.__eo_List_cons
        (__dt_get_constructors (__eo_typeof t)) =
      Term.Numeral 1 ∧
    __eo_prog_dt_collapse_tester_singleton a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f b =>
      cases b with
      | Boolean bv =>
          cases bv with
          | true =>
              cases f with
              | Apply g lhs =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          cases lhs with
                          | Apply tester t =>
                              cases tester with
                              | UOp1 op c =>
                                  cases op with
                                  | is =>
                                      let body :=
                                        Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                                          (Term.Apply (Term.UOp1 UserOp1.is c) t))
                                          (Term.Boolean true)
                                      have hReq :
                                          __eo_requires
                                              (__eo_list_len Term.__eo_List_cons
                                                (__dt_get_constructors (__eo_typeof t)))
                                              (Term.Numeral 1) body ≠
                                            Term.Stuck := by
                                        simpa [__eo_prog_dt_collapse_tester_singleton,
                                          body] using hProg
                                      have hGuard :
                                          __eo_list_len Term.__eo_List_cons
                                              (__dt_get_constructors (__eo_typeof t)) =
                                            Term.Numeral 1 :=
                                        eo_requires_eq_of_ne_stuck_local
                                          (__eo_list_len Term.__eo_List_cons
                                            (__dt_get_constructors (__eo_typeof t)))
                                          (Term.Numeral 1) body hReq
                                      have hProgEq :
                                          __eo_prog_dt_collapse_tester_singleton body =
                                            body := by
                                        simpa [__eo_prog_dt_collapse_tester_singleton,
                                          body] using
                                          eo_requires_eq_result_of_ne_stuck_local
                                            (__eo_list_len Term.__eo_List_cons
                                              (__dt_get_constructors (__eo_typeof t)))
                                            (Term.Numeral 1) body hReq
                                      exact ⟨c, t, rfl, hGuard, hProgEq⟩
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | false =>
              cases f <;> simp [__eo_prog_dt_collapse_tester_singleton] at hProg
      | _ =>
          cases f <;> simp [__eo_prog_dt_collapse_tester_singleton] at hProg
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_collapse_tester_singleton_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_collapse_tester_singleton a1) = Term.Bool ->
  __eo_prog_dt_collapse_tester_singleton a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_collapse_tester_singleton a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_collapse_tester_singleton_ne_stuck a1 hProg with
    ⟨_c, _t, _hEq, _hGuard, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_collapse_tester_singleton_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_tester_singleton a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_collapse_tester_singleton a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_collapse_tester_singleton a1 = a1 :=
    prog_dt_collapse_tester_singleton_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem tester_ctor_translation_of_non_none
    (c t : Term) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is c) t)) ≠
      SmtType.None ->
  ∃ s d i, __eo_to_smt c = SmtTerm.DtCons s d i := by
  intro hNN
  cases hC : __eo_to_smt c with
  | DtCons s d i =>
      exact ⟨s, d, i, rfl⟩
  | _ =>
      exfalso
      apply hNN
      change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c))
              (__eo_to_smt t)) =
          SmtType.None
      rw [hC]
      simp [__eo_to_smt_tester, TranslationProofs.typeof_apply_none_eq]

private theorem nat_eq_one_of_int_ofNat_eq_one
    {n : Nat}
    (h : Int.ofNat n = 1) :
    n = 1 := by
  change Int.ofNat n = Int.ofNat 1 at h
  exact Int.ofNat.inj h

private theorem nat_eq_zero_of_lt_one
    {n : Nat}
    (h : n < 1) :
    n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      have h0 : n < 0 := Nat.succ_lt_succ_iff.mp h
      exact False.elim (Nat.not_lt_zero n h0)

private theorem dt_collapse_tester_singleton_sound
    (M : SmtModel) (hM : model_wf M) (c t : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true)) ->
  __eo_list_len Term.__eo_List_cons
      (__dt_get_constructors (__eo_typeof t)) =
    Term.Numeral 1 ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true)) true := by
  intro hBool hLen
  let lhs := Term.Apply (Term.UOp1 UserOp1.is c) t
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      lhs (Term.Boolean true) hBool
  have hCtorTrans :
      ∃ s d i, __eo_to_smt c = SmtTerm.DtCons s d i :=
    tester_ctor_translation_of_non_none c t hTypes.2
  rcases hCtorTrans with ⟨cs, cd, ci, hCTrans⟩
  have hLeftTranslate :
      __eo_to_smt lhs =
        SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt t) := by
    change
      SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt c)) (__eo_to_smt t) =
        SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt t)
    rw [hCTrans]
    simp [__eo_to_smt_tester]
  have hLeftNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtTester cs cd ci) (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    rw [← hLeftTranslate]
    exact hTypes.2
  have hTType :
      __smtx_typeof (__eo_to_smt t) = SmtType.Datatype cs cd :=
    dt_tester_arg_datatype_of_non_none hLeftNN
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hTType]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Datatype cs cd := by
    simpa [hTType] using
      Smtm.smt_model_eval_preserves_type_of_non_none
        M hM (__eo_to_smt t) hTNN
  have hCtorNN :
      __smtx_typeof_dt_cons_rec (SmtType.Datatype cs cd)
          (__smtx_dt_resolve (__smtx_dd_lookup cs cd) cd) ci ≠
        SmtType.None :=
    dt_tester_ctor_type_non_none_of_non_none hLeftNN
  have hCiLtSub :
      ci <
        smtDatatypeNumCtors
          (__smtx_dt_resolve (__smtx_dd_lookup cs cd) cd) :=
    smt_typeof_dt_cons_rec_non_none_implies_lt_ctors
      (SmtType.Datatype cs cd) hCtorNN
  have hCiLt : ci < smtDatatypeNumCtors (__smtx_dd_lookup cs cd) := by
    simpa [smtDatatypeNumCtors_resolve cd (__smtx_dd_lookup cs cd)] using hCiLtSub
  rcases datatype_value_head_of_type hEvalTy with ⟨idx, hHead⟩
  have hIdxLt : idx < smtDatatypeNumCtors (__smtx_dd_lookup cs cd) :=
    datatype_head_index_lt hHead hEvalTy
  rcases TranslationProofs.eo_to_smt_eq_dt_cons_cases c cs cd ci hCTrans with
    hDt | hTupleUnit
  · rcases hDt with ⟨d0, hCd, hCEq, hReserved⟩
    subst c
    subst cd
    have hEoTType :
        __eo_to_smt_type (__eo_typeof t) =
          SmtType.Datatype cs (__eo_to_smt_datatype_decl d0) :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type t hTType (by simp)
    have hNameNe : cs ≠ (native_string_lit "@Tuple") :=
      TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved
    rcases TranslationProofs.eo_to_smt_type_eq_datatype_non_tuple
        hNameNe hEoTType with
      ⟨dt, hTTypeEo, hDtTrans⟩
    have hLenDt :
        __eo_list_len Term.__eo_List_cons
            (__dt_get_constructors (__eo_typeof t)) =
          Term.Numeral
            (Int.ofNat (eoDatatypeNumCtors (__eo_dd_lookup cs dt))) := by
      rw [hTTypeEo]
      exact eo_list_len_dt_get_constructors_datatype cs dt
    have hCtorCountEo : eoDatatypeNumCtors (__eo_dd_lookup cs dt) = 1 := by
      have hNum :
          Term.Numeral
              (Int.ofNat (eoDatatypeNumCtors (__eo_dd_lookup cs dt))) =
            Term.Numeral 1 := by
        rw [← hLenDt]
        exact hLen
      injection hNum with hInt
      exact nat_eq_one_of_int_ofNat_eq_one hInt
    have hCtorCountSmt :
        smtDatatypeNumCtors
            (__smtx_dd_lookup cs (__eo_to_smt_datatype_decl d0)) = 1 := by
      calc
        smtDatatypeNumCtors
            (__smtx_dd_lookup cs (__eo_to_smt_datatype_decl d0)) =
            smtDatatypeNumCtors
              (__smtx_dd_lookup cs (__eo_to_smt_datatype_decl dt)) := by
          rw [hDtTrans]
        _ = smtDatatypeNumCtors
              (__eo_to_smt_datatype (__eo_dd_lookup cs dt)) := by
          rw [TranslationProofs.eo_to_smt_dd_lookup]
        _ = eoDatatypeNumCtors (__eo_dd_lookup cs dt) :=
          smtDatatypeNumCtors_eo_to_smt (__eo_dd_lookup cs dt)
        _ = 1 := hCtorCountEo
    have hCiZero : ci = native_nat_zero := by
      exact nat_eq_zero_of_lt_one (by
        simpa [hCtorCountSmt] using hCiLt)
    have hIdxZero : idx = native_nat_zero := by
      exact nat_eq_zero_of_lt_one (by
        simpa [hCtorCountSmt] using hIdxLt)
    have hHeadTarget :
        __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
          SmtValue.DtCons cs (__eo_to_smt_datatype_decl d0) ci := by
      subst idx
      subst ci
      exact hHead
    have hLeftEval :
        __smtx_model_eval M (__eo_to_smt lhs) =
          SmtValue.Boolean true := by
      rw [hLeftTranslate]
      simp [__smtx_model_eval, __smtx_model_eval_dt_tester,
        hHeadTarget, native_veq]
    apply RuleProofs.eo_interprets_eq_of_rel M lhs (Term.Boolean true)
    · exact hBool
    · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
      rw [hLeftEval]
      simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq]
  · rcases hTupleUnit with ⟨hCs, hCd, hCi, hCEq⟩
    subst c
    subst cs
    subst cd
    subst ci
    have hHeadUnit :
        __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
          SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
            native_nat_zero :=
      unit_tuple_value_head_zero_of_type hEvalTy
    have hLeftEval :
        __smtx_model_eval M (__eo_to_smt lhs) =
          SmtValue.Boolean true := by
      rw [hLeftTranslate]
      simp [__smtx_model_eval, __smtx_model_eval_dt_tester,
        hHeadUnit, native_veq]
    apply RuleProofs.eo_interprets_eq_of_rel M lhs (Term.Boolean true)
    · exact hBool
    · rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
      rw [hLeftEval]
      simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq]

private theorem facts___eo_prog_dt_collapse_tester_singleton_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_tester_singleton a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_collapse_tester_singleton a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_collapse_tester_singleton a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_collapse_tester_singleton_ne_stuck a1 hProg with
    ⟨c, t, hA1Eq, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true)) := by
    subst hA1Eq
    have hA1Ty :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true)) =
          Term.Bool := by
      simpa [hProgEq] using hResultTy
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.is c) t)) (Term.Boolean true))
      hA1Trans hA1Ty
  rw [hProgEq]
  rw [hA1Eq]
  exact dt_collapse_tester_singleton_sound M hM c t hBool hGuard

public theorem cmd_step_dt_collapse_tester_singleton_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_tester_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_collapse_tester_singleton args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_tester_singleton args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.dt_collapse_tester_singleton args premises ≠
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
              have hA1TransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_collapse_tester_singleton a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_dt_collapse_tester_singleton a1) true
                exact facts___eo_prog_dt_collapse_tester_singleton_impl
                  M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_collapse_tester_singleton a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_collapse_tester_singleton a1)
                  (typed___eo_prog_dt_collapse_tester_singleton_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
