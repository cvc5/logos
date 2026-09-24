module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_has_bool_type_imp_left (A B : Term) :
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp A) B) ->
  RuleProofs.eo_has_bool_type A := by
  intro hImp
  unfold RuleProofs.eo_has_bool_type at hImp ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hImp
  have hNN : term_has_non_none_type (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hImp]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

private theorem eo_has_bool_type_imp_right (A B : Term) :
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp A) B) ->
  RuleProofs.eo_has_bool_type B := by
  intro hImp
  unfold RuleProofs.eo_has_bool_type at hImp ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hImp
  have hNN : term_has_non_none_type (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hImp]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

private theorem eo_has_bool_type_imp_of_bool_args (A B : Term) :
  RuleProofs.eo_has_bool_type A ->
  RuleProofs.eo_has_bool_type B ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) = SmtType.Bool
  rw [typeof_imp_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_mk_apply_arg_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hx
  subst hx
  cases f <;> simp [__eo_mk_apply] at h

private theorem eo_mk_apply_fun_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    f ≠ Term.Stuck := by
  intro h hf
  subst hf
  simp [__eo_mk_apply] at h

private theorem typeof_or_eq_bool_right {A B : Term} :
    __eo_typeof_or A B = Term.Bool ->
    B = Term.Bool := by
  cases A <;> cases B <;> simp [__eo_typeof_or]

private theorem eo_interprets_false (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.Boolean false) false
  exact smt_interprets.intro_false M (SmtTerm.Boolean false)
    (by rw [__smtx_typeof.eq_1])
    (by rw [__smtx_model_eval.eq_1])

private theorem eo_interprets_imp_true_of_left_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A false ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hAFalse hBBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse ⊢
  change smt_interprets M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) true
  cases hAFalse with
  | intro_false hATy hAEval =>
      rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hBEval⟩
      refine smt_interprets.intro_true M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_imp_eq]
        simpa [hATy, hBBool, RuleProofs.eo_has_bool_type, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_10, hAEval, hBEval]
        cases b <;> simp [__smtx_model_eval_imp, __smtx_model_eval_or,
          __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

private theorem eo_interprets_imp_true_of_right_true
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hABool hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBTrue ⊢
  change smt_interprets M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) true
  cases hBTrue with
  | intro_true hBTy hBEval =>
      rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hAEval⟩
      refine smt_interprets.intro_true M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_imp_eq]
        simpa [hABool, hBTy, RuleProofs.eo_has_bool_type, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_10, hAEval, hBEval]
        cases a <;> simp [__smtx_model_eval_imp, __smtx_model_eval_or,
          __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

private theorem extract_antec_rec_target_ne_stuck (F C : Term) :
    __extract_antec_rec F C ≠ Term.Stuck ->
    C ≠ Term.Stuck := by
  intro h hC
  subst hC
  cases F <;> simp [__extract_antec_rec] at h

private theorem extract_antec_target_ne_stuck (F C : Term) :
    __extract_antec F C ≠ Term.Stuck ->
    C ≠ Term.Stuck := by
  intro h hC
  subst hC
  cases F <;> simp [__extract_antec] at h

private theorem eo_eq_false_of_ne_nonstuck (A B : Term) :
    A ≠ Term.Stuck ->
    B ≠ Term.Stuck ->
    A ≠ B ->
    __eo_eq A B = Term.Boolean false := by
  intro hANe hBNe hNe
  have hNe' : B ≠ A := by
    intro h
    exact hNe h.symm
  cases A <;> cases B <;>
    simp [__eo_eq, native_teq, hNe, hNe']
      at hANe hBNe hNe ⊢

private theorem extract_antec_rec_self (F : Term) :
    F ≠ Term.Stuck ->
    __extract_antec_rec F F = Term.Boolean true := by
  intro hFNe
  cases F <;> simp [__extract_antec_rec, __eo_eq, __eo_ite,
    native_ite, native_teq] at hFNe ⊢

private theorem extract_antec_rec_imp_ne (A B C : Term) :
    C ≠ Term.Stuck ->
    Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B ≠ C ->
    __extract_antec_rec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) C =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) A) (__extract_antec_rec B C) := by
  intro hCNe hNe
  have hNe' : ¬ C = Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B := by
    intro h
    exact hNe h.symm
  cases C <;> simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
    __eo_eq, __eo_ite, native_ite, native_teq, hNe'] at hCNe ⊢

private theorem extract_antec_imp_same (A C : Term) :
    C ≠ Term.Stuck ->
    __extract_antec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) C) C = A := by
  intro hCNe
  cases C <;> simp [__extract_antec, __eo_eq, __eo_ite,
    native_ite, native_teq] at hCNe ⊢

private theorem extract_antec_imp_ne (A D C : Term) :
    D ≠ Term.Stuck ->
    C ≠ Term.Stuck ->
    D ≠ C ->
    __extract_antec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) D) C =
      __extract_antec_rec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) D) C := by
  intro hDNe hCNe hNe
  have hEqFalse : __eo_eq D C = Term.Boolean false :=
    eo_eq_false_of_ne_nonstuck D C hDNe hCNe hNe
  simp [__extract_antec, __eo_l_1___extract_antec, __eo_ite, native_ite, native_teq,hEqFalse]

private theorem run_process_scope_false_eq (F : Term) :
    F ≠ Term.Stuck ->
    __run_process_scope F (Term.Boolean false) =
      __eo_mk_apply (Term.UOp UserOp.not) (__extract_antec F (Term.Boolean false)) := by
  intro hFNe
  cases F <;> simp [__run_process_scope] at hFNe ⊢

private theorem run_process_scope_nonfalse_eq (F C : Term) :
    F ≠ Term.Stuck ->
    C ≠ Term.Stuck ->
    C ≠ Term.Boolean false ->
    __run_process_scope F C =
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.imp) (__extract_antec F C)) C := by
  intro hFNe hCNe hCFalse
  cases F <;> cases C <;> simp [__run_process_scope] at hFNe hCNe hCFalse ⊢

private theorem eo_prog_process_scope_eq (C F : Term) :
    C ≠ Term.Stuck ->
    __eo_prog_process_scope C (Proof.pf F) = __run_process_scope F C := by
  intro hCNe
  cases C <;> simp [__eo_prog_process_scope] at hCNe ⊢

private theorem extract_antec_rec_bool :
    ∀ F C : Term,
      RuleProofs.eo_has_bool_type F ->
      __extract_antec_rec F C ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (__extract_antec_rec F C)
  | F, C, hFBool, hRecNe => by
      have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type F hFBool
      have hCNe : C ≠ Term.Stuck := extract_antec_rec_target_ne_stuck F C hRecNe
      by_cases hEq : F = C
      · subst C
        rw [extract_antec_rec_self F hFNe]
        exact RuleProofs.eo_has_bool_type_true
      · have hEq' : ¬ C = F := by
          intro h
          exact hEq h.symm
        cases F with
        | Apply f x =>
            cases f with
            | Apply g A =>
                cases g with
                | UOp op =>
                    cases op with
                    | imp =>
                        rw [extract_antec_rec_imp_ne A x C hCNe hEq] at hRecNe ⊢
                        have hRecTailNe : __extract_antec_rec x C ≠ Term.Stuck := by
                          exact eo_mk_apply_arg_ne_stuck _ _ hRecNe
                        have hABool : RuleProofs.eo_has_bool_type A :=
                          eo_has_bool_type_imp_left A x hFBool
                        have hXBool : RuleProofs.eo_has_bool_type x :=
                          eo_has_bool_type_imp_right A x hFBool
                        have hTailBool : RuleProofs.eo_has_bool_type (__extract_antec_rec x C) :=
                          extract_antec_rec_bool x C hXBool hRecTailNe
                        rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp)
                          (RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool)]
                        exact RuleProofs.eo_has_bool_type_and_of_bool_args A
                          (__extract_antec_rec x C) hABool hTailBool
                    | _ =>
                        simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                          __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                          at hRecNe
                | _ =>
                    simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                      __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                      at hRecNe
            | _ =>
                simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                  __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                  at hRecNe
        | Stuck =>
            exact False.elim (hFNe rfl)
        | _ =>
            simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
              __eo_eq, __eo_ite, native_ite, native_teq, hEq']
              at hRecNe
termination_by F C hFBool hRecNe => F

private theorem extract_antec_bool
    (F C : Term) :
    RuleProofs.eo_has_bool_type F ->
    __extract_antec F C ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__extract_antec F C) := by
  intro hFBool hExtNe
  have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type F hFBool
  have hCNe : C ≠ Term.Stuck := extract_antec_target_ne_stuck F C hExtNe
  cases F with
  | Apply f D =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  have hDBool : RuleProofs.eo_has_bool_type D :=
                    eo_has_bool_type_imp_right A D hFBool
                  have hDNe : D ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_bool_type D hDBool
                  by_cases hEq : D = C
                  · subst C
                    rw [extract_antec_imp_same A D hCNe]
                    exact eo_has_bool_type_imp_left A D hFBool
                  · rw [extract_antec_imp_ne A D C hDNe hCNe hEq] at hExtNe ⊢
                    exact extract_antec_rec_bool
                      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) D) C hFBool hExtNe
              | _ =>
                  simpa [__extract_antec, __eo_l_1___extract_antec] using
                    (extract_antec_rec_bool _ C hFBool
                      (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe))
          | _ =>
              simpa [__extract_antec, __eo_l_1___extract_antec] using
                (extract_antec_rec_bool _ C hFBool
                  (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe))
      | _ =>
          simpa [__extract_antec, __eo_l_1___extract_antec] using
            (extract_antec_rec_bool _ C hFBool
              (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe))
  | Stuck =>
      exact False.elim (hFNe rfl)
  | _ =>
      simpa [__extract_antec, __eo_l_1___extract_antec] using
        (extract_antec_rec_bool _ C hFBool
          (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe))

private theorem extract_antec_rec_sound
    (M : SmtModel) :
    ∀ F C : Term,
      eo_interprets M F true ->
      __extract_antec_rec F C ≠ Term.Stuck ->
      eo_interprets M (__extract_antec_rec F C) true ->
      eo_interprets M C true
  | F, C, hFTrue, hRecNe, hRecTrue => by
      have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_interprets_true M F hFTrue
      have hCNe : C ≠ Term.Stuck := extract_antec_rec_target_ne_stuck F C hRecNe
      by_cases hEq : F = C
      · subst C
        rw [extract_antec_rec_self F hFNe] at hRecTrue
        exact hFTrue
      · have hEq' : ¬ C = F := by
          intro h
          exact hEq h.symm
        cases F with
        | Apply f x =>
            cases f with
            | Apply g A =>
                cases g with
                | UOp op =>
                    cases op with
                    | imp =>
                        rw [extract_antec_rec_imp_ne A x C hCNe hEq] at hRecNe hRecTrue
                        have hRecTailNe : __extract_antec_rec x C ≠ Term.Stuck := by
                          exact eo_mk_apply_arg_ne_stuck _ _ hRecNe
                        have hTailBool : RuleProofs.eo_has_bool_type (__extract_antec_rec x C) :=
                          extract_antec_rec_bool x C
                            (eo_has_bool_type_imp_right A x
                              (RuleProofs.eo_has_bool_type_of_interprets_true M _ hFTrue))
                            hRecTailNe
                        have hTailNe : __extract_antec_rec x C ≠ Term.Stuck :=
                          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
                        have hStepApply :
                            __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) A)
                                (__extract_antec_rec x C) =
                              Term.Apply (Term.Apply (Term.UOp UserOp.and) A)
                                (__extract_antec_rec x C) :=
                          eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hTailNe
                        have hAndTrue :
                            eo_interprets M
                              (Term.Apply (Term.Apply (Term.UOp UserOp.and) A)
                                (__extract_antec_rec x C)) true := by
                          simpa [hStepApply] using hRecTrue
                        have hATrue : eo_interprets M A true :=
                          RuleProofs.eo_interprets_and_left M A (__extract_antec_rec x C)
                            hAndTrue
                        have hTailTrue : eo_interprets M (__extract_antec_rec x C) true :=
                          RuleProofs.eo_interprets_and_right M A (__extract_antec_rec x C)
                            hAndTrue
                        have hxTrue : eo_interprets M x true :=
                          RuleProofs.eo_interprets_imp_elim M A x hFTrue hATrue
                        exact extract_antec_rec_sound M x C hxTrue hRecTailNe hTailTrue
                    | _ =>
                        simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                          __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                          at hRecNe
                | _ =>
                    simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                      __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                      at hRecNe
            | _ =>
                simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
                  __eo_eq, __eo_ite, native_ite, native_teq, hEq']
                  at hRecNe
        | Stuck =>
            exact False.elim (hFNe rfl)
        | _ =>
            simp [__extract_antec_rec, __eo_l_1___extract_antec_rec,
              __eo_eq, __eo_ite, native_ite, native_teq, hEq']
              at hRecNe
termination_by F C hFTrue hRecNe hRecTrue => F

private theorem extract_antec_sound
    (M : SmtModel) (F C : Term) :
    eo_interprets M F true ->
    __extract_antec F C ≠ Term.Stuck ->
    eo_interprets M (__extract_antec F C) true ->
    eo_interprets M C true := by
  intro hFTrue hExtNe hExtTrue
  have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_interprets_true M F hFTrue
  have hCNe : C ≠ Term.Stuck := extract_antec_target_ne_stuck F C hExtNe
  cases F with
  | Apply f D =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  have hDBool : RuleProofs.eo_has_bool_type D :=
                    eo_has_bool_type_imp_right A D
                      (RuleProofs.eo_has_bool_type_of_interprets_true M _ hFTrue)
                  have hDNe : D ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_bool_type D hDBool
                  by_cases hEq : D = C
                  · subst C
                    rw [extract_antec_imp_same A D hCNe] at hExtTrue
                    exact RuleProofs.eo_interprets_imp_elim M A D hFTrue hExtTrue
                  · rw [extract_antec_imp_ne A D C hDNe hCNe hEq] at hExtNe hExtTrue
                    exact extract_antec_rec_sound M
                      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) D) C hFTrue
                      hExtNe hExtTrue
              | _ =>
                  exact extract_antec_rec_sound M _ C hFTrue
                    (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe)
                    (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtTrue)
          | _ =>
              exact extract_antec_rec_sound M _ C hFTrue
                (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe)
                (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtTrue)
      | _ =>
          exact extract_antec_rec_sound M _ C hFTrue
            (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe)
            (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtTrue)
  | Stuck =>
      exact False.elim (hFNe rfl)
  | _ =>
      exact extract_antec_rec_sound M _ C hFTrue
        (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtNe)
        (by simpa [__extract_antec, __eo_l_1___extract_antec] using hExtTrue)

private theorem run_process_scope_bool
    (F C : Term) :
    RuleProofs.eo_has_bool_type F ->
    RuleProofs.eo_has_smt_translation C ->
    __eo_typeof (__run_process_scope F C) = Term.Bool ->
    __run_process_scope F C ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__run_process_scope F C) := by
  intro hFBool hCTrans hRunTy hRunNe
  have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type F hFBool
  by_cases hCFalse : C = Term.Boolean false
  · subst C
    let A := __extract_antec F (Term.Boolean false)
    rw [run_process_scope_false_eq F hFNe] at hRunNe hRunTy ⊢
    have hExtNe : A ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck _ _ (by simpa [A] using hRunNe)
    have hABool : RuleProofs.eo_has_bool_type A :=
      extract_antec_bool F (Term.Boolean false) hFBool hExtNe
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe]
    exact RuleProofs.eo_has_bool_type_not_of_bool_arg A hABool
  · let A := __extract_antec F C
    have hCNe : C ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
    rw [run_process_scope_nonfalse_eq F C hFNe hCNe hCFalse] at hRunNe hRunTy ⊢
    have hInnerNe : __eo_mk_apply (Term.UOp UserOp.imp) A ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck _ _ hRunNe
    have hExtNe : A ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck _ _ hInnerNe
    have hABool : RuleProofs.eo_has_bool_type A :=
      extract_antec_bool F C hFBool hExtNe
    have hCTy : __eo_typeof C = Term.Bool := by
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hCNe] at hRunTy
      have hTy' :
          __eo_typeof_or (__eo_typeof A) (__eo_typeof C) = Term.Bool :=
        hRunTy
      exact typeof_or_eq_bool_right hTy'
    have hCBool : RuleProofs.eo_has_bool_type C :=
      RuleProofs.eo_typeof_bool_implies_has_bool_type C hCTrans hCTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hCNe]
    exact eo_has_bool_type_imp_of_bool_args A C hABool hCBool

private theorem run_process_scope_sound
    (M : SmtModel) (hM : model_wf M) (F C : Term) :
    eo_interprets M F true ->
    RuleProofs.eo_has_bool_type F ->
    RuleProofs.eo_has_smt_translation C ->
    __eo_typeof (__run_process_scope F C) = Term.Bool ->
    __run_process_scope F C ≠ Term.Stuck ->
    eo_interprets M (__run_process_scope F C) true := by
  intro hFTrue hFBool hCTrans hRunTy hRunNe
  have hFNe : F ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type F hFBool
  by_cases hCFalse : C = Term.Boolean false
  · subst C
    let A := __extract_antec F (Term.Boolean false)
    rw [run_process_scope_false_eq F hFNe] at hRunNe hRunTy ⊢
    have hExtNe : A ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck _ _ (by simpa [A] using hRunNe)
    have hABool : RuleProofs.eo_has_bool_type A :=
      extract_antec_bool F (Term.Boolean false) hFBool hExtNe
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe]
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
      ⟨a, hAEval⟩
    cases a with
    | false =>
        exact RuleProofs.eo_interprets_not_of_false M A
          (RuleProofs.eo_interprets_of_bool_eval M A false hABool hAEval)
    | true =>
        have hATrue : eo_interprets M A true :=
          RuleProofs.eo_interprets_of_bool_eval M A true hABool hAEval
        have hFalseTrue : eo_interprets M (Term.Boolean false) true :=
          extract_antec_sound M F (Term.Boolean false) hFTrue hExtNe hATrue
        exact False.elim
          ((RuleProofs.eo_interprets_true_not_false M (Term.Boolean false)
            hFalseTrue) (eo_interprets_false M))
  · let A := __extract_antec F C
    have hCNe : C ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
    rw [run_process_scope_nonfalse_eq F C hFNe hCNe hCFalse] at hRunNe hRunTy ⊢
    have hInnerNe : __eo_mk_apply (Term.UOp UserOp.imp) A ≠ Term.Stuck :=
      eo_mk_apply_fun_ne_stuck _ _ hRunNe
    have hExtNe : A ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck _ _ hInnerNe
    have hABool : RuleProofs.eo_has_bool_type A :=
      extract_antec_bool F C hFBool hExtNe
    have hCTy : __eo_typeof C = Term.Bool := by
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hCNe] at hRunTy
      have hTy' :
          __eo_typeof_or (__eo_typeof A) (__eo_typeof C) = Term.Bool :=
        hRunTy
      exact typeof_or_eq_bool_right hTy'
    have hCBool : RuleProofs.eo_has_bool_type C :=
      RuleProofs.eo_typeof_bool_implies_has_bool_type C hCTrans hCTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hExtNe,
      eo_mk_apply_eq_apply_of_ne_stuck _ _ (by simp) hCNe]
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
      ⟨a, hAEval⟩
    cases a with
    | false =>
        exact eo_interprets_imp_true_of_left_false M hM A C
          (RuleProofs.eo_interprets_of_bool_eval M A false hABool hAEval) hCBool
    | true =>
        have hATrue : eo_interprets M A true :=
          RuleProofs.eo_interprets_of_bool_eval M A true hABool hAEval
        have hCTrue : eo_interprets M C true :=
          extract_antec_sound M F C hFTrue hExtNe hATrue
        exact eo_interprets_imp_true_of_right_true M hM A C hABool hCTrue

public theorem cmd_step_process_scope_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.process_scope args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.process_scope args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.process_scope args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.process_scope args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises <;> exact False.elim (hProg rfl)
  | cons C args =>
      cases args with
      | cons _ _ =>
          cases premises <;> exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | nil =>
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | cons _ _ =>
                  exact False.elim (hProg rfl)
              | nil =>
                  let F := __eo_state_proven_nth s n1
                  have hCTrans : RuleProofs.eo_has_smt_translation C := by
                    simpa [cmdTranslationOk, cArgListTranslationOk, eoHasSmtTranslation,
                      RuleProofs.eo_has_smt_translation] using hCmdTrans.1
                  have hCNe : C ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
                  have hProgEq :
                      __eo_prog_process_scope C (Proof.pf F) = __run_process_scope F C :=
                    eo_prog_process_scope_eq C F hCNe
                  have hFBool : RuleProofs.eo_has_bool_type F :=
                    hPremisesBool F (by simp [F, premiseTermList])
                  have hProgNe :
                      __eo_prog_process_scope C (Proof.pf F) ≠ Term.Stuck := by
                    change __eo_prog_process_scope C (Proof.pf F) ≠ Term.Stuck at hProg
                    exact hProg
                  have hProgTy :
                      __eo_typeof (__eo_prog_process_scope C (Proof.pf F)) = Term.Bool := by
                    change __eo_typeof (__eo_prog_process_scope C (Proof.pf F)) = Term.Bool at hResultTy
                    exact hResultTy
                  have hRunNe : __run_process_scope F C ≠ Term.Stuck := by
                    rwa [hProgEq] at hProgNe
                  have hRunTy : __eo_typeof (__run_process_scope F C) = Term.Bool := by
                    rwa [hProgEq] at hProgTy
                  refine ⟨?_, ?_⟩
                  · intro hPremisesTrue
                    change eo_interprets M (__eo_prog_process_scope C (Proof.pf F)) true
                    rw [hProgEq]
                    exact run_process_scope_sound M hM F C
                      (hPremisesTrue F (by simp [F, premiseTermList]))
                      hFBool hCTrans hRunTy hRunNe
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_process_scope C (Proof.pf F))
                    rw [hProgEq]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (run_process_scope_bool F C hFBool hCTrans hRunTy hRunNe)
