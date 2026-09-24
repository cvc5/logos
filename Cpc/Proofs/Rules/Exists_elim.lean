module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.Translation.Quantifiers
import all Cpc.Proofs.Translation.Quantifiers

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) := by
  rfl

private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [TranslationProofs.smtx_typeof_none]

private def exists_elim_lhs (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.exists) x) F

private def exists_elim_rhs (x F : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not)
    (Term.Apply (Term.Apply (Term.UOp UserOp.forall) x)
      (Term.Apply (Term.UOp UserOp.not) F))

private def exists_elim_formula (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (exists_elim_lhs x F))
    (exists_elim_rhs x F)

private theorem eo_to_smt_exists_elim_lhs
    (x F : Term) (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (exists_elim_lhs x F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  unfold exists_elim_lhs
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_exists_elim_rhs
    (x F : Term) (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (exists_elim_rhs x F) =
      SmtTerm.not
        (SmtTerm.not
          (__eo_to_smt_exists x
            (SmtTerm.not (SmtTerm.not (__eo_to_smt F))))) := by
  unfold exists_elim_rhs
  rw [eo_to_smt_not_eq, eo_to_smt_forall_eq _ _ hx, eo_to_smt_not_eq]

private theorem eo_to_smt_exists_elim_formula
    (x F : Term) (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (exists_elim_formula x F) =
      SmtTerm.eq
        (__eo_to_smt_exists x (__eo_to_smt F))
        (SmtTerm.not
          (SmtTerm.not
            (__eo_to_smt_exists x
              (SmtTerm.not (SmtTerm.not (__eo_to_smt F)))))) := by
  unfold exists_elim_formula
  rw [eo_to_smt_eq_eq, eo_to_smt_exists_elim_lhs _ _ hx,
    eo_to_smt_exists_elim_rhs _ _ hx]

private theorem exists_elim_vars_non_nil_of_translation
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (exists_elim_formula x F) ->
    x ≠ Term.__eo_List_nil := by
  intro hTrans hx
  subst x
  unfold RuleProofs.eo_has_smt_translation at hTrans
  apply hTrans
  unfold exists_elim_formula exists_elim_lhs exists_elim_rhs
  change __smtx_typeof (SmtTerm.eq SmtTerm.None (SmtTerm.not SmtTerm.None)) =
    SmtType.None
  rw [typeof_eq_eq, typeof_not_eq, TranslationProofs.smtx_typeof_none]
  simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]

private theorem eo_to_smt_exists_body_bool_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body = SmtType.Bool := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists] using hTy
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            exact eo_to_smt_exists_body_bool_of_bool a body hSub
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simp [__eo_to_smt_exists] at hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simp [__eo_to_smt_exists] at hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simp [__eo_to_smt_exists] at hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simp [__eo_to_smt_exists] at hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simp [__eo_to_smt_exists] at hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

private theorem smtx_model_eval_not_not_true_iff
    (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) = SmtValue.Boolean true ↔
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
    (M : SmtModel) (xs : Term) (body : SmtTerm) :
    __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
        SmtValue.Boolean true ↔
      __smtx_model_eval M (__eo_to_smt_exists xs body) = SmtValue.Boolean true := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists, __smtx_model_eval] using
      smtx_model_eval_not_not_true_iff (__smtx_model_eval M body)
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a body) = SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body
    (M : SmtModel) (hM : model_wf M)
    (xs : Term) (body : SmtTerm)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
      __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
    simp [__eo_to_smt_exists, __smtx_model_eval, hb, __smtx_model_eval_not,
      SmtEval.native_not]
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a body) = SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_typeof_not_arg_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem smtx_model_eval_not_not
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.not t)) =
      __smtx_model_eval M t := by
  rcases smt_model_eval_bool_is_boolean M hM t hTy with ⟨b, hb⟩
  simp [__smtx_model_eval, hb, __smtx_model_eval_not, SmtEval.native_not]

private theorem exists_elim_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_exists_elim x1 ≠ Term.Stuck ->
    ∃ x F,
      x1 = exists_elim_formula x F ∧
      __eo_prog_exists_elim x1 = exists_elim_formula x F := by
  intro hProg
  cases x1 with
  | Apply lhs rhs =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply exHead F =>
                      cases exHead with
                      | Apply exOp x =>
                          cases exOp with
                          | UOp opExists =>
                              cases opExists with
                              | «exists» =>
                                  cases rhs with
                                  | Apply notHead forallTerm =>
                                      cases notHead with
                                      | UOp opNot1 =>
                                          cases opNot1 with
                                          | not =>
                                              cases forallTerm with
                                              | Apply forallHead notF2 =>
                                                  cases forallHead with
                                                  | Apply forallOp x2 =>
                                                      cases forallOp with
                                                      | UOp opForall =>
                                                          cases opForall with
                                                          | «forall» =>
                                                              cases notF2 with
                                                              | Apply notHead2 F2 =>
                                                                  cases notHead2 with
                                                                  | UOp opNot2 =>
                                                                      cases opNot2 with
                                                                      | not =>
                                                                          have hReq :
                                                                              __eo_requires
                                                                                  (__eo_and
                                                                                    (__eo_eq x x2)
                                                                                    (__eo_eq F F2))
                                                                                  (Term.Boolean true)
                                                                                  (exists_elim_formula x F) ≠
                                                                                Term.Stuck := by
                                                                            simpa [exists_elim_formula,
                                                                              exists_elim_lhs, exists_elim_rhs,
                                                                              __eo_prog_exists_elim] using hProg
                                                                          rcases
                                                                              RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                                                                x F x2 F2
                                                                                (exists_elim_formula x F) hReq with
                                                                            ⟨hx, hF⟩
                                                                          subst x2
                                                                          subst F2
                                                                          have hReq' := hReq
                                                                          simp [__eo_requires, native_ite,
                                                                            native_teq, native_not,
                                                                            SmtEval.native_not] at hReq'
                                                                          have hGuard :
                                                                              __eo_and (__eo_eq x x)
                                                                                (__eo_eq F F) =
                                                                                  Term.Boolean true :=
                                                                            hReq'.1
                                                                          refine ⟨x, F, rfl, ?_⟩
                                                                          change __eo_prog_exists_elim
                                                                              (exists_elim_formula x F) =
                                                                            exists_elim_formula x F
                                                                          rw [show __eo_prog_exists_elim
                                                                              (exists_elim_formula x F) =
                                                                                __eo_requires
                                                                                  (__eo_and
                                                                                    (__eo_eq x x)
                                                                                    (__eo_eq F F))
                                                                                  (Term.Boolean true)
                                                                                  (exists_elim_formula x F) by
                                                                            simp [exists_elim_formula,
                                                                              exists_elim_lhs,
                                                                              exists_elim_rhs,
                                                                              __eo_prog_exists_elim]]
                                                                          rw [__eo_requires]
                                                                          simp [hGuard, native_ite, native_teq,
                                                                            native_not, SmtEval.native_not]
                                                                      | _ =>
                                                                          simp [__eo_prog_exists_elim] at hProg
                                                                  | _ =>
                                                                      simp [__eo_prog_exists_elim] at hProg
                                                              | _ =>
                                                                  simp [__eo_prog_exists_elim] at hProg
                                                          | _ =>
                                                              simp [__eo_prog_exists_elim] at hProg
                                                      | _ =>
                                                          simp [__eo_prog_exists_elim] at hProg
                                                  | _ =>
                                                      simp [__eo_prog_exists_elim] at hProg
                                              | _ =>
                                                  simp [__eo_prog_exists_elim] at hProg
                                          | _ =>
                                              simp [__eo_prog_exists_elim] at hProg
                                      | _ =>
                                          simp [__eo_prog_exists_elim] at hProg
                                  | _ =>
                                      simp [__eo_prog_exists_elim] at hProg
                              | _ =>
                                  simp [__eo_prog_exists_elim] at hProg
                          | _ =>
                              simp [__eo_prog_exists_elim] at hProg
                      | _ =>
                          simp [__eo_prog_exists_elim] at hProg
                  | _ =>
                      simp [__eo_prog_exists_elim] at hProg
              | _ =>
                  simp [__eo_prog_exists_elim] at hProg
          | _ =>
              simp [__eo_prog_exists_elim] at hProg
      | _ =>
          simp [__eo_prog_exists_elim] at hProg
  | _ =>
      simp [__eo_prog_exists_elim] at hProg

private theorem typed_exists_elim_formula_of_translation
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (exists_elim_formula x F) ->
    RuleProofs.eo_has_bool_type (exists_elim_formula x F) := by
  intro hTrans
  have hNN : term_has_non_none_type (__eo_to_smt (exists_elim_formula x F)) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hTrans
  have hx : x ≠ Term.__eo_List_nil :=
    exists_elim_vars_non_nil_of_translation x F hTrans
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_exists_elim_formula _ _ hx]
  rw [eo_to_smt_exists_elim_formula _ _ hx] at hNN
  exact eq_term_typeof_of_non_none hNN

private theorem typed___eo_prog_exists_elim_impl
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_exists_elim x1 ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_exists_elim x1) := by
  intro hTrans hProg
  rcases exists_elim_shape_of_not_stuck x1 hProg with ⟨x, F, hx1, hProgEq⟩
  rw [hProgEq]
  apply typed_exists_elim_formula_of_translation
  simpa [hx1] using hTrans

private theorem smtx_model_eval_exists_elim_formula
    (M : SmtModel) (hM : model_wf M)
    (x F : Term)
    (hTrans : RuleProofs.eo_has_smt_translation (exists_elim_formula x F)) :
    __smtx_model_eval M (__eo_to_smt (exists_elim_rhs x F)) =
      __smtx_model_eval M (__eo_to_smt (exists_elim_lhs x F)) := by
  let body := __eo_to_smt F
  let lhsS := __eo_to_smt_exists x body
  let innerS := __eo_to_smt_exists x (SmtTerm.not (SmtTerm.not body))
  let rhsS := SmtTerm.not (SmtTerm.not innerS)
  have hEqBool :
      RuleProofs.eo_has_bool_type (exists_elim_formula x F) :=
    typed_exists_elim_formula_of_translation x F hTrans
  have hx : x ≠ Term.__eo_List_nil :=
    exists_elim_vars_non_nil_of_translation x F hTrans
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (exists_elim_lhs x F) (exists_elim_rhs x F) hEqBool with
    ⟨hSameTy, hLhsNN⟩
  rw [eo_to_smt_exists_elim_lhs _ _ hx, eo_to_smt_exists_elim_rhs _ _ hx] at hSameTy
  rw [eo_to_smt_exists_elim_lhs _ _ hx] at hLhsNN
  have hSameTy' : __smtx_typeof lhsS = __smtx_typeof rhsS := by
    simpa [body, lhsS, rhsS] using hSameTy
  have hLhsNN' : __smtx_typeof lhsS ≠ SmtType.None := by
    simpa [body, lhsS] using hLhsNN
  have hRhsNN' : __smtx_typeof rhsS ≠ SmtType.None := by
    intro hRhsNone
    apply hLhsNN'
    rw [hSameTy']
    exact hRhsNone
  have hNotInnerTy : __smtx_typeof (SmtTerm.not innerS) = SmtType.Bool :=
    smtx_typeof_not_arg_of_non_none (SmtTerm.not innerS) hRhsNN'
  have hInnerTy : __smtx_typeof innerS = SmtType.Bool :=
    smtx_typeof_not_arg_bool innerS hNotInnerTy
  have hDoubleBodyTy : __smtx_typeof (SmtTerm.not (SmtTerm.not body)) = SmtType.Bool :=
    eo_to_smt_exists_body_bool_of_bool x (SmtTerm.not (SmtTerm.not body)) hInnerTy
  have hNotBodyTy : __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
    smtx_typeof_not_arg_bool (SmtTerm.not body) hDoubleBodyTy
  have hBodyTy : __smtx_typeof body = SmtType.Bool :=
    smtx_typeof_not_arg_bool body hNotBodyTy
  have hEvalRhsInner :
      __smtx_model_eval M rhsS = __smtx_model_eval M innerS :=
    smtx_model_eval_not_not M hM innerS hInnerTy
  have hEvalInnerLhs :
      __smtx_model_eval M innerS = __smtx_model_eval M lhsS :=
    smtx_model_eval_eo_to_smt_exists_double_not_body M hM x body hBodyTy
  rw [eo_to_smt_exists_elim_rhs _ _ hx, eo_to_smt_exists_elim_lhs _ _ hx]
  simpa [body, lhsS, innerS, rhsS] using hEvalRhsInner.trans hEvalInnerLhs

private theorem facts___eo_prog_exists_elim_impl
    (M : SmtModel) (hM : model_wf M)
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_exists_elim x1 ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_exists_elim x1) true := by
  intro hTrans hProg
  rcases exists_elim_shape_of_not_stuck x1 hProg with ⟨x, F, hx1, hProgEq⟩
  rw [hProgEq]
  apply RuleProofs.eo_interprets_eq_of_rel M (exists_elim_lhs x F) (exists_elim_rhs x F)
  · exact typed_exists_elim_formula_of_translation x F (by simpa [hx1] using hTrans)
  · have hEvalEq :=
        smtx_model_eval_exists_elim_formula M hM x F (by simpa [hx1] using hTrans)
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (exists_elim_lhs x F)))

public theorem cmd_step_exists_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.exists_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.exists_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.exists_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.exists_elim args premises ≠ Term.Stuck :=
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgExists :
                  __eo_prog_exists_elim a1 ≠ Term.Stuck := by
                change __eo_prog_exists_elim a1 ≠ Term.Stuck at hProg
                simpa using hProg
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_exists_elim a1) true
                exact facts___eo_prog_exists_elim_impl M hM a1 hTransA1 hProgExists
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_exists_elim_impl a1 hTransA1 hProgExists)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
