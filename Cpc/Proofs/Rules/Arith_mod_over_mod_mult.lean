module

public import Cpc.Proofs.RuleSupport.ArithModOverModSupport
import all Cpc.Proofs.RuleSupport.ArithModOverModSupport

open Eo
open SmtEval
open Smtm
open ArithModOverModSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithModOverModMult

private abbrev lhsTerm (c ts r ss : Term) : Term :=
  modTotalTerm
    (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss)) c

private abbrev rhsTerm (c ts r ss : Term) : Term :=
  modTotalTerm
    (__eo_list_singleton_elim multOp
      (__eo_list_concat multOp ts (multTerm r ss))) c

private theorem smtx_typeof_mod_total_int
    (r c : Term)
    (hR : __smtx_typeof (__eo_to_smt r) = SmtType.Int)
    (hC : __smtx_typeof (__eo_to_smt c) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (modTotalTerm r c)) = SmtType.Int := by
  change __smtx_typeof
      (SmtTerm.mod_total (__eo_to_smt r) (__eo_to_smt c)) = SmtType.Int
  rw [typeof_mod_total_eq]
  simp [native_ite, native_Teq, hR, hC]

private theorem smtx_eval_mod_total_int
    (M : SmtModel) (r c : Term) (nr nc : native_Int)
    (hR : __smtx_model_eval M (__eo_to_smt r) = SmtValue.Numeral nr)
    (hC : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Numeral nc) :
    __smtx_model_eval M (__eo_to_smt (modTotalTerm r c)) =
      SmtValue.Numeral (native_mod_total nr nc) := by
  change __smtx_model_eval M
      (SmtTerm.mod_total (__eo_to_smt r) (__eo_to_smt c)) =
    SmtValue.Numeral (native_mod_total nr nc)
  rw [smtx_eval_mod_total_term_eq, hR, hC]
  simp [__smtx_model_eval_mod_total]

private theorem prog_arith_mod_over_mod_mult_info
    (c ts r ss P : Term)
    (hProg :
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) ≠ Term.Stuck) :
    ∃ c0,
      P = modPremise c0 ∧ c0 = c ∧
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
        multConclusion c ts r ss := by
  unfold __eo_prog_arith_mod_over_mod_mult at hProg
  split at hProg <;> try contradiction
  next h1 h2 h3 h4 heq =>
    rename_i c0
    injection heq with hPEq
    have hc0 := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    have hFinalNe := by
      rw [hc0] at hProg
      simpa [__eo_requires, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, lhsTerm, rhsTerm, multConclusion,
        modTotalTerm, multTerm, eqTerm] using hProg
    refine ⟨c0, ?_, hc0, ?_⟩
    · simpa [modPremise, eqTerm] using hPEq
    · rw [hPEq, hc0]
      simp [__eo_prog_arith_mod_over_mod_mult, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hc0, __eo_eq]
      have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
      have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFinalNe
      have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
      have hLhsFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hLhsNe
      have hRhsFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsFunNe]

private theorem mod_total_arg_ne_stuck_of_type_ne_stuck (x c : Term)
    (h : __eo_typeof (modTotalTerm x c) ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  change __eo_typeof_div (__eo_typeof Term.Stuck) (__eo_typeof c) ≠
    Term.Stuck at h
  have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by rfl
  rw [hStuckTy] at h
  simp [__eo_typeof_div] at h

private theorem typeof_mod_total_args_int_of_ne_stuck (x c : Term)
    (h : __eo_typeof (modTotalTerm x c) ≠ Term.Stuck) :
    __eo_typeof x = Term.Int ∧ __eo_typeof c = Term.Int := by
  change __eo_typeof_div (__eo_typeof x) (__eo_typeof c) ≠ Term.Stuck at h
  cases hx : __eo_typeof x <;>
    cases hc : __eo_typeof c <;>
    simp [__eo_typeof_div, hx, hc] at h ⊢
  case UOp.UOp opx opc =>
    cases opx <;> cases opc <;> simp [__eo_typeof_div] at h ⊢

private theorem typeof_mult_arg_types_of_ne_stuck {A B : Term}
    (h : __eo_typeof_plus A B ≠ Term.Stuck) :
    (A = Term.Int ∧ B = Term.Int) ∨
      (A = Term.Real ∧ B = Term.Real) := by
  cases A <;> cases B <;>
    simp [__eo_typeof_plus, __eo_requires, __is_arith_type, __eo_eq,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;>
      simp [__eo_typeof_plus, __eo_requires, __is_arith_type, __eo_eq,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

private theorem typeof_mult_args_int_of_result_int (x y : Term)
    (h : __eo_typeof (multTerm x y) = Term.Int) :
    __eo_typeof x = Term.Int ∧ __eo_typeof y = Term.Int := by
  have hNe :
      __eo_typeof_plus (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    change __eo_typeof (multTerm x y) ≠ Term.Stuck
    rw [h]
    decide
  rcases typeof_mult_arg_types_of_ne_stuck hNe with hArgs | hArgs
  · exact hArgs
  · change __eo_typeof_plus (__eo_typeof x) (__eo_typeof y) = Term.Int at h
    rw [hArgs.1, hArgs.2] at h
    simp [__eo_typeof_plus, __eo_requires, __is_arith_type,
      __eo_eq, native_ite, native_teq, native_not] at h

private def MulListTypeOrNil (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

private theorem list_concat_rec_cons_of_right_ne_stuck
    (f x xs z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs z) := by
  cases z <;> simp [__eo_list_concat_rec] at hz ⊢

private theorem mk_apply_right_stuck (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem mult_list_concat_rec_right_type_ne_stuck (a z : Term)
    (hList : __eo_is_list multOp a = Term.Boolean true)
    (hTyNe : __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck) :
    __eo_typeof z ≠ Term.Stuck := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [multOp, __eo_is_list] at hList
  | case2 a ha =>
      apply False.elim
      apply hTyNe
      cases a <;> rfl
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true multOp f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self multOp x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [list_concat_rec_cons_of_right_ne_stuck multOp x xs z hz,
          h, mk_apply_right_stuck]
        rfl
      have hTailTyNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [list_concat_rec_cons_of_right_ne_stuck multOp x xs z hz,
          mk_apply_eq_apply_of_ne_stuck _ _ (by simp [multOp]) hTailNe]
        change __eo_typeof_plus (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) = Term.Stuck
        rw [h]
        cases hx : __eo_typeof x <;> simp [__eo_typeof_plus, hx]
      exact ih hTailList hTailTyNe
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTyNe

private theorem mult_list_type_or_nil_of_concat_type (a z : Term)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hAList : __eo_is_list multOp a = Term.Boolean true)
    (hz : z ≠ Term.Stuck)
    (hConcatTy : __eo_typeof (__eo_list_concat_rec a z) = Term.Int) :
    MulListTypeOrNil a := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [multOp, __eo_is_list] at hAList
  | case2 a ha => exact False.elim (hz rfl)
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true multOp f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro hTail
        rw [list_concat_rec_cons_of_right_ne_stuck multOp x xs z hz,
          hTail, mk_apply_right_stuck] at hConcatTy
        cases hConcatTy
      rw [list_concat_rec_cons_of_right_ne_stuck multOp x xs z hz,
        mk_apply_eq_apply_of_ne_stuck _ _ (by simp [multOp]) hTailNe]
        at hConcatTy
      have hXTy := (typeof_mult_args_int_of_result_int x
        (__eo_list_concat_rec xs z) hConcatTy).1
      have hSmtArgs := arith_binop_args_of_non_none
        (op := SmtTerm.mult) (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt xs))
        hATrans
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        rcases hSmtArgs with hArgs | hArgs
        · simp [RuleProofs.eo_has_smt_translation, hArgs.1]
        · simp [RuleProofs.eo_has_smt_translation, hArgs.1]
      have hXSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        smtx_typeof_of_eo_int x hXTrans hXTy
      apply Or.inl
      change __smtx_typeof
          (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt xs)) = SmtType.Int
      rw [typeof_mult_eq]
      rcases hSmtArgs with hArgs | hArgs
      · simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
      · rw [hArgs.1] at hXSmt
        cases hXSmt
  | case4 nil z hNil hZ hNot =>
      apply Or.inr
      intro tail
      unfold __eo_list_concat_rec
      split <;> simp_all

private theorem list_concat_left_is_list_of_ne_stuck {f a b : Term}
    (hConcat : __eo_list_concat f a b ≠ Term.Stuck) :
    __eo_is_list f a = Term.Boolean true := by
  cases hA : __eo_is_list f a <;>
    simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

private theorem list_concat_right_is_list_of_ne_stuck {f a b : Term}
    (hConcat : __eo_list_concat f a b ≠ Term.Stuck) :
    __eo_is_list f b = Term.Boolean true := by
  have hA := list_concat_left_is_list_of_ne_stuck hConcat
  cases hB : __eo_is_list f b <;>
    simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

private theorem mult_lists_of_result_bool
    (c ts r ss P : Term)
    (hProgEq :
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
        multConclusion c ts r ss)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) =
        Term.Bool) :
    __eo_is_list multOp ts = Term.Boolean true ∧
      __eo_is_list multOp ss = Term.Boolean true := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (lhsTerm c ts r ss))
      (__eo_typeof (rhsTerm c ts r ss)) = Term.Bool at hResultTy
  have hOperands :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (lhsTerm c ts r ss))
      (__eo_typeof (rhsTerm c ts r ss)) hResultTy
  have hConcatNe :
      __eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss) ≠
        Term.Stuck :=
    mod_total_arg_ne_stuck_of_type_ne_stuck
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss)) c
      hOperands.1
  have hTsList := list_concat_left_is_list_of_ne_stuck hConcatNe
  have hTailList := list_concat_right_is_list_of_ne_stuck hConcatNe
  have hSsList :=
    eo_is_list_tail_true_of_cons_self multOp (modTotalTerm r c) ss hTailList
  exact ⟨hTsList, hSsList⟩

private theorem mult_arg_types_of_result_bool
    (c ts r ss P : Term)
    (hTsTrans : RuleProofs.eo_has_smt_translation ts)
    (hProgEq :
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
        multConclusion c ts r ss)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) =
        Term.Bool) :
    __eo_typeof c = Term.Int ∧
      __eo_typeof r = Term.Int ∧
      __eo_typeof ss = Term.Int ∧ MulListTypeOrNil ts := by
  have hLists := mult_lists_of_result_bool c ts r ss P hProgEq hResultTy
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (lhsTerm c ts r ss))
      (__eo_typeof (rhsTerm c ts r ss)) = Term.Bool at hResultTy
  have hOperands := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhsTerm c ts r ss))
    (__eo_typeof (rhsTerm c ts r ss)) hResultTy
  have hOuter := typeof_mod_total_args_int_of_ne_stuck
    (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss)) c
    hOperands.1
  have hTailList :
      __eo_is_list multOp (multTerm (modTotalTerm r c) ss) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list multOp (modTotalTerm r c) ss
      (by decide) hLists.2
  have hConcatEq :
      __eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss) =
        __eo_list_concat_rec ts (multTerm (modTotalTerm r c) ss) := by
    simp [__eo_list_concat, hLists.1, hTailList, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not]
  have hConcatTy :
      __eo_typeof
          (__eo_list_concat_rec ts (multTerm (modTotalTerm r c) ss)) =
        Term.Int := by
    rw [← hConcatEq]
    exact hOuter.1
  have hTailTyNe :
      __eo_typeof (multTerm (modTotalTerm r c) ss) ≠ Term.Stuck :=
    mult_list_concat_rec_right_type_ne_stuck ts
      (multTerm (modTotalTerm r c) ss) hLists.1 (by rw [hConcatTy]; decide)
  have hModTyNe : __eo_typeof (modTotalTerm r c) ≠ Term.Stuck := by
    intro h
    apply hTailTyNe
    change __eo_typeof_plus (__eo_typeof (modTotalTerm r c))
      (__eo_typeof ss) = Term.Stuck
    rw [h]
    simp [__eo_typeof_plus]
  have hModArgs := typeof_mod_total_args_int_of_ne_stuck r c hModTyNe
  have hModTy : __eo_typeof (modTotalTerm r c) = Term.Int := by
    change __eo_typeof_div (__eo_typeof r) (__eo_typeof c) = Term.Int
    rw [hModArgs.1, hModArgs.2]
    rfl
  have hSsInt : __eo_typeof ss = Term.Int := by
    change __eo_typeof_plus (__eo_typeof (modTotalTerm r c))
      (__eo_typeof ss) ≠ Term.Stuck at hTailTyNe
    rw [hModTy] at hTailTyNe
    cases hs : __eo_typeof ss <;>
      simp [__eo_typeof_plus, __eo_requires, __is_arith_type, __eo_eq,
        native_ite, native_teq, native_not, hs] at hTailTyNe ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_typeof_plus, __eo_requires, __is_arith_type, __eo_eq,
          native_ite, native_teq, native_not] at hTailTyNe ⊢
  have hTsType := mult_list_type_or_nil_of_concat_type ts
    (multTerm (modTotalTerm r c) ss) hTsTrans hLists.1
    (by simp [multTerm]) hConcatTy
  exact ⟨hOuter.2, hModArgs.1, hSsInt, hTsType⟩

private theorem build_mult_lists
    (M : SmtModel) (hM : model_wf M) (c ts r ss : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hSsTrans : RuleProofs.eo_has_smt_translation ss)
    (hCInt : __eo_typeof c = Term.Int)
    (hRInt : __eo_typeof r = Term.Int)
    (hSsInt : __eo_typeof ss = Term.Int)
    (hTsType : MulListTypeOrNil ts)
    (hTsList : __eo_is_list multOp ts = Term.Boolean true)
    (hSsList : __eo_is_list multOp ss = Term.Boolean true) :
    ∃ nc nts nr nss,
      __smtx_model_eval M (__eo_to_smt c) = SmtValue.Numeral nc ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.Numeral nr ∧
      MulListEval M (__eo_list_concat multOp ts
        (multTerm (modTotalTerm r c) ss))
        (nts * (native_mod_total nr nc * nss)) ∧
      MulListEval M (__eo_list_concat multOp ts (multTerm r ss))
        (nts * (nr * nss)) := by
  have hCSmt : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hCInt
  have hRSmt : __smtx_typeof (__eo_to_smt r) = SmtType.Int :=
    smtx_typeof_of_eo_int r hRTrans hRInt
  have hSsSmt : __smtx_typeof (__eo_to_smt ss) = SmtType.Int :=
    smtx_typeof_of_eo_int ss hSsTrans hSsInt
  rcases smt_eval_int_of_type M hM c hCSmt with ⟨nc, hCEval⟩
  rcases smt_eval_int_of_type M hM r hRSmt with ⟨nr, hREval⟩
  rcases MulListEval.of_type_and_list M hM hSsList hSsSmt with
    ⟨nss, hSsEval⟩
  have hModTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm r c)) = SmtType.Int :=
    smtx_typeof_mod_total_int r c hRSmt hCSmt
  have hModEval :
      __smtx_model_eval M (__eo_to_smt (modTotalTerm r c)) =
        SmtValue.Numeral (native_mod_total nr nc) :=
    smtx_eval_mod_total_int M r c nr nc hREval hCEval
  have hLeftTail := MulListEval.cons hModTy hModEval hSsEval
  have hRightTail := MulListEval.cons hRSmt hREval hSsEval
  rcases hTsType with hTsSmt | hTsNil
  · rcases MulListEval.of_type_and_list M hM hTsList hTsSmt with
      ⟨nts, hTsEval⟩
    exact ⟨nc, nts, nr, nss, hCEval, hREval,
      MulListEval.concat hTsEval hLeftTail,
      MulListEval.concat hTsEval hRightTail⟩
  · have hLeftEq :
        __eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss) =
          multTerm (modTotalTerm r c) ss := by
      simp [__eo_list_concat, hTsList, MulListEval.is_list hLeftTail,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hTsNil]
    have hRightEq :
        __eo_list_concat multOp ts (multTerm r ss) = multTerm r ss := by
      simp [__eo_list_concat, hTsList, MulListEval.is_list hRightTail,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hTsNil]
    refine ⟨nc, 1, nr, nss, hCEval, hREval, ?_, ?_⟩
    · rw [hLeftEq]
      simpa using hLeftTail
    · rw [hRightEq]
      simpa using hRightTail

private theorem typed___eo_prog_arith_mod_over_mod_mult_impl
    (M : SmtModel) (hM : model_wf M)
    (c ts r ss P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation ts ->
    RuleProofs.eo_has_smt_translation r ->
    RuleProofs.eo_has_smt_translation ss ->
    __eo_typeof c = Term.Int ->
    __eo_typeof r = Term.Int ->
    __eo_typeof ss = Term.Int ->
    MulListTypeOrNil ts ->
    __eo_is_list multOp ts = Term.Boolean true ->
    __eo_is_list multOp ss = Term.Boolean true ->
    __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
      multConclusion c ts r ss ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) := by
  intro hCTrans _hTsTrans hRTrans hSsTrans hCInt hRInt hSsInt hTsType
    hTsList hSsList hProgEq
  rcases build_mult_lists M hM c ts r ss hCTrans hRTrans hSsTrans
      hCInt hRInt hSsInt hTsType hTsList hSsList with
    ⟨nc, nts, nr, nss, _hCEval, _hREval, hLList, hRList⟩
  have hCSmt : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hCInt
  have hLhsArgTy := MulListEval.type_int hLList
  have hRhsArgInfo := MulListEval.singleton_elim_eval hRList
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhsTerm c ts r ss)) = SmtType.Int :=
    smtx_typeof_mod_total_int
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss))
      c hLhsArgTy hCSmt
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhsTerm c ts r ss)) = SmtType.Int :=
    smtx_typeof_mod_total_int
      (__eo_list_singleton_elim multOp
        (__eo_list_concat multOp ts (multTerm r ss)))
      c hRhsArgInfo.1 hCSmt
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhsTerm c ts r ss) (rhsTerm c ts r ss)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_arith_mod_over_mod_mult_impl
    (M : SmtModel) (hM : model_wf M)
    (c ts r ss P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation ts ->
    RuleProofs.eo_has_smt_translation r ->
    RuleProofs.eo_has_smt_translation ss ->
    __eo_typeof c = Term.Int ->
    __eo_typeof r = Term.Int ->
    __eo_typeof ss = Term.Int ->
    MulListTypeOrNil ts ->
    __eo_is_list multOp ts = Term.Boolean true ->
    __eo_is_list multOp ss = Term.Boolean true ->
    __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
      multConclusion c ts r ss ->
    eo_interprets M
      (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) true := by
  intro hCTrans hTsTrans hRTrans hSsTrans hCInt hRInt hSsInt hTsType
    hTsList hSsList hProgEq
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) :=
    typed___eo_prog_arith_mod_over_mod_mult_impl M hM c ts r ss P
      hCTrans hTsTrans hRTrans hSsTrans hCInt hRInt hSsInt hTsType
      hTsList hSsList hProgEq
  have hProgBool' : RuleProofs.eo_has_bool_type (multConclusion c ts r ss) := by
    simpa [hProgEq] using hProgBool
  rcases build_mult_lists M hM c ts r ss hCTrans hRTrans hSsTrans
      hCInt hRInt hSsInt hTsType hTsList hSsList with
    ⟨nc, nts, nr, nss, hCEval, _hREval, hLList, hRList⟩
  have hLhsArgEval := MulListEval.eval hLList
  have hRhsArgInfo := MulListEval.singleton_elim_eval hRList
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhsTerm c ts r ss)) =
        SmtValue.Numeral
          (native_mod_total (nts * (native_mod_total nr nc * nss)) nc) :=
    smtx_eval_mod_total_int M
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss))
      c (nts * (native_mod_total nr nc * nss)) nc hLhsArgEval hCEval
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhsTerm c ts r ss)) =
        SmtValue.Numeral
          (native_mod_total (nts * (nr * nss)) nc) :=
    smtx_eval_mod_total_int M
      (__eo_list_singleton_elim multOp
        (__eo_list_concat multOp ts (multTerm r ss)))
      c (nts * (nr * nss)) nc hRhsArgInfo.2 hCEval
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (lhsTerm c ts r ss) (rhsTerm c ts r ss) hProgBool' <| by
      rw [hLhsEval, hRhsEval, mod_mul_replace_mod]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Numeral (native_mod_total (nts * (nr * nss)) nc))

end ArithModOverModMult

open ArithModOverModMult

public theorem cmd_step_arith_mod_over_mod_mult_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod_mult args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p1 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let C1 := a1
                              let TS1 := a2
                              let R1 := a3
                              let SS1 := a4
                              let P1 := __eo_state_proven_nth s p1
                              have hArgsTrans :
                                  RuleProofs.eo_has_smt_translation C1 ∧
                                    RuleProofs.eo_has_smt_translation TS1 ∧
                                      RuleProofs.eo_has_smt_translation R1 ∧
                                        RuleProofs.eo_has_smt_translation SS1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans
                              have hCTrans :
                                  RuleProofs.eo_has_smt_translation C1 :=
                                hArgsTrans.1
                              have hTsTrans :
                                  RuleProofs.eo_has_smt_translation TS1 :=
                                hArgsTrans.2.1
                              have hRTrans :
                                  RuleProofs.eo_has_smt_translation R1 :=
                                hArgsTrans.2.2.1
                              have hSsTrans :
                                  RuleProofs.eo_has_smt_translation SS1 :=
                                hArgsTrans.2.2.2
                              change __eo_typeof
                                (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                  (Proof.pf P1)) = Term.Bool at hResultTy
                              change __eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                (Proof.pf P1) ≠ Term.Stuck at hProg
                              rcases prog_arith_mod_over_mod_mult_info
                                  C1 TS1 R1 SS1 P1 hProg with
                                ⟨C0, hP1Eq, hC0Eq, hProgEq⟩
                              have hArgTypes := mult_arg_types_of_result_bool
                                C1 TS1 R1 SS1 P1 hTsTrans hProgEq hResultTy
                              have hCInt : __eo_typeof C1 = Term.Int :=
                                hArgTypes.1
                              have hRInt : __eo_typeof R1 = Term.Int :=
                                hArgTypes.2.1
                              have hSsInt : __eo_typeof SS1 = Term.Int :=
                                hArgTypes.2.2.1
                              have hTsType : MulListTypeOrNil TS1 :=
                                hArgTypes.2.2.2
                              have hLists :=
                                mult_lists_of_result_bool C1 TS1 R1 SS1 P1
                                  hProgEq hResultTy
                              have hTsList :
                                  __eo_is_list multOp TS1 = Term.Boolean true :=
                                hLists.1
                              have hSsList :
                                  __eo_is_list multOp SS1 = Term.Boolean true :=
                                hLists.2
                              refine ⟨?_, ?_⟩
                              · intro _hPremTrue
                                change eo_interprets M
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1)) true
                                exact facts___eo_prog_arith_mod_over_mod_mult_impl
                                  M hM C1 TS1 R1 SS1 P1
                                  hCTrans hTsTrans hRTrans hSsTrans hCInt
                                  hRInt hSsInt hTsType hTsList hSsList hProgEq
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1))
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1))
                                  (typed___eo_prog_arith_mod_over_mod_mult_impl
                                    M hM C1 TS1 R1 SS1 P1
                                    hCTrans hTsTrans hRTrans hSsTrans hCInt
                                    hRInt hSsInt hTsType hTsList hSsList hProgEq)
