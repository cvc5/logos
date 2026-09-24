module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_self_of_non_stuck
    (T U : Term) :
    T ≠ Term.Stuck ->
    __eo_requires T T U = U := by
  intro hT
  simp [__eo_requires, native_ite, native_not, native_teq, hT]

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem eo_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;> simp [__eo_and, __eo_requires, native_teq,
    native_ite, SmtEval.native_and, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> simp at h

theorem prog_dt_cons_eq_condition_of_not_stuck
    (t s B : Term) :
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) ≠
      Term.Stuck ->
    let cond := __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)
    cond = B ∧ cond ≠ Term.Stuck := by
  intro hProg
  simp [__eo_prog_dt_cons_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg
  simpa

theorem prog_dt_cons_eq_eq_input_of_not_stuck
    (t s B : Term) :
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) ≠
      Term.Stuck ->
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) =
      Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B := by
  intro hProg
  let cond := __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)
  have hCond := prog_dt_cons_eq_condition_of_not_stuck t s B hProg
  have hEq : cond = B := hCond.1
  have hCondNe : cond ≠ Term.Stuck := hCond.2
  subst B
  simpa [__eo_prog_dt_cons_eq, cond] using
    eo_requires_self_of_non_stuck
      cond
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) cond)
      hCondNe

private theorem and_concat_rec_true (z : Term) :
    __eo_list_concat_rec (Term.Boolean true) z = z := by
  cases z <;> simp [__eo_list_concat_rec]

private theorem and_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem concat_rec_preserves_andList {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    CnfSupport.AndList (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  induction hC1 generalizing c2 with
  | true =>
      simpa [and_concat_rec_true] using hC2
  | cons x xs hXs ih =>
      have hTail : CnfSupport.AndList (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        CnfSupport.andList_ne_stuck hTail
      rw [and_concat_rec_cons x xs c2 hTailNe]
      exact CnfSupport.AndList.cons x (__eo_list_concat_rec xs c2) hTail

private theorem concat_preserves_andList {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    CnfSupport.AndList (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2
  simp [__eo_list_concat, CnfSupport.andList_is_list_true hC1,
    CnfSupport.andList_is_list_true hC2, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]
  exact concat_rec_preserves_andList hC1 hC2

private theorem list_concat_nonstuck_left {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.and) a b ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro hConcat
  intro hA
  subst a
  simp [__eo_list_concat, __eo_is_list, __eo_requires,
    native_ite, native_teq] at hConcat

private theorem model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b :=
  bool_value_canonical (typeof_value_model_eval_eq_value v1 v2)

private theorem smtx_model_eval_eq_not_reglan_pair
    (v w : SmtValue)
    (h : ¬ ∃ r1 r2, v = SmtValue.RegLan r1 ∧ w = SmtValue.RegLan r2) :
    __smtx_model_eval_eq v w = SmtValue.Boolean (decide (v = w)) := by
  cases v <;> cases w <;> simp [__smtx_model_eval_eq, native_veq] at h ⊢

private theorem smtx_model_eval_eq_false_of_ne_not_reglan
    {v w : SmtValue}
    (hNe : v ≠ w)
    (hReg : ¬ ∃ r1 r2, v = SmtValue.RegLan r1 ∧ w = SmtValue.RegLan r2) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  rw [smtx_model_eval_eq_not_reglan_pair v w hReg]
  simp [hNe]

inductive SmtValueProperSubterm : SmtValue -> SmtValue -> Prop where
  | app_fun_self {f a : SmtValue} :
      SmtValueProperSubterm f (SmtValue.Apply f a)
  | app_fun {v f a : SmtValue} :
      SmtValueProperSubterm v f ->
      SmtValueProperSubterm v (SmtValue.Apply f a)
  | app_arg {f a : SmtValue} :
      SmtValueProperSubterm a (SmtValue.Apply f a)
  | app_arg_sub {v f a : SmtValue} :
      SmtValueProperSubterm v a ->
      SmtValueProperSubterm v (SmtValue.Apply f a)

theorem smtValueProperSubterm_size_lt
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> sizeOf v < sizeOf w := by
  intro h
  induction h with
  | app_fun_self =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_fun h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg_sub h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega

theorem smtValueProperSubterm_ne
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> v ≠ w := by
  intro h hEq
  have hLt := smtValueProperSubterm_size_lt h
  subst w
  omega

theorem smtValueProperSubterm_trans
    {u v w : SmtValue} :
    SmtValueProperSubterm u v ->
    SmtValueProperSubterm v w ->
    SmtValueProperSubterm u w := by
  intro hUV hVW
  induction hVW with
  | app_fun_self =>
      exact SmtValueProperSubterm.app_fun hUV
  | app_fun h ih =>
      exact SmtValueProperSubterm.app_fun (ih hUV)
  | app_arg =>
      exact SmtValueProperSubterm.app_arg_sub hUV
  | app_arg_sub h ih =>
      exact SmtValueProperSubterm.app_arg_sub (ih hUV)

theorem smtValueProperSubterm_parent_ne_reglan
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> ∀ r, w ≠ SmtValue.RegLan r := by
  intro h r
  induction h with
  | app_fun_self => simp
  | app_fun => simp
  | app_arg => simp
  | app_arg_sub => simp

theorem smtx_model_eval_eq_false_of_proper_subterm
    {v w : SmtValue}
    (hSub : SmtValueProperSubterm v w) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (smtValueProperSubterm_ne hSub)
    (by
      rintro ⟨r1, r2, hV, hW⟩
      exact smtValueProperSubterm_parent_ne_reglan hSub r2 hW)

private theorem smtx_model_eval_eq_apply_eq_and
    (f g x y : SmtValue)
    (hF : ¬ ∃ r1 r2, f = SmtValue.RegLan r1 ∧ g = SmtValue.RegLan r2)
    (hX : ¬ ∃ r1 r2, x = SmtValue.RegLan r1 ∧ y = SmtValue.RegLan r2) :
    __smtx_model_eval_eq (SmtValue.Apply f x) (SmtValue.Apply g y) =
      __smtx_model_eval_and (__smtx_model_eval_eq f g)
        (__smtx_model_eval_eq x y) := by
  rw [smtx_model_eval_eq_not_reglan_pair f g hF,
    smtx_model_eval_eq_not_reglan_pair x y hX]
  simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_and,
    SmtEval.native_and]

private theorem vsm_apply_ext_aux :
    ∀ (n : Nat) (v w : SmtValue),
      vsm_num_apply_args v = n ->
      __smtx_apply_head_value v = __smtx_apply_head_value w ->
      vsm_num_apply_args v = vsm_num_apply_args w ->
      (∀ j, j < vsm_num_apply_args v ->
        __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) =
          __smtx_apply_arg_nth_value w j (vsm_num_apply_args w)) ->
      v = w := by
  intro n
  induction n with
  | zero =>
      intro v w hv hHead hCount _hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      all_goals
        cases w <;> simp [vsm_num_apply_args] at hCount
        simp [__smtx_apply_head_value] at hHead ⊢
        all_goals try exact hHead
  | succ n ih =>
      intro v w hv hHead hCount hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      case Apply f a =>
        cases w <;> simp [vsm_num_apply_args] at hCount
        case Apply g b =>
          have hCountFG : vsm_num_apply_args f = vsm_num_apply_args g := hCount
          have hLast :
              __smtx_apply_arg_nth_value (SmtValue.Apply f a) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply f a)) =
                __smtx_apply_arg_nth_value (SmtValue.Apply g b) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply g b)) :=
            hArgs (vsm_num_apply_args f) (by simp [vsm_num_apply_args])
          have hab : a = b := by
            simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, hCountFG,
              Smtm.native_nateq, native_ite] using hLast
          have hfg : f = g := by
            apply ih f g hv
            · simpa [__smtx_apply_head_value] using hHead
            · exact hCountFG
            · intro j hj
              have hjTop : j < vsm_num_apply_args (SmtValue.Apply f a) := by
                simp [vsm_num_apply_args]
                exact Nat.lt_succ_of_lt hj
              have hArg := hArgs j hjTop
              have hNeF : j ≠ vsm_num_apply_args f := by omega
              have hNeG : j ≠ vsm_num_apply_args g := by
                intro hEq
                apply hNeF
                rw [hCountFG, hEq]
              simpa [__smtx_apply_arg_nth_value, vsm_num_apply_args, hCountFG,
                Smtm.native_nateq, hNeF, hNeG, native_ite] using hArg
          subst hfg
          subst hab
          rfl

private theorem vsm_apply_ext
    (v w : SmtValue)
    (hHead : __smtx_apply_head_value v = __smtx_apply_head_value w)
    (hCount : vsm_num_apply_args v = vsm_num_apply_args w)
    (hArgs : ∀ j, j < vsm_num_apply_args v ->
      __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) =
        __smtx_apply_arg_nth_value w j (vsm_num_apply_args w)) :
    v = w :=
  vsm_apply_ext_aux (vsm_num_apply_args v) v w rfl hHead hCount hArgs

def tuplePrependValueRec
    (tailD : SmtDatatype) (tailVal : SmtValue) : Nat -> SmtValue -> SmtValue
  | 0, acc => acc
  | Nat.succ k, acc =>
      SmtValue.Apply (tuplePrependValueRec tailD tailVal k acc)
        (__smtx_apply_arg_nth_value tailVal k (__smtx_dt_num_sels tailD native_nat_zero))

private theorem tuplePrependValueRec_head
    (tailD : SmtDatatype) (tailVal : SmtValue) :
    ∀ k acc,
      __smtx_apply_head_value (tuplePrependValueRec tailD tailVal k acc) =
        __smtx_apply_head_value acc
  | 0, acc => by simp [tuplePrependValueRec]
  | Nat.succ k, acc => by
      simp [tuplePrependValueRec, __smtx_apply_head_value,
        tuplePrependValueRec_head tailD tailVal k acc]

private theorem tuplePrependValueRec_eq_components
    (tailD : SmtDatatype) (tailVal tailVal' acc acc' : SmtValue) :
    ∀ k,
      tuplePrependValueRec tailD tailVal k acc =
        tuplePrependValueRec tailD tailVal' k acc' ->
      acc = acc' ∧
        ∀ j, j < k ->
          __smtx_apply_arg_nth_value tailVal j (__smtx_dt_num_sels tailD native_nat_zero) =
            __smtx_apply_arg_nth_value tailVal' j (__smtx_dt_num_sels tailD native_nat_zero)
  | 0, hEq => by
      simp [tuplePrependValueRec] at hEq
      exact ⟨hEq, by intro j hj; omega⟩
  | Nat.succ k, hEq => by
      simp [tuplePrependValueRec] at hEq
      rcases hEq with ⟨hRec, hArg⟩
      rcases tuplePrependValueRec_eq_components tailD tailVal tailVal' acc acc' k hRec with
        ⟨hAcc, hArgs⟩
      constructor
      · exact hAcc
      · intro j hj
        by_cases hLast : j = k
        · subst j
          exact hArg
        · exact hArgs j (by omega)

private theorem smtx_model_eval_apply_of_dt_chain
    (M : SmtModel) (v x : SmtValue)
    (hHead : ∃ s d i, __smtx_apply_head_value v = SmtValue.DtCons s d i)
    (hx : x ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M v x = SmtValue.Apply v x := by
  cases x <;> simp [__smtx_model_eval_apply] at hx ⊢
  all_goals
    cases v <;> simp [__smtx_apply_head_value] at hHead ⊢

private theorem vsm_apply_arg_nth_ne_notvalue_of_non_none_aux :
    ∀ (n : Nat) (v : SmtValue),
      vsm_num_apply_args v = n ->
      __smtx_typeof_value v ≠ SmtType.None ->
      ∀ j, j < n -> __smtx_apply_arg_nth_value v j n ≠ SmtValue.NotValue := by
  intro n
  induction n with
  | zero =>
      intro v hvCount _hNN j hj
      omega
  | succ n ih =>
      intro v hvCount hNN j hj
      cases v <;> simp [vsm_num_apply_args] at hvCount
      case Apply f a =>
        have hCountF : vsm_num_apply_args f = n := by omega
        have hApplyNN :
            __smtx_typeof_apply_value (__smtx_typeof_value f)
                (__smtx_typeof_value a) ≠ SmtType.None := by
          simpa [__smtx_typeof_value] using hNN
        rcases typeof_apply_value_non_none_cases hApplyNN with
          ⟨A, B, hF, hA, hANN, _hBNN⟩
        by_cases hLast : j = vsm_num_apply_args f
        · have hAValue : a ≠ SmtValue.NotValue := by
            intro hNot
            apply hANN
            rw [← hA]
            simp [hNot, __smtx_typeof_value]
          subst j
          simpa [__smtx_apply_arg_nth_value, hCountF, Smtm.native_nateq,
            native_ite] using hAValue
        · have hjF : j < vsm_num_apply_args f := by omega
          have hFNN : __smtx_typeof_value f ≠ SmtType.None := by
            rw [hF]
            simp 
          have hRec := ih f hCountF hFNN j (by simpa [hCountF] using hjF)
          have hNe : j ≠ n := by omega
          simpa [__smtx_apply_arg_nth_value, hCountF, Smtm.native_nateq, hLast,
            hNe, native_ite] using hRec

private theorem vsm_apply_arg_nth_ne_notvalue_of_non_none
    (v : SmtValue)
    (hNN : __smtx_typeof_value v ≠ SmtType.None)
    {j : Nat}
    (hj : j < vsm_num_apply_args v) :
    __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) ≠ SmtValue.NotValue :=
  vsm_apply_arg_nth_ne_notvalue_of_non_none_aux
    (vsm_num_apply_args v) v rfl hNN j hj

private theorem tuple_selector_eval_eq_arg
    (M : SmtModel) (tailD : SmtDatatype) (tail : SmtTerm) (j : Nat)
    (hHead :
      __smtx_apply_head_value (__smtx_model_eval M tail) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero) :
    __smtx_model_eval M
        (SmtTerm.Apply
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl tailD) native_nat_zero j)
          tail) =
      __smtx_apply_arg_nth_value (__smtx_model_eval M tail) j
        (__smtx_dt_num_sels tailD native_nat_zero) := by
  simp [__smtx_model_eval, __smtx_model_eval_dt_sel, hHead, native_veq,
    native_ite, __eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
    SmtEval.native_streq]

private theorem tuple_value_arg_not_notvalue
    {v : SmtValue} {tailD : SmtDatatype} {j : Nat}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD))
    (hHead :
      __smtx_apply_head_value v =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero)
    (hCount :
      vsm_num_apply_args v = __smtx_dt_num_sels tailD native_nat_zero)
    (hj : j < __smtx_dt_num_sels tailD native_nat_zero) :
    __smtx_apply_arg_nth_value v j (__smtx_dt_num_sels tailD native_nat_zero) ≠
      SmtValue.NotValue := by
  have hNN : __smtx_typeof_value v ≠ SmtType.None := by
    rw [hTy]
    simp
  have hArg :=
    vsm_apply_arg_nth_ne_notvalue_of_non_none v hNN
      (by simpa [hCount] using hj)
  simpa [hCount] using hArg

private theorem smtx_model_eval_apply_eq_apply_of_not_dt_ops
    (M : SmtModel) (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f <;> simp [__smtx_model_eval]
  case DtSel s d i j => exact False.elim (hSel s d i j rfl)
  case DtTester s d i => exact False.elim (hTester s d i rfl)

private theorem tuple_prepend_rec_ne_dt_sel
    (tailD : SmtDatatype) (tail acc : SmtTerm)
    (hAcc : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) :
    ∀ k s d i j,
      __eo_to_smt_tuple_prepend_rec
        (__eo_to_smt_tuple_decl tailD) tailD tail k acc ≠
          SmtTerm.DtSel s d i j
  | 0, s, d, i, j => hAcc s d i j
  | Nat.succ k, s, d, i, j => by
      simp [__eo_to_smt_tuple_prepend_rec]

private theorem tuple_prepend_rec_ne_dt_tester
    (tailD : SmtDatatype) (tail acc : SmtTerm)
    (hAcc : ∀ s d i, acc ≠ SmtTerm.DtTester s d i) :
    ∀ k s d i,
      __eo_to_smt_tuple_prepend_rec
        (__eo_to_smt_tuple_decl tailD) tailD tail k acc ≠
          SmtTerm.DtTester s d i
  | 0, s, d, i => hAcc s d i
  | Nat.succ k, s, d, i => by
      simp [__eo_to_smt_tuple_prepend_rec]

private theorem tuple_value_head_zero_of_type
    {v : SmtValue} {c : SmtDatatypeCons}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null))) :
    __smtx_apply_head_value v =
      SmtValue.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl
          (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero := by
  rcases datatype_value_head_of_type hTy with ⟨i, hHead⟩
  have hiLt := datatype_head_index_lt hHead hTy
  have hi : i = 0 := by
    simpa [smtDatatypeNumCtors, __eo_to_smt_tuple_decl,
      __smtx_dd_lookup, native_streq, SmtEval.native_streq, native_ite] using hiLt
  subst i
  exact hHead

private theorem tuple_value_count_of_type
    {v : SmtValue} {tailD : SmtDatatype}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD))
    (hHead :
      __smtx_apply_head_value v =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero) :
    vsm_num_apply_args v = __smtx_dt_num_sels tailD native_nat_zero := by
  have hCount :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  simpa [__eo_to_smt_tuple_decl, __smtx_dd_lookup, native_streq,
    SmtEval.native_streq, native_ite, dt_num_sels_resolve] using hCount

private theorem tuple_prepend_rec_eval_eq_value_rec
    (M : SmtModel) (tailD : SmtDatatype) (tail acc : SmtTerm)
    (fullD : SmtDatatype)
    (hAccNoSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccNoTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hTailHead :
      __smtx_apply_head_value (__smtx_model_eval M tail) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero)
    (hTailTy :
      __smtx_typeof_value (__smtx_model_eval M tail) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD))
    (hTailCount :
      vsm_num_apply_args (__smtx_model_eval M tail) =
        __smtx_dt_num_sels tailD native_nat_zero)
    (hAccHead :
      __smtx_apply_head_value (__smtx_model_eval M acc) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl fullD) native_nat_zero) :
    ∀ k,
      k ≤ __smtx_dt_num_sels tailD native_nat_zero ->
      __smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec
            (__eo_to_smt_tuple_decl tailD) tailD tail k acc) =
        tuplePrependValueRec tailD (__smtx_model_eval M tail) k
          (__smtx_model_eval M acc)
  | 0, _hk => by
      simp [__eo_to_smt_tuple_prepend_rec, tuplePrependValueRec]
  | Nat.succ k, hk => by
      have hkLe : k ≤ __smtx_dt_num_sels tailD native_nat_zero :=
        Nat.le_of_succ_le hk
      have hkLt : k < __smtx_dt_num_sels tailD native_nat_zero :=
        Nat.lt_of_succ_le hk
      have ih :=
        tuple_prepend_rec_eval_eq_value_rec M tailD tail acc fullD
          hAccNoSel hAccNoTester hTailHead hTailTy hTailCount hAccHead k hkLe
      have hArgEval :=
        tuple_selector_eval_eq_arg M tailD tail k hTailHead
      have hArgNot :
          __smtx_apply_arg_nth_value (__smtx_model_eval M tail) k
              (__smtx_dt_num_sels tailD native_nat_zero) ≠
            SmtValue.NotValue :=
        tuple_value_arg_not_notvalue hTailTy hTailHead hTailCount hkLt
      have hRecHead :
          ∃ s d i,
            __smtx_apply_head_value
                (tuplePrependValueRec tailD (__smtx_model_eval M tail) k
                  (__smtx_model_eval M acc)) =
              SmtValue.DtCons s d i := by
        refine ⟨native_string_lit "@Tuple",
          __eo_to_smt_tuple_decl fullD, native_nat_zero, ?_⟩
        rw [tuplePrependValueRec_head, hAccHead]
      simp only [__eo_to_smt_tuple_prepend_rec, tuplePrependValueRec]
      rw [show
        __smtx_model_eval M
            (SmtTerm.Apply
              (__eo_to_smt_tuple_prepend_rec
                (__eo_to_smt_tuple_decl tailD) tailD tail k acc)
              (SmtTerm.Apply
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl tailD) native_nat_zero k)
                tail)) =
          __smtx_model_eval_apply M
            (__smtx_model_eval M
              (__eo_to_smt_tuple_prepend_rec
                (__eo_to_smt_tuple_decl tailD) tailD tail k acc))
            (__smtx_model_eval M
              (SmtTerm.Apply
                (SmtTerm.DtSel (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl tailD) native_nat_zero k)
                tail)) by
          exact smtx_model_eval_apply_eq_apply_of_not_dt_ops M
            (__eo_to_smt_tuple_prepend_rec
              (__eo_to_smt_tuple_decl tailD) tailD tail k acc)
            (SmtTerm.Apply
              (SmtTerm.DtSel (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl tailD) native_nat_zero k)
              tail)
            (tuple_prepend_rec_ne_dt_sel tailD tail acc hAccNoSel k)
            (tuple_prepend_rec_ne_dt_tester tailD tail acc hAccNoTester k)]
      rw [ih, hArgEval]
      exact smtx_model_eval_apply_of_dt_chain M
        (tuplePrependValueRec tailD (__smtx_model_eval M tail) k
          (__smtx_model_eval M acc))
        (__smtx_apply_arg_nth_value (__smtx_model_eval M tail) k
          (__smtx_dt_num_sels tailD native_nat_zero))
        hRecHead hArgNot

theorem tuple_prepend_eval_eq_value_rec
    (M : SmtModel) (hM : model_wf M)
    (head tail : SmtTerm) (headTy : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = headTy)
    (hTailTy :
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)))
    (hPrependNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
        SmtType.None) :
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
    __smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail) =
      tuplePrependValueRec tailD (__smtx_model_eval M tail)
        (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M head)) := by
  intro tailD fullD
  let seed :=
    SmtTerm.Apply
      (SmtTerm.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl fullD) native_nat_zero) head
  have hFullWf :
      __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD)) = true := by
    cases hWf :
        __smtx_type_wf
          (SmtType.Datatype (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD))
    · exfalso
      apply hPrependNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      dsimp [fullD, __eo_to_smt_tuple_decl] at hWf
      simp [__eo_to_smt_tuple_prepend_of_type,
        __eo_to_smt_tuple_decl, native_streq, native_and, native_ite, hWf]
    · rfl
  have hTerm :
      __eo_to_smt_tuple_prepend head headTy tail =
        __eo_to_smt_tuple_prepend_rec
          (__eo_to_smt_tuple_decl tailD) tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero) seed := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    dsimp [fullD, __eo_to_smt_tuple_decl] at hFullWf
    simp [__eo_to_smt_tuple_prepend_of_type, tailD, fullD, seed,
      __eo_to_smt_tuple_decl, native_streq, native_and, native_ite, hFullWf]
  have hTailEvalTy :
      __smtx_typeof_value (__smtx_model_eval M tail) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) := by
    have hTailNN : term_has_non_none_type tail := by
      unfold term_has_non_none_type
      rw [hTailTy]
      simp 
    have hPres :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM tail hTailNN
    rw [hTailTy] at hPres
    simpa [tailD] using hPres
  have hTailHead :
      __smtx_apply_head_value (__smtx_model_eval M tail) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero :=
    tuple_value_head_zero_of_type (by simpa [tailD] using hTailEvalTy)
  have hTailCount :
      vsm_num_apply_args (__smtx_model_eval M tail) =
        __smtx_dt_num_sels tailD native_nat_zero :=
    tuple_value_count_of_type hTailEvalTy hTailHead
  have hHeadTermNN : __smtx_typeof head ≠ SmtType.None :=
    TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
      tail head headTy c hTailTy hPrependNN
  have hHeadNN : headTy ≠ SmtType.None := by
    rw [← hHeadTy]
    exact hHeadTermNN
  have hHeadEvalTy :
      __smtx_typeof_value (__smtx_model_eval M head) = headTy := by
    have hHeadTermNN' : term_has_non_none_type head := by
      unfold term_has_non_none_type
      exact hHeadTermNN
    have hPres :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM head hHeadTermNN'
    rw [hHeadTy] at hPres
    exact hPres
  have hHeadEvalNN : __smtx_model_eval M head ≠ SmtValue.NotValue := by
    intro hNot
    apply hHeadNN
    rw [← hHeadEvalTy, hNot]
    simp [__smtx_typeof_value]
  have hSeedEval :
      __smtx_model_eval M seed =
        SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M head) := by
    cases hHeadEval : __smtx_model_eval M head <;>
      simp [seed, __smtx_model_eval, __smtx_model_eval_apply,
        hHeadEval] at hHeadEvalNN ⊢
  have hAccHead :
      __smtx_apply_head_value (__smtx_model_eval M seed) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl fullD) native_nat_zero := by
    rw [hSeedEval]
    simp [__smtx_apply_head_value]
  rw [hTerm]
  have hRec :=
    tuple_prepend_rec_eval_eq_value_rec M tailD tail seed fullD
      (by intro s d i j h; simp [seed] at h)
      (by intro s d i h; simp [seed] at h)
      hTailHead hTailEvalTy hTailCount hAccHead
      (__smtx_dt_num_sels tailD native_nat_zero) (Nat.le_refl _)
  simpa [hSeedEval] using hRec

private theorem tuplePrependValueRec_seed_arg_proper
    (tailD : SmtDatatype) (tailVal : SmtValue)
    (seedF seedA : SmtValue) :
    ∀ k,
      SmtValueProperSubterm seedA
        (tuplePrependValueRec tailD tailVal k
          (SmtValue.Apply seedF seedA))
  | 0 => by
      simp [tuplePrependValueRec]
      exact SmtValueProperSubterm.app_arg
  | Nat.succ k => by
      simp [tuplePrependValueRec]
      exact SmtValueProperSubterm.app_fun
        (tuplePrependValueRec_seed_arg_proper tailD tailVal seedF seedA k)

theorem tuple_apply_head_model_eval_proper
    (M : SmtModel) (hM : model_wf M) (head tail : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail) ->
    SmtValueProperSubterm
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail))) := by
  intro hTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      tail head hTrans with
    ⟨c, hTailTy⟩
  have hEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt head) (__eo_to_smt tail)
    (__smtx_typeof (__eo_to_smt head)) c rfl hTailTy hTrans
  dsimp at hEval
  change
    SmtValueProperSubterm
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)))
  rw [hEval]
  exact tuplePrependValueRec_seed_arg_proper
    (SmtDatatype.sum c SmtDatatype.null)
    (__smtx_model_eval M (__eo_to_smt tail))
    (SmtValue.DtCons (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl
        (SmtDatatype.sum
          (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt head)) c)
          SmtDatatype.null)) native_nat_zero)
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)

private def tuplePrependValueRecAt
    (total : Nat) (tailVal : SmtValue) : Nat -> SmtValue -> SmtValue
  | 0, acc => acc
  | Nat.succ k, acc =>
      SmtValue.Apply (tuplePrependValueRecAt total tailVal k acc)
        (__smtx_apply_arg_nth_value tailVal k total)

private theorem tuplePrependValueRec_eq_at
    (tailD : SmtDatatype) (tailVal acc : SmtValue) :
    ∀ k,
      tuplePrependValueRec tailD tailVal k acc =
        tuplePrependValueRecAt
          (__smtx_dt_num_sels tailD native_nat_zero) tailVal k acc
  | 0 => by
      simp [tuplePrependValueRec, tuplePrependValueRecAt]
  | Nat.succ k => by
      simp [tuplePrependValueRec, tuplePrependValueRecAt,
        tuplePrependValueRec_eq_at tailD tailVal acc k]

private theorem tuplePrependValueRecAt_apply_prefix
    (v a acc : SmtValue) :
    ∀ {n total : Nat},
      n ≤ total ->
      tuplePrependValueRecAt (Nat.succ total) (SmtValue.Apply v a) n acc =
        tuplePrependValueRecAt total v n acc
  | 0, total, _ => by
      simp [tuplePrependValueRecAt]
  | Nat.succ n, total, hLe => by
      have hnLe : n ≤ total := Nat.le_of_succ_le hLe
      have hnNe : n ≠ total := by omega
      have hArg :
          __smtx_apply_arg_nth_value (SmtValue.Apply v a) n (Nat.succ total) =
            __smtx_apply_arg_nth_value v n total := by
        simp [__smtx_apply_arg_nth_value, Smtm.native_nateq, native_ite, hnNe]
      simp [tuplePrependValueRecAt,
        tuplePrependValueRecAt_apply_prefix v a acc hnLe, hArg]

private theorem tuplePrependValueRecAt_size_lt_of_head_lt :
    ∀ (tailVal acc : SmtValue),
      sizeOf (__smtx_apply_head_value tailVal) < sizeOf acc ->
      sizeOf tailVal <
        sizeOf
          (tuplePrependValueRecAt (vsm_num_apply_args tailVal) tailVal
            (vsm_num_apply_args tailVal) acc)
  | SmtValue.Apply f a, acc, hHeadLt => by
      have hRec :=
        tuplePrependValueRecAt_size_lt_of_head_lt f acc hHeadLt
      have hPrefix :=
        tuplePrependValueRecAt_apply_prefix f a acc
          (n := vsm_num_apply_args f) (total := vsm_num_apply_args f)
          (Nat.le_refl _)
      simp [tuplePrependValueRecAt, vsm_num_apply_args,
        __smtx_apply_arg_nth_value, Smtm.native_nateq, native_ite,
        hPrefix]
      omega
  | SmtValue.NotValue, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Boolean b, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Numeral n, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Rational q, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Binary w n, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Map m, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Fun s T U, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Set m, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Seq xs, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.Char c, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.UValue i j, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.RegLan r, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt
  | SmtValue.DtCons s d i, acc, hHeadLt => by simpa [tuplePrependValueRecAt, vsm_num_apply_args, __smtx_apply_head_value] using hHeadLt

private theorem tuple_tail_head_size_lt_seed
    (headTy : SmtType) (c : SmtDatatypeCons) (headVal : SmtValue) :
    sizeOf
        (SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) native_nat_zero) <
      sizeOf
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum
                (SmtDatatypeCons.cons headTy c) SmtDatatype.null))
            native_nat_zero)
          headVal) := by
  simp [__eo_to_smt_tuple_decl]
  omega

theorem tuple_apply_tail_model_eval_size_lt
    (M : SmtModel) (hM : model_wf M) (head tail : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail) ->
    sizeOf (__smtx_model_eval M (__eo_to_smt tail)) <
      sizeOf
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail))) := by
  intro hTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      tail head hTrans with
    ⟨c, hTailTy⟩
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD :=
    SmtDatatype.sum
      (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt head)) c)
      SmtDatatype.null
  let tailVal := __smtx_model_eval M (__eo_to_smt tail)
  let seed :=
    SmtValue.Apply
      (SmtValue.DtCons (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl fullD) native_nat_zero)
      (__smtx_model_eval M (__eo_to_smt head))
  have hEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt head) (__eo_to_smt tail)
    (__smtx_typeof (__eo_to_smt head)) c rfl hTailTy hTrans
  dsimp at hEval
  have hTailEvalTy :
      __smtx_typeof_value tailVal =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) := by
    have hTailNN : term_has_non_none_type (__eo_to_smt tail) := by
      unfold term_has_non_none_type
      rw [hTailTy]
      simp
    have hPres :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt tail) hTailNN
    rw [hTailTy] at hPres
    simpa [tailVal, tailD] using hPres
  have hTailHead :
      __smtx_apply_head_value tailVal =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero :=
    tuple_value_head_zero_of_type (by simpa [tailD] using hTailEvalTy)
  have hTailCount :
      vsm_num_apply_args tailVal =
        __smtx_dt_num_sels tailD native_nat_zero :=
    tuple_value_count_of_type hTailEvalTy hTailHead
  have hHeadLt :
      sizeOf (__smtx_apply_head_value tailVal) < sizeOf seed := by
    rw [hTailHead]
    exact
      tuple_tail_head_size_lt_seed
        (__smtx_typeof (__eo_to_smt head)) c
        (__smtx_model_eval M (__eo_to_smt head))
  have hSizeLt :
      sizeOf tailVal <
        sizeOf
          (tuplePrependValueRecAt (vsm_num_apply_args tailVal) tailVal
            (vsm_num_apply_args tailVal) seed) :=
    tuplePrependValueRecAt_size_lt_of_head_lt tailVal seed hHeadLt
  change
    sizeOf tailVal <
      sizeOf
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend (__eo_to_smt head)
            (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)))
  rw [hEval]
  dsimp [tailD, fullD, seed] at hSizeLt ⊢
  rw [tuplePrependValueRec_eq_at]
  rw [← hTailCount]
  exact hSizeLt

private theorem tuplePrependValueRec_seed_apply_ne_reglan
    (tailD : SmtDatatype) (tailVal : SmtValue)
    (fullD : SmtDatatype) (headVal : SmtValue) :
    ∀ k r,
      tuplePrependValueRec tailD tailVal k
          (SmtValue.Apply
            (SmtValue.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl fullD) native_nat_zero)
            headVal) ≠
        SmtValue.RegLan r
  | 0, r => by simp [tuplePrependValueRec]
  | Nat.succ k, r => by simp [tuplePrependValueRec]

theorem tuple_apply_model_eval_ne_reglan
    (M : SmtModel) (hM : model_wf M) (head tail : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail) ->
    ∀ r,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail)) ≠
        SmtValue.RegLan r := by
  intro hTrans r
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      tail head hTrans with
    ⟨c, hTailTy⟩
  have hEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt head) (__eo_to_smt tail)
    (__smtx_typeof (__eo_to_smt head)) c rfl hTailTy hTrans
  dsimp at hEval
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtValue.RegLan r
  rw [hEval]
  exact tuplePrependValueRec_seed_apply_ne_reglan
    (SmtDatatype.sum c SmtDatatype.null)
    (__smtx_model_eval M (__eo_to_smt tail))
    (SmtDatatype.sum
      (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt head)) c)
      SmtDatatype.null)
    (__smtx_model_eval M (__eo_to_smt head))
    (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)
    r

private theorem tuplePrependValueRec_seed_apply_eq_iff
    (tailD fullD : SmtDatatype)
    (headVal headVal' tailVal tailVal' : SmtValue)
    (hTailHead :
      __smtx_apply_head_value tailVal =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero)
    (hTailHead' :
      __smtx_apply_head_value tailVal' =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero)
    (hTailCount :
      vsm_num_apply_args tailVal = __smtx_dt_num_sels tailD native_nat_zero)
    (hTailCount' :
      vsm_num_apply_args tailVal' = __smtx_dt_num_sels tailD native_nat_zero) :
    tuplePrependValueRec tailD tailVal (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          headVal) =
      tuplePrependValueRec tailD tailVal' (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          headVal') ↔
      headVal = headVal' ∧ tailVal = tailVal' := by
  constructor
  · intro hEq
    rcases tuplePrependValueRec_eq_components tailD tailVal tailVal'
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          headVal)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          headVal')
        (__smtx_dt_num_sels tailD native_nat_zero) hEq with
      ⟨hSeed, hArgs⟩
    have hHeadVal : headVal = headVal' := by
      cases hSeed
      exact rfl
    have hTailVal : tailVal = tailVal' := by
      apply vsm_apply_ext
      · rw [hTailHead, hTailHead']
      · rw [hTailCount, hTailCount']
      · intro j hj
        have hj' : j < __smtx_dt_num_sels tailD native_nat_zero := by
          simpa [hTailCount] using hj
        have hArg := hArgs j hj'
        simpa [hTailCount, hTailCount'] using hArg
    exact ⟨hHeadVal, hTailVal⟩
  · intro h
    rcases h with ⟨rfl, rfl⟩
    rfl

private theorem eo_eq_eq_of_true {c c2 : Term} :
    __eo_eq c c2 = Term.Boolean true ->
    c2 = c := by
  cases c <;> cases c2 <;> simp [__eo_eq, native_teq]

private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_and_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) =
      SmtTerm.and (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

theorem eo_eq_has_bool_type_of_eq_has_bool_type
    (t s B : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t) s) := by
  intro hOuter
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply Term.eq t) s) B hOuter with
    ⟨_hTyEq, hEqNN⟩
  unfold RuleProofs.eo_has_bool_type
  rw [eo_to_smt_eq_eq, typeof_eq_eq]
  exact
    (RuleProofs.smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt t))
      (__smtx_typeof (__eo_to_smt s))).mpr
      (by
        have hEqNN' :
            __smtx_typeof_eq (__smtx_typeof (__eo_to_smt t))
                (__smtx_typeof (__eo_to_smt s)) ≠
              SmtType.None := by
          simpa [eo_to_smt_eq_eq, typeof_eq_eq] using hEqNN
        cases ht : __smtx_typeof (__eo_to_smt t) <;>
          cases hs : __smtx_typeof (__eo_to_smt s) <;>
            simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
              native_Teq, ht, hs] at hEqNN' ⊢ <;> exact hEqNN')

private def tuplePrependHeadTypeOfType : SmtType -> SmtType
  | SmtType.Datatype _
      (SmtDatatypeDecl.cons _
        (SmtDatatype.sum (SmtDatatypeCons.cons T _) SmtDatatype.null)
        SmtDatatypeDecl.nil) => T
  | _ => SmtType.None

private def tuplePrependTailConsOfType : SmtType -> SmtDatatypeCons
  | SmtType.Datatype _
      (SmtDatatypeDecl.cons _
        (SmtDatatype.sum (SmtDatatypeCons.cons _ c) SmtDatatype.null)
        SmtDatatypeDecl.nil) => c
  | _ => SmtDatatypeCons.unit

private theorem tuple_eq_has_bool_type_components
    (a as b bs : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as))
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs)) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) ∧
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq as) bs) := by
  intro hBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs) hBool with
    ⟨hTyEq, hTyNN⟩
  change
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) =
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) (__eo_to_smt bs)) at hTyEq
  change
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) ≠
      SmtType.None at hTyNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      as a hTyNN with
    ⟨c, hAsTy⟩
  have hRightNN :
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) (__eo_to_smt bs)) ≠
      SmtType.None := by
    rw [← hTyEq]
    exact hTyNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      bs b hRightNN with
    ⟨c', hBsTy⟩
  have hLeftFull :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt as) (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
      c hAsTy hTyNN
  have hRightFull :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt bs) (__eo_to_smt b) (__smtx_typeof (__eo_to_smt b))
      c' hBsTy hRightNN
  rw [hLeftFull, hRightFull] at hTyEq
  have hHeadTy :
      __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) := by
    have h := congrArg tuplePrependHeadTypeOfType hTyEq
    simpa [tuplePrependHeadTypeOfType, __eo_to_smt_tuple_decl] using h
  have hTailCons : c = c' := by
    have h := congrArg tuplePrependTailConsOfType hTyEq
    simpa [tuplePrependTailConsOfType, __eo_to_smt_tuple_decl] using h
  have hHeadNN : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
    TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
      (__eo_to_smt as) (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
      c hAsTy hTyNN
  have hTailTy :
      __smtx_typeof (__eo_to_smt as) = __smtx_typeof (__eo_to_smt bs) := by
    rw [hAsTy, hBsTy, hTailCons]
  have hTailNN : __smtx_typeof (__eo_to_smt as) ≠ SmtType.None := by
    rw [hAsTy]
    simp
  constructor
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b hHeadTy hHeadNN
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type as bs hTailTy hTailNN

private theorem smt_model_eval_pair_not_reglan_of_non_reg_type
    (M : SmtModel) (hM : model_wf M)
    (x y : SmtTerm) (A : SmtType)
    (hxTy : __smtx_typeof x = A)
    (hyTy : __smtx_typeof y = A)
    (hANN : A ≠ SmtType.None)
    (hAReg : A ≠ SmtType.RegLan) :
    ¬ ∃ r1 r2,
      __smtx_model_eval M x = SmtValue.RegLan r1 ∧
        __smtx_model_eval M y = SmtValue.RegLan r2 := by
  intro hReg
  rcases hReg with ⟨r1, _r2, hxReg, _hyReg⟩
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact hANN
  have hxPres :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM x hxNN
  rw [hxTy] at hxPres
  apply hAReg
  rw [← hxPres, hxReg]
  simp [__smtx_typeof_value]

private theorem typeof_apply_same_head_arg_type_eq
    {F X Y : SmtType}
    (hEq : __smtx_typeof_apply F X = __smtx_typeof_apply F Y)
    (hNN : __smtx_typeof_apply F X ≠ SmtType.None) :
    X = Y := by
  have hYNN : __smtx_typeof_apply F Y ≠ SmtType.None := by
    rw [← hEq]
    exact hNN
  rcases typeof_apply_non_none_cases hNN with
    ⟨A, B, hHead, hX, _hANN, _hBNN⟩
  rcases typeof_apply_non_none_cases hYNN with
    ⟨A', B', hHead', hY, _hA'NN, _hB'NN⟩
  have hAA : A = A' := by
    rcases hHead with hHead | hHead <;>
      rcases hHead' with hHead' | hHead'
    · cases hHead
      cases hHead'
      rfl
    · cases hHead
      cases hHead'
    · cases hHead
      cases hHead'
    · cases hHead
      cases hHead'
      rfl
  rw [hX, hY, hAA]

private theorem typeof_apply_eq_of_same_head_non_none
    {F X Y : SmtType}
    (hX : __smtx_typeof_apply F X ≠ SmtType.None)
    (hY : __smtx_typeof_apply F Y ≠ SmtType.None) :
    __smtx_typeof_apply F X = __smtx_typeof_apply F Y := by
  rcases typeof_apply_non_none_cases hX with
    ⟨A, B, hHead, hArg, hANN, _hBNN⟩
  rcases typeof_apply_non_none_cases hY with
    ⟨A', B', hHead', hArg', _hA'NN, _hB'NN⟩
  have hBB : B = B' := by
    rcases hHead with hHead | hHead <;>
      rcases hHead' with hHead' | hHead'
    · cases hHead
      cases hHead'
      rfl
    · cases hHead
      cases hHead'
    · cases hHead
      cases hHead'
    · cases hHead
      cases hHead'
      rfl
  have hLeft :
      __smtx_typeof_apply F X = B := by
    rcases hHead with hHead | hHead <;>
      rw [hHead, hArg] <;>
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq, hANN]
  have hRight :
      __smtx_typeof_apply F Y = B' := by
    rcases hHead' with hHead' | hHead' <;>
      rw [hHead', hArg'] <;>
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq, _hA'NN]
  rw [hLeft, hRight, hBB]

private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] :
    (p ↔ q) -> decide p = decide q := by
  intro h
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢

private theorem tuple_prepend_eval_eq_and
    (M : SmtModel) (hM : model_wf M) (a as b bs : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as))
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs)) ->
    __smtx_model_eval_eq
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs))) =
    __smtx_model_eval_and
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)))
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt as))
        (__smtx_model_eval M (__eo_to_smt bs))) := by
  intro hBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs) hBool with
    ⟨hTyEq, hTyNN⟩
  change
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) =
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) (__eo_to_smt bs)) at hTyEq
  change
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) ≠
      SmtType.None at hTyNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      as a hTyNN with
    ⟨c, hAsTy⟩
  have hRightNN :
      __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) (__eo_to_smt bs)) ≠
      SmtType.None := by
    rw [← hTyEq]
    exact hTyNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      bs b hRightNN with
    ⟨c', hBsTy⟩
  have hLeftFull :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt as) (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
      c hAsTy hTyNN
  have hRightFull :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt bs) (__eo_to_smt b) (__smtx_typeof (__eo_to_smt b))
      c' hBsTy hRightNN
  rw [hLeftFull, hRightFull] at hTyEq
  have hHeadTy :
      __smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b) := by
    have h := congrArg tuplePrependHeadTypeOfType hTyEq
    simpa [tuplePrependHeadTypeOfType, __eo_to_smt_tuple_decl] using h
  have hTailCons : c = c' := by
    have h := congrArg tuplePrependTailConsOfType hTyEq
    simpa [tuplePrependTailConsOfType, __eo_to_smt_tuple_decl] using h
  have hBsTyC :
      __smtx_typeof (__eo_to_smt bs) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum c SmtDatatype.null)) := by
    rw [hBsTy, hTailCons]
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD :=
    SmtDatatype.sum
      (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt a)) c)
      SmtDatatype.null
  have hEvalLeft :
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)) =
      tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt as))
        (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M (__eo_to_smt a))) := by
    change
      __smtx_model_eval M
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) =
      tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt as))
        (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M (__eo_to_smt a)))
    simpa [tailD, fullD] using
      tuple_prepend_eval_eq_value_rec M hM
        (__eo_to_smt a) (__eo_to_smt as)
        (__smtx_typeof (__eo_to_smt a)) c rfl hAsTy hTyNN
  have hEvalRight :
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs)) =
      tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt bs))
        (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M (__eo_to_smt b))) := by
    have hEvalRight0 :=
      tuple_prepend_eval_eq_value_rec M hM
        (__eo_to_smt b) (__eo_to_smt bs)
        (__smtx_typeof (__eo_to_smt b)) c' rfl hBsTy hRightNN
    change
      __smtx_model_eval M
        (__eo_to_smt_tuple_prepend (__eo_to_smt b)
          (__smtx_typeof (__eo_to_smt b)) (__eo_to_smt bs)) =
      tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt bs))
        (__smtx_dt_num_sels tailD native_nat_zero)
        (SmtValue.Apply
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl fullD) native_nat_zero)
          (__smtx_model_eval M (__eo_to_smt b)))
    simpa [tailD, fullD, hHeadTy, hTailCons] using hEvalRight0
  have hAsEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt as)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) := by
    have hAsNN : term_has_non_none_type (__eo_to_smt as) := by
      unfold term_has_non_none_type
      rw [hAsTy]
      simp 
    have hPres :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt as) hAsNN
    rw [hAsTy] at hPres
    simpa [tailD] using hPres
  have hBsEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt bs)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) := by
    have hBsNN : term_has_non_none_type (__eo_to_smt bs) := by
      unfold term_has_non_none_type
      rw [hBsTyC]
      simp 
    have hPres :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt bs) hBsNN
    rw [hBsTyC] at hPres
    simpa [tailD] using hPres
  have hAsHead :
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt as)) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero :=
    tuple_value_head_zero_of_type (by simpa [tailD] using hAsEvalTy)
  have hBsHead :
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt bs)) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl tailD) native_nat_zero :=
    tuple_value_head_zero_of_type (by simpa [tailD] using hBsEvalTy)
  have hAsCount :
      vsm_num_apply_args (__smtx_model_eval M (__eo_to_smt as)) =
        __smtx_dt_num_sels tailD native_nat_zero :=
    tuple_value_count_of_type hAsEvalTy hAsHead
  have hBsCount :
      vsm_num_apply_args (__smtx_model_eval M (__eo_to_smt bs)) =
        __smtx_dt_num_sels tailD native_nat_zero :=
    tuple_value_count_of_type hBsEvalTy hBsHead
  rcases CongSupport.tuple_prepend_head_non_reg_of_non_none
      (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)
      c hAsTy hTyNN with
    ⟨A, hATy, hANN, hAReg⟩
  have hBTy : __smtx_typeof (__eo_to_smt b) = A := by
    rw [← hHeadTy]
    exact hATy
  have hHeadNoReg :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt a) (__eo_to_smt b) A hATy hBTy hANN hAReg
  have hTailNoReg :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt as) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt bs) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt as) (__eo_to_smt bs)
      (SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl tailD))
      (by simpa [tailD] using hAsTy)
      (by simpa [tailD] using hBsTyC)
      (by simp [tailD])
      (by simp [tailD])
  rw [hEvalLeft, hEvalRight]
  have hFullNoReg :
      ¬ ∃ r1 r2,
        tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt as))
            (__smtx_dt_num_sels tailD native_nat_zero)
            (SmtValue.Apply
              (SmtValue.DtCons (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl fullD) native_nat_zero)
              (__smtx_model_eval M (__eo_to_smt a))) =
          SmtValue.RegLan r1 ∧
        tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt bs))
            (__smtx_dt_num_sels tailD native_nat_zero)
            (SmtValue.Apply
              (SmtValue.DtCons (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl fullD) native_nat_zero)
              (__smtx_model_eval M (__eo_to_smt b))) =
          SmtValue.RegLan r2 := by
    intro hReg
    rcases hReg with ⟨r1, _r2, hLeftReg, _hRightReg⟩
    exact
      (tuplePrependValueRec_seed_apply_ne_reglan tailD
        (__smtx_model_eval M (__eo_to_smt as)) fullD
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_dt_num_sels tailD native_nat_zero) r1) hLeftReg
  rw [smtx_model_eval_eq_not_reglan_pair _ _ hFullNoReg,
    smtx_model_eval_eq_not_reglan_pair _ _ hHeadNoReg,
    smtx_model_eval_eq_not_reglan_pair _ _ hTailNoReg]
  have hFullIff :=
    tuplePrependValueRec_seed_apply_eq_iff tailD fullD
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b))
      (__smtx_model_eval M (__eo_to_smt as))
      (__smtx_model_eval M (__eo_to_smt bs))
      hAsHead hBsHead hAsCount hBsCount
  rw [show
      decide
          (tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt as))
              (__smtx_dt_num_sels tailD native_nat_zero)
              (SmtValue.Apply
                (SmtValue.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD) native_nat_zero)
                (__smtx_model_eval M (__eo_to_smt a))) =
            tuplePrependValueRec tailD (__smtx_model_eval M (__eo_to_smt bs))
              (__smtx_dt_num_sels tailD native_nat_zero)
              (SmtValue.Apply
                (SmtValue.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl fullD) native_nat_zero)
                (__smtx_model_eval M (__eo_to_smt b)))) =
        decide
          (__smtx_model_eval M (__eo_to_smt a) =
              __smtx_model_eval M (__eo_to_smt b) ∧
            __smtx_model_eval M (__eo_to_smt as) =
              __smtx_model_eval M (__eo_to_smt bs)) from
        decide_eq_of_iff hFullIff]
  by_cases hHeadEq :
      __smtx_model_eval M (__eo_to_smt a) =
        __smtx_model_eval M (__eo_to_smt b) <;>
    by_cases hTailEq :
      __smtx_model_eval M (__eo_to_smt as) =
        __smtx_model_eval M (__eo_to_smt bs) <;>
      simp [hHeadEq, hTailEq, __smtx_model_eval_and,
        SmtEval.native_and]

theorem tuple_apply_model_eval_eq_false_of_component
    (M : SmtModel) (hM : model_wf M) (a as b bs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as) ->
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs) ->
    (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false ∨
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt as))
        (__smtx_model_eval M (__eo_to_smt bs)) = SmtValue.Boolean false) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hComponent
  let left := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as
  let right := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) b) bs
  by_cases hTyEq :
      __smtx_typeof (__eo_to_smt left) =
        __smtx_typeof (__eo_to_smt right)
  · have hBool :
        RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq left) right) :=
      RuleProofs.eo_has_bool_type_eq_of_same_smt_type
        left right hTyEq hLeftTrans
    have hEval := tuple_prepend_eval_eq_and M hM a as b bs hBool
    change
        __smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt left))
            (__smtx_model_eval M (__eo_to_smt right)) =
          __smtx_model_eval_and
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt a))
              (__smtx_model_eval M (__eo_to_smt b)))
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt as))
              (__smtx_model_eval M (__eo_to_smt bs))) at hEval
    rw [hEval]
    rcases hComponent with hHead | hTail
    · rcases model_eval_eq_is_boolean
          (__smtx_model_eval M (__eo_to_smt as))
          (__smtx_model_eval M (__eo_to_smt bs)) with
        ⟨bt, hTailBool⟩
      rw [hHead, hTailBool]
      simp [__smtx_model_eval_and, SmtEval.native_and]
    · rcases model_eval_eq_is_boolean
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) with
        ⟨bh, hHeadBool⟩
      rw [hTail, hHeadBool]
      cases bh <;> simp [__smtx_model_eval_and, SmtEval.native_and]
  · have hLeftTyNeReg :
        __smtx_typeof (__eo_to_smt left) ≠ SmtType.RegLan := by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_prepend (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) ≠
          SmtType.RegLan
      rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
          as a hLeftTrans with
        ⟨c, hTailTy⟩
      rw [TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
        (__eo_to_smt as) (__eo_to_smt a)
        (__smtx_typeof (__eo_to_smt a)) c hTailTy hLeftTrans]
      simp
    have hLeftValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt left)) =
          __smtx_typeof (__eo_to_smt left) :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt left)
        (by
          unfold term_has_non_none_type
          exact hLeftTrans)
    have hRightValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt right)) =
          __smtx_typeof (__eo_to_smt right) :=
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt right)
        (by
          unfold term_has_non_none_type
          exact hRightTrans)
    have hNe :
        __smtx_model_eval M (__eo_to_smt left) ≠
          __smtx_model_eval M (__eo_to_smt right) := by
      intro hEq
      apply hTyEq
      have hValTyEq :
          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt left)) =
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt right)) := by
        rw [hEq]
      rw [hLeftValTy, hRightValTy] at hValTyEq
      exact hValTyEq
    have hNoReg :
        ¬ ∃ r₁ r₂,
          __smtx_model_eval M (__eo_to_smt left) = SmtValue.RegLan r₁ ∧
            __smtx_model_eval M (__eo_to_smt right) = SmtValue.RegLan r₂ := by
      intro hReg
      rcases hReg with ⟨r₁, _r₂, hLeftReg, _hRightReg⟩
      rw [hLeftReg] at hLeftValTy
      exact hLeftTyNeReg hLeftValTy.symm
    rw [smtx_model_eval_eq_not_reglan_pair _ _ hNoReg]
    simp [hNe]

private theorem mk_dt_cons_eq_stuck_left (s : Term) :
    __mk_dt_cons_eq Term.Stuck s = Term.Stuck := by
  cases s <;> rfl

private theorem mk_dt_cons_eq_stuck_right (t : Term) :
    __mk_dt_cons_eq t Term.Stuck = Term.Stuck := by
  cases t <;> rfl

private inductive DtConsSpineRoot :
    Term -> native_String -> DatatypeDecl -> native_Nat -> Prop where
  | root (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      DtConsSpineRoot (Term.DtCons s d i) s d i
  | app {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
      (x : Term) :
      DtConsSpineRoot t s d i ->
      DtConsSpineRoot (Term.Apply t x) s d i

private theorem dtConsSpineRoot_apply_generic
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) (x : Term) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  induction hSp generalizing x with
  | root s d i =>
      rfl
  | app x' hSp ih =>
      cases hSp with
      | root s d i =>
          rfl
      | app x'' hSp' =>
          cases hSp' with
          | root s d i =>
              rfl
          | app x''' hSp'' =>
              cases hSp'' <;> rfl

private inductive CtorSpineRoot : Term -> Term -> Prop where
  | tuple :
      CtorSpineRoot (Term.UOp UserOp.tuple) (Term.UOp UserOp.tuple)
  | tupleUnit :
      CtorSpineRoot (Term.UOp UserOp.tuple_unit) (Term.UOp UserOp.tuple_unit)
  | dtCons (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      CtorSpineRoot (Term.DtCons s d i) (Term.DtCons s d i)
  | app {t root : Term} (x : Term) :
      CtorSpineRoot t root ->
      CtorSpineRoot (Term.Apply t x) root

private inductive CtorSpineEq : Term -> Term -> Term -> Prop where
  | tuple :
      CtorSpineEq (Term.UOp UserOp.tuple) (Term.UOp UserOp.tuple)
        (Term.UOp UserOp.tuple)
  | tupleUnit :
      CtorSpineEq (Term.UOp UserOp.tuple_unit) (Term.UOp UserOp.tuple_unit)
        (Term.UOp UserOp.tuple_unit)
  | dtCons (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
      CtorSpineEq (Term.DtCons s d i) (Term.DtCons s d i)
        (Term.DtCons s d i)
  | app {t s root : Term} (x y : Term) :
      CtorSpineEq t s root ->
      CtorSpineEq (Term.Apply t x) (Term.Apply s y) root

private theorem ctorSpineRoot_apply_generic_of_not_tuple_one_arg
    {f root : Term}
    (hSp : CtorSpineRoot f root) (a : Term)
    (hNotTupleOne : ∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) :
    __eo_to_smt (Term.Apply f a) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a) := by
  cases hSp with
  | tuple =>
      rfl
  | tupleUnit =>
      rfl
  | dtCons s d i =>
      rfl
  | app x hPrev =>
      cases hPrev with
      | tuple =>
          exact False.elim (hNotTupleOne x rfl)
      | tupleUnit =>
          rfl
      | dtCons s d i =>
          rfl
      | app y hPrev' =>
          cases hPrev' <;> try rfl
          case app z hPrev'' =>
            cases hPrev'' <;> rfl

private theorem ctorSpineRoot_to_smt_ne_dt_sel
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j := by
  induction hSp with
  | tuple =>
      intro s d i j h
      cases h
  | tupleUnit =>
      intro s d i j h
      rw [TranslationProofs.eo_to_smt_term_tuple_unit] at h
      cases h
  | dtCons s d i =>
      intro s' d' i' j h
      rw [TranslationProofs.eo_to_smt_term_dt_cons] at h
      by_cases hRes : TranslationProofs.__eo_reserved_datatype_name s <;>
        simp [native_ite, hRes] at h
  | app x hPrev ih =>
      intro s d i j h
      cases hPrev with
      | tuple =>
          change
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x) =
              SmtTerm.DtSel s d i j at h
          cases h
      | tupleUnit =>
          have hNotOne :
              ∀ z, Term.UOp UserOp.tuple_unit ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              CtorSpineRoot.tupleUnit x hNotOne
          rw [hTo] at h
          cases h
      | dtCons s0 d0 i0 =>
          have hNotOne :
              ∀ z, Term.DtCons s0 d0 i0 ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              (CtorSpineRoot.dtCons s0 d0 i0) x hNotOne
          rw [hTo] at h
          cases h
      | app y hPrev' =>
          cases hPrev' with
          | tuple =>
              exact
                TranslationProofs.eo_to_smt_tuple_ne_dt_sel x y s d i j h
          | tupleUnit =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.UOp UserOp.tuple_unit) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y CtorSpineRoot.tupleUnit) x hNotOne
              rw [hTo] at h
              cases h
          | dtCons s0 d0 i0 =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.DtCons s0 d0 i0) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y (CtorSpineRoot.dtCons s0 d0 i0))
                  x hNotOne
              rw [hTo] at h
              cases h
          | app z hPrev'' =>
              have hCurSp := CtorSpineRoot.app y (CtorSpineRoot.app z hPrev'')
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  hCurSp x (by intro w hw; cases hw)
              rw [hTo] at h
              cases h

private theorem ctorSpineRoot_to_smt_ne_dt_tester
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i := by
  induction hSp with
  | tuple =>
      intro s d i h
      cases h
  | tupleUnit =>
      intro s d i h
      rw [TranslationProofs.eo_to_smt_term_tuple_unit] at h
      cases h
  | dtCons s d i =>
      intro s' d' i' h
      rw [TranslationProofs.eo_to_smt_term_dt_cons] at h
      by_cases hRes : TranslationProofs.__eo_reserved_datatype_name s <;>
        simp [native_ite, hRes] at h
  | app x hPrev ih =>
      intro s d i h
      cases hPrev with
      | tuple =>
          change
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x) =
              SmtTerm.DtTester s d i at h
          cases h
      | tupleUnit =>
          have hNotOne :
              ∀ z, Term.UOp UserOp.tuple_unit ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              CtorSpineRoot.tupleUnit x hNotOne
          rw [hTo] at h
          cases h
      | dtCons s0 d0 i0 =>
          have hNotOne :
              ∀ z, Term.DtCons s0 d0 i0 ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              (CtorSpineRoot.dtCons s0 d0 i0) x hNotOne
          rw [hTo] at h
          cases h
      | app y hPrev' =>
          cases hPrev' with
          | tuple =>
              exact
                TranslationProofs.eo_to_smt_tuple_ne_dt_tester x y s d i h
          | tupleUnit =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.UOp UserOp.tuple_unit) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y CtorSpineRoot.tupleUnit) x hNotOne
              rw [hTo] at h
              cases h
          | dtCons s0 d0 i0 =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.DtCons s0 d0 i0) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y (CtorSpineRoot.dtCons s0 d0 i0))
                  x hNotOne
              rw [hTo] at h
              cases h
          | app z hPrev'' =>
              have hCurSp := CtorSpineRoot.app y (CtorSpineRoot.app z hPrev'')
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  hCurSp x (by intro w hw; cases hw)
              rw [hTo] at h
              cases h

private theorem ctorSpineEq_left_root
    {t s root : Term} :
    CtorSpineEq t s root -> CtorSpineRoot t root := by
  intro h
  induction h with
  | tuple => exact CtorSpineRoot.tuple
  | tupleUnit => exact CtorSpineRoot.tupleUnit
  | dtCons s d i => exact CtorSpineRoot.dtCons s d i
  | app x y h ih => exact CtorSpineRoot.app x ih

private theorem ctorSpineEq_right_root
    {t s root : Term} :
    CtorSpineEq t s root -> CtorSpineRoot s root := by
  intro h
  induction h with
  | tuple => exact CtorSpineRoot.tuple
  | tupleUnit => exact CtorSpineRoot.tupleUnit
  | dtCons s d i => exact CtorSpineRoot.dtCons s d i
  | app x y h ih => exact CtorSpineRoot.app y ih

private theorem dtConsSpineRoot_of_ctor_dtCons_aux
    {t root : Term} :
    CtorSpineRoot t root ->
      ∀ {s : native_String} {d : DatatypeDecl} {i : native_Nat},
        root = Term.DtCons s d i -> DtConsSpineRoot t s d i := by
  intro h
  induction h with
  | tuple =>
      intro s d i hEq
      cases hEq
  | tupleUnit =>
      intro s d i hEq
      cases hEq
  | dtCons s' d' i' =>
      intro s d i hEq
      cases hEq
      exact DtConsSpineRoot.root s' d' i'
  | app x h ih =>
      intro s d i hEq
      exact DtConsSpineRoot.app x (ih hEq)

private theorem dtConsSpineRoot_of_ctor_dtCons
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat} :
    CtorSpineRoot t (Term.DtCons s d i) ->
      DtConsSpineRoot t s d i := by
  intro h
  exact dtConsSpineRoot_of_ctor_dtCons_aux h rfl

private theorem dtConsSpineRoot_left_of_ctorSpineEq
    {t u : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (h : CtorSpineEq t u (Term.DtCons s d i)) :
    DtConsSpineRoot t s d i :=
  dtConsSpineRoot_of_ctor_dtCons (ctorSpineEq_left_root h)

private theorem dtConsSpineRoot_right_of_ctorSpineEq
    {t u : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (h : CtorSpineEq t u (Term.DtCons s d i)) :
    DtConsSpineRoot u s d i :=
  dtConsSpineRoot_of_ctor_dtCons (ctorSpineEq_right_root h)

private theorem eo_to_smt_dtCons_eq
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) := by
  rfl

private theorem dtConsSpineRoot_to_smt_ne_dt_sel
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    ∀ s' d' i' j, __eo_to_smt t ≠ SmtTerm.DtSel s' d' i' j := by
  induction hSp with
  | root s d i =>
      intro s' d' i' j
      rw [eo_to_smt_dtCons_eq]
      by_cases hRes : __eo_to_smt_reserved_datatype_name s <;>
        simp [native_ite, hRes]
  | app x hSp ih =>
      intro s' d' i' j hEq
      rw [dtConsSpineRoot_apply_generic hSp x] at hEq
      cases hEq

private theorem dtConsSpineRoot_to_smt_ne_dt_tester
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    ∀ s' d' i', __eo_to_smt t ≠ SmtTerm.DtTester s' d' i' := by
  induction hSp with
  | root s d i =>
      intro s' d' i'
      rw [eo_to_smt_dtCons_eq]
      by_cases hRes : __eo_to_smt_reserved_datatype_name s <;>
        simp [native_ite, hRes]
  | app x hSp ih =>
      intro s' d' i' hEq
      rw [dtConsSpineRoot_apply_generic hSp x] at hEq
      cases hEq

private theorem smt_model_eval_not_notvalue_of_non_none
    (M : SmtModel) (hM : model_wf M) (x : SmtTerm)
    (hNN : __smtx_typeof x ≠ SmtType.None) :
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    exact hNN
  have hPres :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM x hxNN
  intro hNot
  apply hNN
  rw [← hPres, hNot]
  simp [__smtx_typeof_value]

private theorem dtConsSpineRoot_eval_head_of_type
    (M : SmtModel) (hM : model_wf M)
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    ∃ s' d' i',
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.DtCons s' d' i' := by
  induction hSp with
  | root s d i =>
      rw [eo_to_smt_dtCons_eq] at hNN
      by_cases hRes : __eo_to_smt_reserved_datatype_name s
      · exfalso
        apply hNN
        simp [native_ite, hRes]
      · refine ⟨s, __eo_to_smt_datatype_decl d, i, ?_⟩
        rw [eo_to_smt_dtCons_eq]
        simp [native_ite, hRes]
        simp [__smtx_model_eval, __smtx_apply_head_value]
  | app x hSp ih =>
      rename_i t0 s0 d0 i0
      have hTo := dtConsSpineRoot_apply_generic hSp x
      have hGen : generic_apply_type (__eo_to_smt t0) (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
          (dtConsSpineRoot_to_smt_ne_dt_tester hSp)
      have hApplyNN := by
        have hNN' := hNN
        rw [hTo] at hNN'
        unfold generic_apply_type at hGen
        rw [hGen] at hNN'
        exact hNN'
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hHead, hX, hANN, _hBNN⟩
      have hHeadNN : __smtx_typeof (__eo_to_smt t0) ≠ SmtType.None := by
        rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
      rcases ih hHeadNN with ⟨s', d', i', hEvalHead⟩
      have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hX]
        exact hANN
      have hxNot :=
        smt_model_eval_not_notvalue_of_non_none M hM (__eo_to_smt x) hXNN
      refine ⟨s', d', i', ?_⟩
      rw [hTo]
      rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops M
        _ _
        (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
        (dtConsSpineRoot_to_smt_ne_dt_tester hSp)]
      rw [smtx_model_eval_apply_of_dt_chain M
        _ _
        ⟨s', d', i', hEvalHead⟩ hxNot]
      simp [__smtx_apply_head_value, hEvalHead]

private theorem dtConsSpineRoot_apply_eval_eq_apply
    (M : SmtModel) (hM : model_wf M)
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) (x : Term)
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply t x)) ≠ SmtType.None) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply t x)) =
      SmtValue.Apply (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt x)) := by
  have hTo := dtConsSpineRoot_apply_generic hSp x
  have hGen : generic_apply_type (__eo_to_smt t) (__eo_to_smt x) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hSp)
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt t))
          (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTo] using hNN
    unfold generic_apply_type at hGen
    rw [hGen] at hNN'
    exact hNN'
  rcases typeof_apply_non_none_cases hApplyNN with
    ⟨A, B, hHead, hX, hANN, _hBNN⟩
  have hHeadNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hEvalHead :=
    dtConsSpineRoot_eval_head_of_type M hM hSp hHeadNN
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hANN
  have hxNot :=
    smt_model_eval_not_notvalue_of_non_none M hM (__eo_to_smt x) hXNN
  rw [hTo]
  rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops M
    (__eo_to_smt t) (__eo_to_smt x)
    (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
    (dtConsSpineRoot_to_smt_ne_dt_tester hSp)]
  exact smtx_model_eval_apply_of_dt_chain M
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M (__eo_to_smt x))
    hEvalHead hxNot

private theorem smt_type_ne_fun_self
    (A B : SmtType) :
    B ≠ SmtType.FunType A B := by
  intro h
  have hSize := congrArg sizeOf h
  simp at hSize

private theorem smt_type_ne_dtc_app_self
    (A B : SmtType) :
    B ≠ SmtType.DtcAppType A B := by
  intro h
  have hSize := congrArg sizeOf h
  simp at hSize

private theorem smt_apply_head_type_ne_result
    {F X : SmtTerm}
    (hGen : generic_apply_type F X)
    (hNN : __smtx_typeof (SmtTerm.Apply F X) ≠ SmtType.None) :
    __smtx_typeof F ≠ __smtx_typeof (SmtTerm.Apply F X) := by
  intro hEq
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X) ≠
        SmtType.None := by
    rw [← hGen]
    exact hNN
  rcases typeof_apply_non_none_cases hApplyNN with
    ⟨A, B, hHead, hX, hA, _hB⟩
  have hApplyTy :
      __smtx_typeof (SmtTerm.Apply F X) = B := by
    rw [hGen]
    rcases hHead with hHead | hHead
    · rw [hHead, hX]
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq, hA]
    · rw [hHead, hX]
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq, hA]
  have hFB : __smtx_typeof F = B :=
    hEq.trans hApplyTy
  rcases hHead with hHead | hHead
  · exact smt_type_ne_fun_self A B (hFB.symm.trans hHead)
  · exact smt_type_ne_dtc_app_self A B (hFB.symm.trans hHead)

private theorem smt_type_ne_reglan_of_apply_head_cases
    {F A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) :
    F ≠ SmtType.RegLan := by
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem ctorSpineEq_dtCons_type_eq_of_non_none_aux
    {f g root : Term}
    (hSp : CtorSpineEq f g root) :
    ∀ {s : native_String} {d : DatatypeDecl} {i : native_Nat},
      root = Term.DtCons s d i ->
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt g) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __smtx_typeof (__eo_to_smt g) := by
  induction hSp with
  | tuple =>
      intro s d i hRoot _hFNN _hGNN
      cases hRoot
  | tupleUnit =>
      intro s d i hRoot _hFNN _hGNN
      cases hRoot
  | dtCons s d i =>
      intro s' d' i' hRoot _hFNN _hGNN
      cases hRoot
      rfl
  | app x y hSp ih =>
      intro s d i hRoot hFNN hGNN
      rename_i f0 g0 root
      have hSpDt : CtorSpineEq f0 g0 (Term.DtCons s d i) := by
        simpa [hRoot] using hSp
      have hFSp := dtConsSpineRoot_left_of_ctorSpineEq hSpDt
      have hGSp := dtConsSpineRoot_right_of_ctorSpineEq hSpDt
      have hToF := dtConsSpineRoot_apply_generic hFSp x
      have hToG := dtConsSpineRoot_apply_generic hGSp y
      have hGenF : generic_apply_type (__eo_to_smt f0) (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hFSp)
          (dtConsSpineRoot_to_smt_ne_dt_tester hFSp)
      have hGenG : generic_apply_type (__eo_to_smt g0) (__eo_to_smt y) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hGSp)
          (dtConsSpineRoot_to_smt_ne_dt_tester hGSp)
      have hApplyFNN :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f0))
              (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
        have hFNN' :
            __smtx_typeof (SmtTerm.Apply (__eo_to_smt f0) (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [hToF] using hFNN
        unfold generic_apply_type at hGenF
        rw [hGenF] at hFNN'
        exact hFNN'
      have hApplyGNN :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g0))
              (__smtx_typeof (__eo_to_smt y)) ≠ SmtType.None := by
        have hGNN' :
            __smtx_typeof (SmtTerm.Apply (__eo_to_smt g0) (__eo_to_smt y)) ≠
              SmtType.None := by
          simpa [hToG] using hGNN
        unfold generic_apply_type at hGenG
        rw [hGenG] at hGNN'
        exact hGNN'
      rcases typeof_apply_non_none_cases hApplyFNN with
        ⟨AF, BF, hHeadF, _hXF, _hAFNN, _hBFNN⟩
      rcases typeof_apply_non_none_cases hApplyGNN with
        ⟨AG, BG, hHeadG, _hXG, _hAGNN, _hBGNN⟩
      have hF0NN : __smtx_typeof (__eo_to_smt f0) ≠ SmtType.None := by
        rcases hHeadF with hHeadF | hHeadF <;> rw [hHeadF] <;> simp
      have hG0NN : __smtx_typeof (__eo_to_smt g0) ≠ SmtType.None := by
        rcases hHeadG with hHeadG | hHeadG <;> rw [hHeadG] <;> simp
      have hHeadEq :
          __smtx_typeof (__eo_to_smt f0) =
            __smtx_typeof (__eo_to_smt g0) :=
        ih hRoot hF0NN hG0NN
      have hApplyGNN' :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f0))
              (__smtx_typeof (__eo_to_smt y)) ≠ SmtType.None := by
        simpa [hHeadEq] using hApplyGNN
      have hApplyEq :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f0))
              (__smtx_typeof (__eo_to_smt x)) =
            __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f0))
              (__smtx_typeof (__eo_to_smt y)) :=
        typeof_apply_eq_of_same_head_non_none hApplyFNN hApplyGNN'
      rw [hToF, hToG]
      unfold generic_apply_type at hGenF hGenG
      rw [hGenF, hGenG]
      simpa [hHeadEq] using hApplyEq

private theorem ctorSpineEq_dtCons_type_eq_of_non_none
    {f g : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : CtorSpineEq f g (Term.DtCons s d i))
    (hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None)
    (hGNN : __smtx_typeof (__eo_to_smt g) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt f) = __smtx_typeof (__eo_to_smt g) :=
  ctorSpineEq_dtCons_type_eq_of_non_none_aux hSp rfl hFNN hGNN

private theorem dtCons_ctor_spine_eq_apply_bool_components
    {f g : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (a b : Term)
    (hSp : CtorSpineEq f g (Term.DtCons s d i))
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply f a)) (Term.Apply g b))) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq f) g) ∧
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply f a) (Term.Apply g b) hBool with
    ⟨hTyEq, hLeftNN⟩
  have hFSp := dtConsSpineRoot_left_of_ctorSpineEq hSp
  have hGSp := dtConsSpineRoot_right_of_ctorSpineEq hSp
  have hToF := dtConsSpineRoot_apply_generic hFSp a
  have hToG := dtConsSpineRoot_apply_generic hGSp b
  have hGenF : generic_apply_type (__eo_to_smt f) (__eo_to_smt a) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hFSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hFSp)
  have hGenG : generic_apply_type (__eo_to_smt g) (__eo_to_smt b) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hGSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hGSp)
  have hTyEqApply :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt b)) := by
    have hTyEq' := hTyEq
    rw [hToF, hToG] at hTyEq'
    unfold generic_apply_type at hGenF hGenG
    rw [hGenF, hGenG] at hTyEq'
    exact hTyEq'
  have hLeftApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) ≠
          SmtType.None := by
      simpa [hToF] using hLeftNN
    unfold generic_apply_type at hGenF
    rw [hGenF] at hNN'
    exact hNN'
  have hRightApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt b)) ≠ SmtType.None := by
    rw [← hTyEqApply]
    exact hLeftApplyNN
  rcases typeof_apply_non_none_cases hLeftApplyNN with
    ⟨A, _B, hHeadF, hATy, hANN, _hBNN⟩
  rcases typeof_apply_non_none_cases hRightApplyNN with
    ⟨A', _B', hHeadG, _hBTy, _hA'NN, _hB'NN⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hHeadF with hHeadF | hHeadF <;> rw [hHeadF] <;> simp
  have hGNN : __smtx_typeof (__eo_to_smt g) ≠ SmtType.None := by
    rcases hHeadG with hHeadG | hHeadG <;> rw [hHeadG] <;> simp
  have hFnTyEq :
      __smtx_typeof (__eo_to_smt f) =
        __smtx_typeof (__eo_to_smt g) :=
    ctorSpineEq_dtCons_type_eq_of_non_none hSp hFNN hGNN
  have hLeftApplyGHeadNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
    simpa [hFnTyEq] using hLeftApplyNN
  have hSameHeadEq :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt b)) := by
    simpa [hFnTyEq] using hTyEqApply
  have hArgTyEq :
      __smtx_typeof (__eo_to_smt a) =
        __smtx_typeof (__eo_to_smt b) :=
    typeof_apply_same_head_arg_type_eq hSameHeadEq hLeftApplyGHeadNN
  have hArgNN : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
    rw [hATy]
    exact hANN
  constructor
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type f g hFnTyEq hFNN
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b hArgTyEq hArgNN

private theorem dtCons_ctor_spine_eq_apply_eval_eq_and
    (M : SmtModel) (hM : model_wf M)
    {f g : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (a b : Term)
    (hSp : CtorSpineEq f g (Term.DtCons s d i))
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply f a)) (Term.Apply g b))) :
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      __smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt f))
          (__smtx_model_eval M (__eo_to_smt g)))
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b))) := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply f a) (Term.Apply g b) hBool with
    ⟨hTyEq, hLeftNN⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (Term.Apply g b)) ≠ SmtType.None := by
    rw [← hTyEq]
    exact hLeftNN
  have hFSp := dtConsSpineRoot_left_of_ctorSpineEq hSp
  have hGSp := dtConsSpineRoot_right_of_ctorSpineEq hSp
  have hToF := dtConsSpineRoot_apply_generic hFSp a
  have hGenF : generic_apply_type (__eo_to_smt f) (__eo_to_smt a) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hFSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hFSp)
  have hApplyFNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) ≠
          SmtType.None := by
      simpa [hToF] using hLeftNN
    unfold generic_apply_type at hGenF
    rw [hGenF] at hNN'
    exact hNN'
  rcases typeof_apply_non_none_cases hApplyFNN with
    ⟨A, _B, hHeadF, hATy, hANN, _hBNN⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hHeadF with hHeadF | hHeadF <;> rw [hHeadF] <;> simp
  have hGNN : __smtx_typeof (__eo_to_smt g) ≠ SmtType.None := by
    have hFnTyEqTmp :=
      ctorSpineEq_dtCons_type_eq_of_non_none hSp hFNN
        (by
          have hGSpApply := dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightNN
          rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
              (Term.Apply f a) (Term.Apply g b) hBool with
            ⟨_hTyEq', hLeftNN'⟩
          have hGNN' :
              __smtx_typeof (__eo_to_smt g) ≠ SmtType.None := by
            have hToG := dtConsSpineRoot_apply_generic hGSp b
            have hGenG : generic_apply_type (__eo_to_smt g) (__eo_to_smt b) :=
              generic_apply_type_of_non_datatype_head
                (dtConsSpineRoot_to_smt_ne_dt_sel hGSp)
                (dtConsSpineRoot_to_smt_ne_dt_tester hGSp)
            have hRightNNApply :
                __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
                    (__smtx_typeof (__eo_to_smt b)) ≠ SmtType.None := by
              have hNN'' :
                  __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt b)) ≠
                    SmtType.None := by
                simpa [hToG] using hRightNN
              unfold generic_apply_type at hGenG
              rw [hGenG] at hNN''
              exact hNN''
            rcases typeof_apply_non_none_cases hRightNNApply with
              ⟨AG, BG, hHeadG, _hBTy, _hAGNN, _hBGNN⟩
            rcases hHeadG with hHeadG | hHeadG <;> rw [hHeadG] <;> simp
          exact hGNN')
    exact by
      have hComps := dtCons_ctor_spine_eq_apply_bool_components a b hSp hBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type f g hComps.1 with
        ⟨hFnTyEq, hFNN'⟩
      rw [← hFnTyEq]
      exact hFNN'
  have hComps := dtCons_ctor_spine_eq_apply_bool_components a b hSp hBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type f g hComps.1 with
    ⟨hFnTyEq, hFNNFromEq⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hComps.2 with
    ⟨hArgTyEq, _hArgNN⟩
  have hFTypeNeReg :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_apply_head_cases hHeadF
  have hFTermNN : term_has_non_none_type (__eo_to_smt f) := by
    unfold term_has_non_none_type
    exact hFNN
  have hAReg : A ≠ SmtType.RegLan :=
    Smtm.smt_term_fun_like_arg_ne_reglan_of_non_none
      (__eo_to_smt f) hFTermNN hHeadF
  have hArgBTy : __smtx_typeof (__eo_to_smt b) = A :=
    hArgTyEq.symm.trans hATy
  have hFPair :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt f) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt g) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt f) (__eo_to_smt g)
      (__smtx_typeof (__eo_to_smt f)) rfl hFnTyEq.symm
      hFNNFromEq hFTypeNeReg
  have hArgPair :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt a) (__eo_to_smt b) A hATy hArgBTy hANN hAReg
  have hLeftEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hFSp a hLeftNN
  have hRightEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightNN
  rw [hLeftEval, hRightEval]
  exact smtx_model_eval_eq_apply_eq_and
    (__smtx_model_eval M (__eo_to_smt f))
    (__smtx_model_eval M (__eo_to_smt g))
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b))
    hFPair hArgPair

private theorem dtCons_ctor_spine_eq_apply_eval_eq_false_of_component
    (M : SmtModel) (hM : model_wf M)
    {f g : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (a b : Term)
    (hSp : CtorSpineEq f g (Term.DtCons s d i))
    (hLeftTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a))
    (hRightTrans : RuleProofs.eo_has_smt_translation (Term.Apply g b)) :
    (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g)) = SmtValue.Boolean false ∨
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hComponent
  have hLeftNN :
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) ≠ SmtType.None :=
    hLeftTrans
  have hRightNN :
      __smtx_typeof (__eo_to_smt (Term.Apply g b)) ≠ SmtType.None :=
    hRightTrans
  have hFSp := dtConsSpineRoot_left_of_ctorSpineEq hSp
  have hGSp := dtConsSpineRoot_right_of_ctorSpineEq hSp
  have hToF := dtConsSpineRoot_apply_generic hFSp a
  have hToG := dtConsSpineRoot_apply_generic hGSp b
  have hGenF : generic_apply_type (__eo_to_smt f) (__eo_to_smt a) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hFSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hFSp)
  have hGenG : generic_apply_type (__eo_to_smt g) (__eo_to_smt b) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hGSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hGSp)
  have hApplyFNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) ≠
          SmtType.None := by
      simpa [hToF] using hLeftNN
    unfold generic_apply_type at hGenF
    rw [hGenF] at hNN'
    exact hNN'
  have hApplyGNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt g))
          (__smtx_typeof (__eo_to_smt b)) ≠ SmtType.None := by
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt b)) ≠
          SmtType.None := by
      simpa [hToG] using hRightNN
    unfold generic_apply_type at hGenG
    rw [hGenG] at hNN'
    exact hNN'
  rcases typeof_apply_non_none_cases hApplyFNN with
    ⟨A, _B, hHeadF, hATy, hANN, _hBNN⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hHeadF with hHeadF | hHeadF <;> rw [hHeadF] <;> simp
  have hGNN : __smtx_typeof (__eo_to_smt g) ≠ SmtType.None := by
    rcases typeof_apply_non_none_cases hApplyGNN with
      ⟨AG, BG, hHeadG, _hBTy, _hAGNN, _hBGNN⟩
    rcases hHeadG with hHeadG | hHeadG <;> rw [hHeadG] <;> simp
  have hFnTyEq :
      __smtx_typeof (__eo_to_smt f) =
        __smtx_typeof (__eo_to_smt g) :=
    ctorSpineEq_dtCons_type_eq_of_non_none hSp hFNN hGNN
  have hApplyGAsF :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt b)) ≠ SmtType.None := by
    simpa [hFnTyEq] using hApplyGNN
  have hSameHeadApplyEq :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt b)) :=
    typeof_apply_eq_of_same_head_non_none hApplyFNN hApplyGAsF
  have hArgTyEq :
      __smtx_typeof (__eo_to_smt a) =
        __smtx_typeof (__eo_to_smt b) :=
    typeof_apply_same_head_arg_type_eq hSameHeadApplyEq hApplyFNN
  have hFTypeNeReg :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_apply_head_cases hHeadF
  have hFTermNN : term_has_non_none_type (__eo_to_smt f) := by
    unfold term_has_non_none_type
    exact hFNN
  have hAReg : A ≠ SmtType.RegLan :=
    Smtm.smt_term_fun_like_arg_ne_reglan_of_non_none
      (__eo_to_smt f) hFTermNN hHeadF
  have hArgBTy : __smtx_typeof (__eo_to_smt b) = A :=
    hArgTyEq.symm.trans hATy
  have hFPair :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt f) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt g) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt f) (__eo_to_smt g)
      (__smtx_typeof (__eo_to_smt f)) rfl hFnTyEq.symm
      hFNN hFTypeNeReg
  have hArgPair :
      ¬ ∃ r1 r2,
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan r1 ∧
          __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan r2 :=
    smt_model_eval_pair_not_reglan_of_non_reg_type M hM
      (__eo_to_smt a) (__eo_to_smt b) A hATy hArgBTy hANN hAReg
  have hLeftEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hFSp a hLeftNN
  have hRightEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightNN
  rw [hLeftEval, hRightEval]
  rw [smtx_model_eval_eq_apply_eq_and
    (__smtx_model_eval M (__eo_to_smt f))
    (__smtx_model_eval M (__eo_to_smt g))
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b))
    hFPair hArgPair]
  rcases hComponent with hHeadFalse | hArgFalse
  · rcases model_eval_eq_is_boolean
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) with
      ⟨ba, hArgBool⟩
    rw [hHeadFalse, hArgBool]
    simp [__smtx_model_eval_and, SmtEval.native_and]
  · rcases model_eval_eq_is_boolean
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g)) with
      ⟨bf, hHeadBool⟩
    rw [hArgFalse, hHeadBool]
    cases bf <;> simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem smtx_typeof_apply_tuple_prepend_eq_none
    (head tail arg : SmtTerm) (headTy : SmtType) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tuple_prepend head headTy tail) arg) =
      SmtType.None := by
  have hGen :
      generic_apply_type (__eo_to_smt_tuple_prepend head headTy tail) arg :=
    generic_apply_type_of_non_datatype_head
      (TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_sel head headTy tail)
      (TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_tester head headTy tail)
  by_cases hNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
        SmtType.None
  · rcases CongSupport.tuple_prepend_tail_type_of_non_none
      head headTy tail hNN with ⟨c, hTailTy⟩
    have hTy :=
      TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
        tail head headTy c hTailTy hNN
    unfold generic_apply_type at hGen
    rw [hGen, hTy]
    simp [__smtx_typeof_apply]
  · have hNone :
        __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
          SmtType.None := by
      cases hTy : __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) <;>
        simp [hTy] at hNN ⊢
    unfold generic_apply_type at hGen
    rw [hGen, hNone]
    simp [__smtx_typeof_apply]

theorem tuple_full_apply_type_none
    (head tail arg : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail)
            arg)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt_tuple_prepend (__eo_to_smt head)
            (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail))
          (__eo_to_smt arg)) =
      SmtType.None
  exact smtx_typeof_apply_tuple_prepend_eq_none
    (__eo_to_smt head) (__eo_to_smt tail) (__eo_to_smt arg)
    (__smtx_typeof (__eo_to_smt head))

private theorem ctorSpineRoot_tuple_apply_type_none_or_one_arg_aux
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ {a : Term}, root = Term.UOp UserOp.tuple ->
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None ∨
        ∃ x, f = Term.Apply (Term.UOp UserOp.tuple) x := by
  induction hSp with
  | tuple =>
      intro a _hRoot
      left
      change
        __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
      exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt a)
  | tupleUnit =>
      intro a hRoot
      cases hRoot
  | dtCons s d i =>
      intro a hRoot
      cases hRoot
  | app x hSp ih =>
      intro a hRoot
      cases hSp with
      | tuple =>
          right
          exact ⟨x, rfl⟩
      | tupleUnit =>
          cases hRoot
      | dtCons s d i =>
          cases hRoot
      | app x' hSp' =>
          left
          have hPrev := ih (a := x) hRoot
          rcases hPrev with hNone | hOne
          · have hCurSp := CtorSpineRoot.app x (CtorSpineRoot.app x' hSp')
            have hTo :=
              ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                hCurSp a (by intro z hz; cases hz)
            have hGen :=
              generic_apply_type_of_non_datatype_head
                (x := __eo_to_smt a)
                (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
                (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
            rw [hTo]
            unfold generic_apply_type at hGen
            rw [hGen, hNone]
            simp [__smtx_typeof_apply]
          · rcases hOne with ⟨z, hz⟩
            cases hz
            have hCurSp :=
              CtorSpineRoot.app x (CtorSpineRoot.app x' CtorSpineRoot.tuple)
            have hTo :=
              ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                hCurSp a (by intro w hw; cases hw)
            rw [hTo]
            change
              __smtx_typeof
                  (SmtTerm.Apply
                    (__eo_to_smt_tuple_prepend (__eo_to_smt x')
                      (__smtx_typeof (__eo_to_smt x')) (__eo_to_smt x))
                    (__eo_to_smt a)) = SmtType.None
            exact smtx_typeof_apply_tuple_prepend_eq_none
              (__eo_to_smt x') (__eo_to_smt x) (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt x'))

private theorem ctorSpineRoot_tuple_apply_type_none_or_one_arg
    {f a : Term}
    (hSp : CtorSpineRoot f (Term.UOp UserOp.tuple)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None ∨
      ∃ x, f = Term.Apply (Term.UOp UserOp.tuple) x :=
  ctorSpineRoot_tuple_apply_type_none_or_one_arg_aux hSp rfl

private theorem ctorSpineRoot_tupleUnit_apply_type_none_aux
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ {a : Term}, root = Term.UOp UserOp.tuple_unit ->
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None := by
  induction hSp with
  | tuple =>
      intro a hRoot
      cases hRoot
  | tupleUnit =>
      intro a _hRoot
      change
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.DtCons (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl
                  (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
                native_nat_zero)
              (__eo_to_smt a)) =
          SmtType.None
      have hGeneric :
          generic_apply_type
            (SmtTerm.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
              native_nat_zero)
            (__eo_to_smt a) :=
        generic_apply_type_of_non_datatype_head
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      unfold generic_apply_type at hGeneric
      rw [hGeneric]
      simp [__eo_to_smt_tuple_decl,
        TranslationProofs.smtx_typeof_tuple_unit_translation]
      rfl
  | dtCons s d i =>
      intro a hRoot
      cases hRoot
  | app x hSp ih =>
      intro a hRoot
      cases hSp with
      | tuple =>
          cases hRoot
      | tupleUnit =>
          have hPrev := ih (a := x) hRoot
          have hCurSp := CtorSpineRoot.app x CtorSpineRoot.tupleUnit
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              hCurSp a (by intro z hz; cases hz)
          have hGen :=
            generic_apply_type_of_non_datatype_head
              (x := __eo_to_smt a)
              (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
              (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
          rw [hTo]
          unfold generic_apply_type at hGen
          rw [hGen, hPrev]
          simp [__smtx_typeof_apply]
      | dtCons s d i =>
          cases hRoot
      | app x' hSp' =>
          have hPrev := ih (a := x) hRoot
          have hCurSp := CtorSpineRoot.app x (CtorSpineRoot.app x' hSp')
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              hCurSp a (by intro z hz; cases hz)
          have hGen :=
            generic_apply_type_of_non_datatype_head
              (x := __eo_to_smt a)
              (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
              (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
          rw [hTo]
          unfold generic_apply_type at hGen
          rw [hGen, hPrev]
          simp [__smtx_typeof_apply]

private theorem ctorSpineRoot_tupleUnit_apply_type_none
    {f a : Term}
    (hSp : CtorSpineRoot f (Term.UOp UserOp.tuple_unit)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None :=
  ctorSpineRoot_tupleUnit_apply_type_none_aux hSp rfl

private theorem ctorSpineRoot_root_cases
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    root = Term.UOp UserOp.tuple ∨
      root = Term.UOp UserOp.tuple_unit ∨
        ∃ s d i, root = Term.DtCons s d i := by
  induction hSp with
  | tuple =>
      exact Or.inl rfl
  | tupleUnit =>
      exact Or.inr (Or.inl rfl)
  | dtCons s d i =>
      exact Or.inr (Or.inr ⟨s, d, i, rfl⟩)
  | app x hSp ih =>
      exact ih

private def dtConsDistinctBaseGuard (c : Term) : Term :=
  __eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
    (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
      (__eo_is_ok (__eo_dt_selectors c)))

private theorem dtConsDistinct_base_guard_root
    (c : Term) :
    dtConsDistinctBaseGuard c = Term.Boolean true ->
    CtorSpineRoot c c := by
  intro h
  cases c <;>
    simp [dtConsDistinctBaseGuard, __eo_is_eq, __eo_ite, __eo_is_ok,
      __eo_dt_selectors, __eo_dt_selectors_main, native_ite, native_teq,
      native_and, native_not, SmtEval.native_and, SmtEval.native_not] at h
  case UOp op =>
    cases op <;> simp at h
    · exact CtorSpineRoot.tupleUnit
    · exact CtorSpineRoot.tuple
  case DtCons s d i =>
    exact CtorSpineRoot.dtCons s d i

private theorem dtConsDistinct_base_info {c d : Term} :
    __eo_requires
        (__eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d))
        (Term.Boolean true) (__eo_not (__eo_eq c d)) =
      Term.Boolean true ->
    dtConsDistinctBaseGuard c = Term.Boolean true ∧
      dtConsDistinctBaseGuard d = Term.Boolean true := by
  intro h
  have hReqNe :
      __eo_requires
          (__eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d))
          (Term.Boolean true) (__eo_not (__eo_eq c d)) ≠
        Term.Stuck := by
    rw [h]
    intro hBad
    cases hBad
  have hGuardAnd :
      __eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReqNe
  exact eo_and_true hGuardAnd

private theorem eo_not_eq_false_eq_true {x : Term} :
    __eo_not x = Term.Boolean false -> x = Term.Boolean true := by
  intro h
  cases x <;> simp [__eo_not] at h
  case Boolean b =>
    cases b <;> simp [SmtEval.native_not] at h ⊢

private theorem dtConsDistinct_base_info_false {c d : Term} :
    __eo_requires
        (__eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d))
        (Term.Boolean true) (__eo_not (__eo_eq c d)) =
      Term.Boolean false ->
    dtConsDistinctBaseGuard c = Term.Boolean true ∧
      dtConsDistinctBaseGuard d = Term.Boolean true ∧ c = d := by
  intro h
  have hReqNe :
      __eo_requires
          (__eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d))
          (Term.Boolean true) (__eo_not (__eo_eq c d)) ≠
        Term.Stuck := by
    rw [h]
    intro hBad
    cases hBad
  have hGuardAnd :
      __eo_and (dtConsDistinctBaseGuard c) (dtConsDistinctBaseGuard d) =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReqNe
  have hResult :
      __eo_not (__eo_eq c d) = Term.Boolean false := by
    have hReqResult := eo_requires_result_eq_of_ne_stuck hReqNe
    simpa [h] using hReqResult.symm
  rcases eo_and_true hGuardAnd with ⟨hc, hd⟩
  have hEqTrue : __eo_eq c d = Term.Boolean true :=
    eo_not_eq_false_eq_true hResult
  exact ⟨hc, hd, (eo_eq_eq_of_true hEqTrue).symm⟩

private theorem eo_ite_true_eq_false
    {c e : Term} :
    __eo_ite c (Term.Boolean true) e = Term.Boolean false ->
    c = Term.Boolean false ∧ e = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b <;> simp at h
    exact ⟨rfl, h⟩

private theorem eo_ite_eq_true_cases (c t e : Term) :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

private theorem dt_distinct_terms_false_same_root
    (t s : Term) :
    __dt_distinct_terms t s = Term.Boolean false ->
    ∃ root, CtorSpineRoot t root ∧ CtorSpineRoot s root := by
  intro hDistinct
  by_cases htApply : ∃ f x, t = Term.Apply f x
  · rcases htApply with ⟨f, x, rfl⟩
    by_cases hsApply : ∃ g y, s = Term.Apply g y
    · rcases hsApply with ⟨g, y, rfl⟩
      rw [__dt_distinct_terms.eq_def] at hDistinct
      change
        __eo_ite (__dt_distinct_terms f g) (Term.Boolean true)
          (__eo_ite (__eo_eq x y) (Term.Boolean false)
            (__are_distinct_terms_type x y (__eo_typeof x))) =
          Term.Boolean false at hDistinct
      rcases eo_ite_true_eq_false hDistinct with ⟨hHead, _hTail⟩
      rcases dt_distinct_terms_false_same_root f g hHead with
        ⟨root, hf, hg⟩
      exact ⟨root, CtorSpineRoot.app x hf, CtorSpineRoot.app y hg⟩
    · have hsNotApply : ∀ g y, s ≠ Term.Apply g y := by
        intro g y h
        exact hsApply ⟨g, y, h⟩
      have hHead : __dt_distinct_terms f s = Term.Boolean false := by
        cases s <;> try (simp [__dt_distinct_terms] at hDistinct ⊢; exact hDistinct)
        case Stuck =>
          simp [__dt_distinct_terms] at hDistinct
        case Apply g y =>
          exact False.elim (hsNotApply g y rfl)
      rcases dt_distinct_terms_false_same_root f s hHead with
        ⟨root, hf, hs⟩
      exact ⟨root, CtorSpineRoot.app x hf, hs⟩
  · have htNotApply : ∀ f x, t ≠ Term.Apply f x := by
      intro f x h
      exact htApply ⟨f, x, h⟩
    by_cases hsApply : ∃ g y, s = Term.Apply g y
    · rcases hsApply with ⟨g, y, rfl⟩
      have hHead : __dt_distinct_terms t g = Term.Boolean false := by
        cases t <;> try simpa only [__dt_distinct_terms] using hDistinct
        case Apply f x =>
          exact False.elim (htNotApply f x rfl)
      rcases dt_distinct_terms_false_same_root t g hHead with
        ⟨root, ht, hg⟩
      exact ⟨root, ht, CtorSpineRoot.app y hg⟩
    · have hsNotApply : ∀ g y, s ≠ Term.Apply g y := by
        intro g y h
        exact hsApply ⟨g, y, h⟩
      have hBase :
          __eo_requires
              (__eo_and (dtConsDistinctBaseGuard t)
                (dtConsDistinctBaseGuard s))
              (Term.Boolean true) (__eo_not (__eo_eq t s)) =
            Term.Boolean false := by
        cases t <;> cases s <;>
          try
            (first
              | exact False.elim (htNotApply _ _ rfl)
              | exact False.elim (hsNotApply _ _ rfl))
        all_goals
          simp [__dt_distinct_terms] at hDistinct
          try exact hDistinct
      rcases dtConsDistinct_base_info_false hBase with
        ⟨htGuard, _hsGuard, hEq⟩
      subst s
      exact ⟨t, dtConsDistinct_base_guard_root t htGuard,
        dtConsDistinct_base_guard_root t htGuard⟩
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

theorem dt_distinct_terms_distinct_left_ne_false
    (g : Term) :
    __dt_distinct_terms (Term.UOp UserOp.distinct) g ≠
      Term.Boolean false := by
  intro hDistinct
  rcases dt_distinct_terms_false_same_root
      (Term.UOp UserOp.distinct) g hDistinct with
    ⟨root, hRoot, _⟩
  cases hRoot

theorem dt_distinct_terms_distinct_right_ne_false
    (f : Term) :
    __dt_distinct_terms f (Term.UOp UserOp.distinct) ≠
      Term.Boolean false := by
  intro hDistinct
  rcases dt_distinct_terms_false_same_root
      f (Term.UOp UserOp.distinct) hDistinct with
    ⟨root, _, hRoot⟩
  cases hRoot

private theorem dt_distinct_terms_roots_of_nonapply_pair
    {t c : Term} :
    (∀ f x, t ≠ Term.Apply f x) ->
    (∀ f x, c ≠ Term.Apply f x) ->
    __dt_distinct_terms t c = Term.Boolean true ->
    ∃ rt rc, CtorSpineRoot t rt ∧ CtorSpineRoot c rc := by
  intro htNotApply hcNotApply hDistinct
  have hBase :
      __eo_requires
          (__eo_and (dtConsDistinctBaseGuard t) (dtConsDistinctBaseGuard c))
          (Term.Boolean true) (__eo_not (__eo_eq t c)) =
        Term.Boolean true := by
    cases t <;> cases c <;>
      try
        (first
          | exact False.elim (htNotApply _ _ rfl)
          | exact False.elim (hcNotApply _ _ rfl))
    all_goals
      simp [__dt_distinct_terms] at hDistinct
      try exact hDistinct
  rcases dtConsDistinct_base_info hBase with ⟨htGuard, hcGuard⟩
  exact ⟨t, c, dtConsDistinct_base_guard_root t htGuard,
    dtConsDistinct_base_guard_root c hcGuard⟩

private theorem dt_distinct_terms_roots_of_right_nonapply
    {t c : Term} :
    (∀ f x, c ≠ Term.Apply f x) ->
    __dt_distinct_terms t c = Term.Boolean true ->
    ∃ rt rc, CtorSpineRoot t rt ∧ CtorSpineRoot c rc := by
  intro hcNotApply hDistinct
  by_cases htApply : ∃ f x, t = Term.Apply f x
  · rcases htApply with ⟨f, a, rfl⟩
    have hHead : __dt_distinct_terms f c = Term.Boolean true := by
      cases c <;> try (simp [__dt_distinct_terms] at hDistinct ⊢; exact hDistinct)
      case Stuck =>
        simp [__dt_distinct_terms] at hDistinct
      case Apply g y =>
        exact False.elim (hcNotApply g y rfl)
    rcases dt_distinct_terms_roots_of_right_nonapply
        hcNotApply hHead with ⟨rt, rc, ht, hc⟩
    exact ⟨rt, rc, CtorSpineRoot.app a ht, hc⟩
  · have htNotApply : ∀ f x, t ≠ Term.Apply f x := by
      intro f x h
      exact htApply ⟨f, x, h⟩
    exact dt_distinct_terms_roots_of_nonapply_pair
      htNotApply hcNotApply hDistinct
termination_by sizeOf t
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem tuplePrependValueRec_seed_is_apply
    (tailD : SmtDatatype) (tailVal : SmtValue) (k : Nat)
    (seedF seedA : SmtValue) :
    ∃ v x,
      tuplePrependValueRec tailD tailVal k (SmtValue.Apply seedF seedA) =
        SmtValue.Apply v x := by
  cases k with
  | zero =>
      exact ⟨seedF, seedA, rfl⟩
  | succ k =>
      exact ⟨tuplePrependValueRec tailD tailVal k
          (SmtValue.Apply seedF seedA),
        __smtx_apply_arg_nth_value tailVal k
          (__smtx_dt_num_sels tailD native_nat_zero),
        by simp [tuplePrependValueRec]⟩

private theorem tuple_apply_model_eval_is_apply
    (M : SmtModel) (hM : model_wf M) (a as : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as) ->
    ∃ v x,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) as)) =
        SmtValue.Apply v x := by
  intro hTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt a)
          (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) ≠
      SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      as a hTrans with
    ⟨c, hTailTy⟩
  have hEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt a) (__eo_to_smt as)
    (__smtx_typeof (__eo_to_smt a)) c rfl hTailTy hTrans
  dsimp at hEval
  change
    ∃ v x,
      __smtx_model_eval M
          (__eo_to_smt_tuple_prepend (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt as)) =
        SmtValue.Apply v x
  rw [hEval]
  exact tuplePrependValueRec_seed_is_apply
    (SmtDatatype.sum c SmtDatatype.null)
    (__smtx_model_eval M (__eo_to_smt as))
    (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)
    (SmtValue.DtCons (native_string_lit "@Tuple")
      (__eo_to_smt_tuple_decl
        (SmtDatatype.sum
          (SmtDatatypeCons.cons (__smtx_typeof (__eo_to_smt a)) c)
          SmtDatatype.null)) native_nat_zero)
    (__smtx_model_eval M (__eo_to_smt a))

private theorem ctorSpineRoot_nonapply_eval_ne_apply
    (M : SmtModel) {c root : Term}
    (hSp : CtorSpineRoot c root)
    (hcNotApply : ∀ f x, c ≠ Term.Apply f x)
    (hTrans : RuleProofs.eo_has_smt_translation c) :
    ∀ v x,
      __smtx_model_eval M (__eo_to_smt c) ≠ SmtValue.Apply v x := by
  intro v x
  cases hSp with
  | tuple =>
      exact False.elim (hTrans TranslationProofs.smtx_typeof_none)
  | tupleUnit =>
      rw [TranslationProofs.eo_to_smt_term_tuple_unit]
      simp [__smtx_model_eval]
  | dtCons s d i =>
      rw [eo_to_smt_dtCons_eq]
      by_cases hRes : __eo_to_smt_reserved_datatype_name s
      · exact False.elim (hTrans (by simp [native_ite, hRes]))
      · simp [native_ite, hRes, __smtx_model_eval]
  | app y hPrev =>
      exact False.elim (hcNotApply _ _ rfl)

private theorem ctorSpineRoot_apply_eval_is_apply
    (M : SmtModel) (hM : model_wf M)
    {f a root : Term}
    (hSp : CtorSpineRoot (Term.Apply f a) root)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a)) :
    ∃ v x,
      __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
        SmtValue.Apply v x := by
  cases hSp with
  | app y hPrev =>
      rcases ctorSpineRoot_root_cases hPrev with
        hTuple | hRest
      · have hPrevTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
          simpa [hTuple] using hPrev
        rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hPrevTuple with
          hNone | hOne
        · exact False.elim (hTrans hNone)
        · rcases hOne with ⟨head, hF⟩
          subst f
          exact tuple_apply_model_eval_is_apply M hM head a hTrans
      · rcases hRest with hUnit | hDt
        · have hPrevUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
            simpa [hUnit] using hPrev
          exact False.elim
            (hTrans (ctorSpineRoot_tupleUnit_apply_type_none hPrevUnit))
        · rcases hDt with ⟨s, d, i, hRoot⟩
          have hPrevDt : CtorSpineRoot f (Term.DtCons s d i) := by
            simpa [hRoot] using hPrev
          have hDtSp : DtConsSpineRoot f s d i :=
            dtConsSpineRoot_of_ctor_dtCons hPrevDt
          have hEval :=
            dtConsSpineRoot_apply_eval_eq_apply M hM hDtSp a hTrans
          rw [hEval]
          exact ⟨__smtx_model_eval M (__eo_to_smt f),
            __smtx_model_eval M (__eo_to_smt a), rfl⟩

theorem dt_distinct_terms_apply_left_nonapply_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M)
    (f a c : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation c ->
    (∀ g y, c ≠ Term.Apply g y) ->
    __dt_distinct_terms (Term.Apply f a) c = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt c)) =
      SmtValue.Boolean false := by
  intro hAppTrans hcTrans hcNotApply hDistinct
  rcases dt_distinct_terms_roots_of_right_nonapply
      hcNotApply hDistinct with
    ⟨rApp, rC, hAppRoot, hCRoot⟩
  rcases ctorSpineRoot_apply_eval_is_apply M hM hAppRoot hAppTrans with
    ⟨vf, vx, hEvalApp⟩
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      rw [hEvalApp] at hEq
      exact ctorSpineRoot_nonapply_eval_ne_apply
        M hCRoot hcNotApply hcTrans vf vx hEq.symm)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      rw [hEvalApp] at h₁
      cases h₁)

private theorem dt_distinct_terms_roots_of_left_nonapply
    {c t : Term} :
    (∀ f x, c ≠ Term.Apply f x) ->
    __dt_distinct_terms c t = Term.Boolean true ->
    ∃ rc rt, CtorSpineRoot c rc ∧ CtorSpineRoot t rt := by
  intro hcNotApply hDistinct
  by_cases htApply : ∃ f x, t = Term.Apply f x
  · rcases htApply with ⟨f, a, rfl⟩
    have hHead : __dt_distinct_terms c f = Term.Boolean true := by
      cases c <;> try simpa only [__dt_distinct_terms] using hDistinct
      case Apply g y =>
        exact False.elim (hcNotApply g y rfl)
    rcases dt_distinct_terms_roots_of_left_nonapply
        hcNotApply hHead with ⟨rc, rt, hc, ht⟩
    exact ⟨rc, rt, hc, CtorSpineRoot.app a ht⟩
  · have htNotApply : ∀ f x, t ≠ Term.Apply f x := by
      intro f x h
      exact htApply ⟨f, x, h⟩
    exact dt_distinct_terms_roots_of_nonapply_pair
      hcNotApply htNotApply hDistinct
termination_by sizeOf t
decreasing_by
  all_goals subst_vars; simp_wf; omega

theorem dt_distinct_terms_apply_right_nonapply_model_eval_eq_false
    (M : SmtModel) (hM : model_wf M)
    (c g b : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    (∀ f x, c ≠ Term.Apply f x) ->
    __dt_distinct_terms c (Term.Apply g b) = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hcTrans hAppTrans hcNotApply hDistinct
  rcases dt_distinct_terms_roots_of_left_nonapply
      hcNotApply hDistinct with
    ⟨rC, rApp, hCRoot, hAppRoot⟩
  rcases ctorSpineRoot_apply_eval_is_apply M hM hAppRoot hAppTrans with
    ⟨vg, vb, hEvalApp⟩
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      rw [hEvalApp] at hEq
      exact ctorSpineRoot_nonapply_eval_ne_apply
        M hCRoot hcNotApply hcTrans vg vb hEq)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, h₂⟩
      rw [hEvalApp] at h₂
      cases h₂)

private theorem dt_distinct_terms_true_roots
    (t s : Term) :
    __dt_distinct_terms t s = Term.Boolean true ->
    ∃ rt rs, CtorSpineRoot t rt ∧ CtorSpineRoot s rs := by
  intro hDistinct
  by_cases htApply : ∃ f x, t = Term.Apply f x
  · rcases htApply with ⟨f, x, rfl⟩
    by_cases hsApply : ∃ g y, s = Term.Apply g y
    · rcases hsApply with ⟨g, y, rfl⟩
      rw [__dt_distinct_terms.eq_def] at hDistinct
      change
        __eo_ite (__dt_distinct_terms f g) (Term.Boolean true)
          (__eo_ite (__eo_eq x y) (Term.Boolean false)
            (__are_distinct_terms_type x y (__eo_typeof x))) =
          Term.Boolean true at hDistinct
      rcases eo_ite_eq_true_cases
          (__dt_distinct_terms f g) (Term.Boolean true)
          (__eo_ite (__eo_eq x y) (Term.Boolean false)
            (__are_distinct_terms_type x y (__eo_typeof x)))
          hDistinct with hHead | hTail
      · rcases dt_distinct_terms_true_roots f g hHead.1 with
          ⟨rt, rs, hf, hg⟩
        exact ⟨rt, rs, CtorSpineRoot.app x hf,
          CtorSpineRoot.app y hg⟩
      · rcases dt_distinct_terms_false_same_root f g hTail.1 with
          ⟨root, hf, hg⟩
        exact ⟨root, root, CtorSpineRoot.app x hf,
          CtorSpineRoot.app y hg⟩
    · have hsNotApply : ∀ g y, s ≠ Term.Apply g y := by
        intro g y h
        exact hsApply ⟨g, y, h⟩
      exact dt_distinct_terms_roots_of_right_nonapply
        hsNotApply hDistinct
  · have htNotApply : ∀ f x, t ≠ Term.Apply f x := by
      intro f x h
      exact htApply ⟨f, x, h⟩
    by_cases hsApply : ∃ g y, s = Term.Apply g y
    · rcases hsApply with ⟨g, y, rfl⟩
      exact dt_distinct_terms_roots_of_left_nonapply
        htNotApply hDistinct
    · have hsNotApply : ∀ g y, s ≠ Term.Apply g y := by
        intro g y h
        exact hsApply ⟨g, y, h⟩
      exact dt_distinct_terms_roots_of_nonapply_pair
        htNotApply hsNotApply hDistinct
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem smt_eval_eq_false_implies_ne
    {v w : SmtValue} :
    __smtx_model_eval_eq v w = SmtValue.Boolean false ->
    v ≠ w := by
  intro hEq hSame
  subst w
  have hRefl : __smtx_model_eval_eq v v = SmtValue.Boolean true :=
    RuleProofs.smtx_model_eval_eq_refl v
  rw [hRefl] at hEq
  cases hEq

private theorem dtConsSpineRoot_head_translation_of_apply_translation
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) (x : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply t x) ->
    RuleProofs.eo_has_smt_translation t := by
  intro hTrans
  have hTo := dtConsSpineRoot_apply_generic hSp x
  have hGen : generic_apply_type (__eo_to_smt t) (__eo_to_smt x) :=
    generic_apply_type_of_non_datatype_head
      (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
      (dtConsSpineRoot_to_smt_ne_dt_tester hSp)
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt t))
          (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
    have hTransNN :
        __smtx_typeof (__eo_to_smt (Term.Apply t x)) ≠ SmtType.None :=
      hTrans
    have hNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTo] using hTransNN
    unfold generic_apply_type at hGen
    rw [hGen] at hNN'
    exact hNN'
  rcases typeof_apply_non_none_cases hApplyNN with
    ⟨A, B, hHead, _hX, _hANN, _hBNN⟩
  unfold RuleProofs.eo_has_smt_translation
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem dtConsSpineRoot_reserved_false_of_translation
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_to_smt_reserved_datatype_name s = false := by
  induction hSp with
  | root s d i =>
      intro hTrans
      unfold RuleProofs.eo_has_smt_translation at hTrans
      rw [eo_to_smt_dtCons_eq] at hTrans
      by_cases hRes : __eo_to_smt_reserved_datatype_name s
      · exfalso
        apply hTrans
        simp [native_ite, hRes]
      · simpa using hRes
  | app x hSp ih =>
      intro hTrans
      exact ih
        (dtConsSpineRoot_head_translation_of_apply_translation
          hSp x hTrans)

private theorem dtConsSpineRoot_eval_head_name_of_type
    (M : SmtModel) (hM : model_wf M)
    {t : Term} {s : native_String} {d : DatatypeDecl} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    ∃ d' i',
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.DtCons s d' i' := by
  induction hSp with
  | root s d i =>
      rw [eo_to_smt_dtCons_eq] at hNN
      by_cases hRes : __eo_to_smt_reserved_datatype_name s
      · exfalso
        apply hNN
        simp [native_ite, hRes]
      · refine ⟨__eo_to_smt_datatype_decl d, i, ?_⟩
        rw [eo_to_smt_dtCons_eq]
        simp [native_ite, hRes]
        simp [__smtx_model_eval, __smtx_apply_head_value]
  | app x hSp ih =>
      rename_i t0 s0 d0 i0
      have hTo := dtConsSpineRoot_apply_generic hSp x
      have hGen : generic_apply_type (__eo_to_smt t0) (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
          (dtConsSpineRoot_to_smt_ne_dt_tester hSp)
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt t0))
              (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
        have hNN' := hNN
        rw [hTo] at hNN'
        unfold generic_apply_type at hGen
        rw [hGen] at hNN'
        exact hNN'
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hHead, hX, hANN, _hBNN⟩
      have hHeadNN : __smtx_typeof (__eo_to_smt t0) ≠ SmtType.None := by
        rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
      rcases ih hHeadNN with ⟨d', i', hEvalHead⟩
      have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hX]
        exact hANN
      have hxNot :=
        smt_model_eval_not_notvalue_of_non_none M hM (__eo_to_smt x) hXNN
      refine ⟨d', i', ?_⟩
      rw [hTo]
      rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops M
        _ _
        (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
        (dtConsSpineRoot_to_smt_ne_dt_tester hSp)]
      rw [smtx_model_eval_apply_of_dt_chain M
        _ _
        ⟨s0, d', i', hEvalHead⟩ hxNot]
      simp [__smtx_apply_head_value, hEvalHead]

theorem dt_distinct_terms_true_nontranslated_left_apply_head_is_tuple
    (f g a : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    __dt_distinct_terms f g = Term.Boolean true ->
    ¬ RuleProofs.eo_has_smt_translation f ->
    ∃ x, f = Term.Apply (Term.UOp UserOp.tuple) x := by
  intro hApplyTrans hDistinct hNoTrans
  rcases dt_distinct_terms_true_roots f g hDistinct with
    ⟨rF, _rG, hFRoot, _hGRoot⟩
  rcases ctorSpineRoot_root_cases hFRoot with hFRootTuple | hFRest
  · have hFRootTuple' : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
      simpa [hFRootTuple] using hFRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRootTuple' with
      hNone | hOne
    · exact False.elim (hApplyTrans hNone)
    · exact hOne
  rcases hFRest with hFRootUnit | hFRootDt
  · have hFRootUnit' : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
      simpa [hFRootUnit] using hFRoot
    exact False.elim
      (hApplyTrans (ctorSpineRoot_tupleUnit_apply_type_none hFRootUnit'))
  rcases hFRootDt with ⟨s, d, i, hFRootDt⟩
  have hFRootDt' : CtorSpineRoot f (Term.DtCons s d i) := by
    simpa [hFRootDt] using hFRoot
  have hFSp : DtConsSpineRoot f s d i :=
    dtConsSpineRoot_of_ctor_dtCons hFRootDt'
  exact False.elim
    (hNoTrans
      (dtConsSpineRoot_head_translation_of_apply_translation hFSp a
        hApplyTrans))

theorem dt_distinct_terms_true_nontranslated_right_apply_head_is_tuple
    (f g b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    __dt_distinct_terms f g = Term.Boolean true ->
    ¬ RuleProofs.eo_has_smt_translation g ->
    ∃ y, g = Term.Apply (Term.UOp UserOp.tuple) y := by
  intro hApplyTrans hDistinct hNoTrans
  rcases dt_distinct_terms_true_roots f g hDistinct with
    ⟨_rF, rG, _hFRoot, hGRoot⟩
  rcases ctorSpineRoot_root_cases hGRoot with hGRootTuple | hGRest
  · have hGRootTuple' : CtorSpineRoot g (Term.UOp UserOp.tuple) := by
      simpa [hGRootTuple] using hGRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRootTuple' with
      hNone | hOne
    · exact False.elim (hApplyTrans hNone)
    · exact hOne
  rcases hGRest with hGRootUnit | hGRootDt
  · have hGRootUnit' : CtorSpineRoot g (Term.UOp UserOp.tuple_unit) := by
      simpa [hGRootUnit] using hGRoot
    exact False.elim
      (hApplyTrans (ctorSpineRoot_tupleUnit_apply_type_none hGRootUnit'))
  rcases hGRootDt with ⟨s, d, i, hGRootDt⟩
  have hGRootDt' : CtorSpineRoot g (Term.DtCons s d i) := by
    simpa [hGRootDt] using hGRoot
  have hGSp : DtConsSpineRoot g s d i :=
    dtConsSpineRoot_of_ctor_dtCons hGRootDt'
  exact False.elim
    (hNoTrans
      (dtConsSpineRoot_head_translation_of_apply_translation hGSp b
        hApplyTrans))

theorem dt_distinct_terms_apply_apply_model_eval_eq_false_of_head_component
    (M : SmtModel) (hM : model_wf M)
    (f g a b : Term) :
    RuleProofs.eo_has_smt_translation f ->
    RuleProofs.eo_has_smt_translation g ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    __dt_distinct_terms f g = Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g)) = SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hFTrans hGTrans hLeftTrans hRightTrans hDistinct hHeadFalse
  rcases dt_distinct_terms_true_roots f g hDistinct with
    ⟨rF, rG, hFRoot, hGRoot⟩
  rcases ctorSpineRoot_root_cases hFRoot with hFRootTuple | hFRest
  · have hFRootTuple' : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
      simpa [hFRootTuple] using hFRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRootTuple' with
      hNone | hOne
    · exact False.elim (hLeftTrans hNone)
    · rcases hOne with ⟨x, hFx⟩
      subst f
      exact False.elim
        (hFTrans
          (by
            change
              __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                SmtType.None
            exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt x)))
  rcases hFRest with hFRootUnit | hFRootDt
  · have hFRootUnit' : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
      simpa [hFRootUnit] using hFRoot
    exact False.elim
      (hLeftTrans (ctorSpineRoot_tupleUnit_apply_type_none hFRootUnit'))
  rcases hFRootDt with ⟨sF, dF, iF, hFRootDt⟩
  have hFRootDt' : CtorSpineRoot f (Term.DtCons sF dF iF) := by
    simpa [hFRootDt] using hFRoot
  rcases ctorSpineRoot_root_cases hGRoot with hGRootTuple | hGRest
  · have hGRootTuple' : CtorSpineRoot g (Term.UOp UserOp.tuple) := by
      simpa [hGRootTuple] using hGRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRootTuple' with
      hNone | hOne
    · exact False.elim (hRightTrans hNone)
    · rcases hOne with ⟨y, hGy⟩
      subst g
      exact False.elim
        (hGTrans
          (by
            change
              __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) =
                SmtType.None
            exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt y)))
  rcases hGRest with hGRootUnit | hGRootDt
  · have hGRootUnit' : CtorSpineRoot g (Term.UOp UserOp.tuple_unit) := by
      simpa [hGRootUnit] using hGRoot
    exact False.elim
      (hRightTrans (ctorSpineRoot_tupleUnit_apply_type_none hGRootUnit'))
  rcases hGRootDt with ⟨sG, dG, iG, hGRootDt⟩
  have hGRootDt' : CtorSpineRoot g (Term.DtCons sG dG iG) := by
    simpa [hGRootDt] using hGRoot
  have hFSp : DtConsSpineRoot f sF dF iF :=
    dtConsSpineRoot_of_ctor_dtCons hFRootDt'
  have hGSp : DtConsSpineRoot g sG dG iG :=
    dtConsSpineRoot_of_ctor_dtCons hGRootDt'
  have hLeftEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hFSp a hLeftTrans
  have hRightEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightTrans
  have hHeadNe :
      __smtx_model_eval M (__eo_to_smt f) ≠
        __smtx_model_eval M (__eo_to_smt g) :=
    smt_eval_eq_false_implies_ne hHeadFalse
  rw [hLeftEval, hRightEval]
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      injection hEq with hHeadEq _hArgEq
      exact hHeadNe hHeadEq)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      cases h₁)

theorem dt_distinct_terms_apply_apply_model_eval_eq_false_of_right_tuple_head
    (M : SmtModel) (hM : model_wf M)
    (f a y b : Term) :
    RuleProofs.eo_has_smt_translation f ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) b) ->
    __dt_distinct_terms f (Term.Apply (Term.UOp UserOp.tuple) y) =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) b))) =
      SmtValue.Boolean false := by
  intro hFTrans hLeftTrans hRightTrans hDistinct
  rcases dt_distinct_terms_true_roots f
      (Term.Apply (Term.UOp UserOp.tuple) y) hDistinct with
    ⟨rF, _rG, hFRoot, _hGRoot⟩
  rcases ctorSpineRoot_root_cases hFRoot with hFRootTuple | hFRest
  · have hFRootTuple' : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
      simpa [hFRootTuple] using hFRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRootTuple' with
      hNone | hOne
    · exact False.elim (hLeftTrans hNone)
    · rcases hOne with ⟨x, hFx⟩
      subst f
      exact False.elim
        (hFTrans
          (by
            change
              __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
                SmtType.None
            exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt x)))
  rcases hFRest with hFRootUnit | hFRootDt
  · have hFRootUnit' : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
      simpa [hFRootUnit] using hFRoot
    exact False.elim
      (hLeftTrans (ctorSpineRoot_tupleUnit_apply_type_none hFRootUnit'))
  rcases hFRootDt with ⟨sF, dF, iF, hFRootDt⟩
  have hFRootDt' : CtorSpineRoot f (Term.DtCons sF dF iF) := by
    simpa [hFRootDt] using hFRoot
  have hFSp : DtConsSpineRoot f sF dF iF :=
    dtConsSpineRoot_of_ctor_dtCons hFRootDt'
  have hLeftEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hFSp a hLeftTrans
  have hRightNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) b)) ≠
        SmtType.None :=
    hRightTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt y)
          (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt b)) ≠
      SmtType.None at hRightNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      b y hRightNN with
    ⟨c, hTailTy⟩
  have hRightEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt y) (__eo_to_smt b)
    (__smtx_typeof (__eo_to_smt y)) c rfl hTailTy hRightNN
  dsimp at hRightEval
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None :=
    hFTrans
  rcases dtConsSpineRoot_eval_head_name_of_type M hM hFSp hFNN with
    ⟨dHead, iHead, hFHead⟩
  have hReservedFalse :
      __eo_to_smt_reserved_datatype_name sF = false :=
    dtConsSpineRoot_reserved_false_of_translation hFSp hFTrans
  have hTupleReserved :
      __eo_to_smt_reserved_datatype_name (native_string_lit "@Tuple") = true := by
    native_decide
  rw [hLeftEval]
  change
    __smtx_model_eval_eq
        (SmtValue.Apply (__smtx_model_eval M (__eo_to_smt f))
          (__smtx_model_eval M (__eo_to_smt a)))
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt b))) =
      SmtValue.Boolean false
  rw [hRightEval]
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      have hHeads := congrArg __smtx_apply_head_value hEq
      rw [tuplePrependValueRec_head] at hHeads
      simp [__smtx_apply_head_value, hFHead] at hHeads
      rcases hHeads with ⟨hName, _hD, _hI⟩
      rw [hName, hTupleReserved] at hReservedFalse
      cases hReservedFalse)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      cases h₁)

theorem dt_distinct_terms_apply_apply_model_eval_eq_false_of_left_tuple_head
    (M : SmtModel) (hM : model_wf M)
    (x a g b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) a) ->
    RuleProofs.eo_has_smt_translation g ->
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    __dt_distinct_terms (Term.Apply (Term.UOp UserOp.tuple) x) g =
      Term.Boolean true ->
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hGTrans hRightTrans hDistinct
  rcases dt_distinct_terms_true_roots
      (Term.Apply (Term.UOp UserOp.tuple) x) g hDistinct with
    ⟨_rF, rG, _hFRoot, hGRoot⟩
  rcases ctorSpineRoot_root_cases hGRoot with hGRootTuple | hGRest
  · have hGRootTuple' : CtorSpineRoot g (Term.UOp UserOp.tuple) := by
      simpa [hGRootTuple] using hGRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRootTuple' with
      hNone | hOne
    · exact False.elim (hRightTrans hNone)
    · rcases hOne with ⟨y, hGy⟩
      subst g
      exact False.elim
        (hGTrans
          (by
            change
              __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) =
                SmtType.None
            exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt y)))
  rcases hGRest with hGRootUnit | hGRootDt
  · have hGRootUnit' : CtorSpineRoot g (Term.UOp UserOp.tuple_unit) := by
      simpa [hGRootUnit] using hGRoot
    exact False.elim
      (hRightTrans (ctorSpineRoot_tupleUnit_apply_type_none hGRootUnit'))
  rcases hGRootDt with ⟨sG, dG, iG, hGRootDt⟩
  have hGRootDt' : CtorSpineRoot g (Term.DtCons sG dG iG) := by
    simpa [hGRootDt] using hGRoot
  have hGSp : DtConsSpineRoot g sG dG iG :=
    dtConsSpineRoot_of_ctor_dtCons hGRootDt'
  have hRightEval :=
    dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightTrans
  have hLeftNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) a)) ≠
        SmtType.None :=
    hLeftTrans
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt x)
          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt a)) ≠
      SmtType.None at hLeftNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      a x hLeftNN with
    ⟨c, hTailTy⟩
  have hLeftEval := tuple_prepend_eval_eq_value_rec M hM
    (__eo_to_smt x) (__eo_to_smt a)
    (__smtx_typeof (__eo_to_smt x)) c rfl hTailTy hLeftNN
  dsimp at hLeftEval
  have hGNN : __smtx_typeof (__eo_to_smt g) ≠ SmtType.None :=
    hGTrans
  rcases dtConsSpineRoot_eval_head_name_of_type M hM hGSp hGNN with
    ⟨dHead, iHead, hGHead⟩
  have hReservedFalse :
      __eo_to_smt_reserved_datatype_name sG = false :=
    dtConsSpineRoot_reserved_false_of_translation hGSp hGTrans
  have hTupleReserved :
      __eo_to_smt_reserved_datatype_name (native_string_lit "@Tuple") = true := by
    native_decide
  rw [hRightEval]
  change
    __smtx_model_eval_eq
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt a)))
        (SmtValue.Apply (__smtx_model_eval M (__eo_to_smt g))
          (__smtx_model_eval M (__eo_to_smt b))) =
      SmtValue.Boolean false
  rw [hLeftEval]
  exact smtx_model_eval_eq_false_of_ne_not_reglan
    (by
      intro hEq
      have hHeads := congrArg __smtx_apply_head_value hEq
      rw [tuplePrependValueRec_head] at hHeads
      simp [__smtx_apply_head_value, hGHead] at hHeads
      rcases hHeads with ⟨hName, _hD, _hI⟩
      rw [← hName, hTupleReserved] at hReservedFalse
      cases hReservedFalse)
    (by
      intro hReg
      rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
      have hHead := congrArg __smtx_apply_head_value h₁
      rw [tuplePrependValueRec_head] at hHead
      simp [__smtx_apply_head_value] at hHead)

theorem dt_distinct_terms_apply_apply_model_eval_eq_false_of_arg_component
    (M : SmtModel) (hM : model_wf M)
    (f g a b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    (∀ x y,
      f = Term.Apply (Term.UOp UserOp.tuple) x ->
      g = Term.Apply (Term.UOp UserOp.tuple) y -> False) ->
    __dt_distinct_terms f g = Term.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hLeftTrans hRightTrans hNotTuple hHeadFalse hArgFalse
  rcases dt_distinct_terms_false_same_root f g hHeadFalse with
    ⟨root, hFRoot, hGRoot⟩
  rcases ctorSpineRoot_root_cases hFRoot with hRootTuple | hRest
  · have hFRootTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
      simpa [hRootTuple] using hFRoot
    have hGRootTuple : CtorSpineRoot g (Term.UOp UserOp.tuple) := by
      simpa [hRootTuple] using hGRoot
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRootTuple with
      hFNone | hFOne
    · exact False.elim (hLeftTrans hFNone)
    rcases hFOne with ⟨x, hFx⟩
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRootTuple with
      hGNone | hGOne
    · exact False.elim (hRightTrans hGNone)
    rcases hGOne with ⟨y, hGy⟩
    exact False.elim (hNotTuple x y hFx hGy)
  · rcases hRest with hRootUnit | hRootDt
    · have hFRootUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
        simpa [hRootUnit] using hFRoot
      exact False.elim
        (hLeftTrans (ctorSpineRoot_tupleUnit_apply_type_none hFRootUnit))
    · rcases hRootDt with ⟨s, d, i, hRootDt⟩
      have hFRootDt : CtorSpineRoot f (Term.DtCons s d i) := by
        simpa [hRootDt] using hFRoot
      have hGRootDt : CtorSpineRoot g (Term.DtCons s d i) := by
        simpa [hRootDt] using hGRoot
      have hFSp : DtConsSpineRoot f s d i :=
        dtConsSpineRoot_of_ctor_dtCons hFRootDt
      have hGSp : DtConsSpineRoot g s d i :=
        dtConsSpineRoot_of_ctor_dtCons hGRootDt
      have hLeftEval :=
        dtConsSpineRoot_apply_eval_eq_apply M hM hFSp a hLeftTrans
      have hRightEval :=
        dtConsSpineRoot_apply_eval_eq_apply M hM hGSp b hRightTrans
      have hArgNe :
          __smtx_model_eval M (__eo_to_smt a) ≠
            __smtx_model_eval M (__eo_to_smt b) :=
        smt_eval_eq_false_implies_ne hArgFalse
      rw [hLeftEval, hRightEval]
      exact smtx_model_eval_eq_false_of_ne_not_reglan
        (by
          intro hEq
          injection hEq with _ hArgEq
          exact hArgNe hArgEq)
        (by
          intro hReg
          rcases hReg with ⟨r₁, r₂, h₁, _h₂⟩
          cases h₁)

private theorem ctorSpineEq_tuple_apply_bool_false
    {f g a b : Term}
    (hSp : CtorSpineEq f g (Term.UOp UserOp.tuple))
    (hNotTuple : ∀ (a b : Term),
      f = Term.Apply (Term.UOp UserOp.tuple) a ->
      g = Term.Apply (Term.UOp UserOp.tuple) b -> False)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply f a)) (Term.Apply g b))) :
    False := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply f a) (Term.Apply g b) hBool with
    ⟨hTyEq, hLeftNN⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (Term.Apply g b)) ≠ SmtType.None := by
    rw [← hTyEq]
    exact hLeftNN
  have hFRoot := ctorSpineEq_left_root hSp
  have hGRoot := ctorSpineEq_right_root hSp
  rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRoot with
    hFNone | hFOne
  · exact hLeftNN hFNone
  · rcases hFOne with ⟨x, hFx⟩
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRoot with
      hGNone | hGOne
    · exact hRightNN hGNone
    · rcases hGOne with ⟨y, hGy⟩
      exact hNotTuple x y hFx hGy

private theorem ctorSpineEq_tupleUnit_apply_bool_false
    {f g a b : Term}
    (hSp : CtorSpineEq f g (Term.UOp UserOp.tuple_unit))
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply f a)) (Term.Apply g b))) :
    False := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply f a) (Term.Apply g b) hBool with
    ⟨_hTyEq, hLeftNN⟩
  exact hLeftNN
    (ctorSpineRoot_tupleUnit_apply_type_none (ctorSpineEq_left_root hSp))

private theorem ctorSpineEq_tuple_apply_translation_false
    {f g a b : Term}
    (hSp : CtorSpineEq f g (Term.UOp UserOp.tuple))
    (hNotTuple : ∀ (a b : Term),
      f = Term.Apply (Term.UOp UserOp.tuple) a ->
      g = Term.Apply (Term.UOp UserOp.tuple) b -> False)
    (hLeftTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a))
    (hRightTrans : RuleProofs.eo_has_smt_translation (Term.Apply g b)) :
    False := by
  have hLeftNN :
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) ≠ SmtType.None :=
    hLeftTrans
  have hRightNN :
      __smtx_typeof (__eo_to_smt (Term.Apply g b)) ≠ SmtType.None :=
    hRightTrans
  have hFRoot := ctorSpineEq_left_root hSp
  have hGRoot := ctorSpineEq_right_root hSp
  rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hFRoot with
    hFNone | hFOne
  · exact hLeftNN hFNone
  · rcases hFOne with ⟨x, hFx⟩
    rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hGRoot with
      hGNone | hGOne
    · exact hRightNN hGNone
    · rcases hGOne with ⟨y, hGy⟩
      exact hNotTuple x y hFx hGy

private theorem ctorSpineEq_tupleUnit_apply_translation_false
    {f g a b : Term}
    (hSp : CtorSpineEq f g (Term.UOp UserOp.tuple_unit))
    (hLeftTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a)) :
    False := by
  exact hLeftTrans
    (ctorSpineRoot_tupleUnit_apply_type_none (ctorSpineEq_left_root hSp))

private theorem ctorSpineEq_root_cases
    {f g root : Term}
    (hSp : CtorSpineEq f g root) :
    root = Term.UOp UserOp.tuple ∨
      root = Term.UOp UserOp.tuple_unit ∨
        ∃ s d i, root = Term.DtCons s d i := by
  induction hSp with
  | tuple =>
      exact Or.inl rfl
  | tupleUnit =>
      exact Or.inr (Or.inl rfl)
  | dtCons s d i =>
      exact Or.inr (Or.inr ⟨s, d, i, rfl⟩)
  | app x y hSp ih =>
      exact ih

private theorem ctorSpineRoot_of_is_cons_app_true
    (t : Term) :
    __is_cons_app t = Term.Boolean true ->
    ∃ root, CtorSpineRoot t root := by
  cases t with
  | UOp op =>
      intro h
      cases op <;>
        simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
          __eo_dt_selectors_main, native_teq, native_ite, native_not,
          SmtEval.native_not, SmtEval.native_and] at h ⊢
      all_goals
        first
        | exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple⟩
        | exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineRoot.tupleUnit⟩
        | contradiction
  | Apply f a =>
      intro h
      rcases ctorSpineRoot_of_is_cons_app_true f
          (by simpa [__is_cons_app] using h) with
        ⟨root, hRoot⟩
      exact ⟨root, CtorSpineRoot.app a hRoot⟩
  | DtCons s d i =>
      intro _h
      exact ⟨Term.DtCons s d i, CtorSpineRoot.dtCons s d i⟩
  | Stuck =>
      intro h
      simp [__is_cons_app] at h
  | UOp1 op t =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp2 op t u =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp3 op t u v =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_nil =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_cons =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Bool =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Boolean b =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Numeral n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Rational q =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | String str =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Binary w n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | «Type» =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | FunType =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Var n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeType s d =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeTypeRef s =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtcAppType T U =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtSel s d i j =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | USort n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UConst n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
termination_by sizeOf t
decreasing_by
  simp_wf
  omega

theorem is_cons_app_apply_model_eval_is_apply
    (M : SmtModel) (hM : model_wf M)
    (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    ∃ v x,
      __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
        SmtValue.Apply v x := by
  intro hCons hTrans
  rcases ctorSpineRoot_of_is_cons_app_true (Term.Apply f a) hCons with
    ⟨root, hRoot⟩
  exact ctorSpineRoot_apply_eval_is_apply M hM hRoot hTrans

theorem is_cons_app_apply_eval_eq_apply_of_not_tuple
    (M : SmtModel) (hM : model_wf M)
    (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    (∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
      SmtValue.Apply
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt a)) := by
  intro hCons hNotTuple hTrans
  rcases ctorSpineRoot_of_is_cons_app_true (Term.Apply f a) hCons with
    ⟨root, hRoot⟩
  cases hRoot with
  | app y hPrev =>
      rcases ctorSpineRoot_root_cases hPrev with hTuple | hRest
      · have hPrevTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
          simpa [hTuple] using hPrev
        rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hPrevTuple with
          hNone | hOne
        · exact False.elim (hTrans hNone)
        · rcases hOne with ⟨head, hF⟩
          exact False.elim (hNotTuple head hF)
      · rcases hRest with hUnit | hDt
        · have hPrevUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
            simpa [hUnit] using hPrev
          exact False.elim
            (hTrans (ctorSpineRoot_tupleUnit_apply_type_none hPrevUnit))
        · rcases hDt with ⟨s, d, i, hRootDt⟩
          have hPrevDt : CtorSpineRoot f (Term.DtCons s d i) := by
            simpa [hRootDt] using hPrev
          have hDtSp : DtConsSpineRoot f s d i :=
            dtConsSpineRoot_of_ctor_dtCons hPrevDt
          exact dtConsSpineRoot_apply_eval_eq_apply M hM hDtSp a hTrans

theorem is_cons_app_apply_head_has_smt_translation_of_not_tuple
    (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    (∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation f := by
  intro hCons hNotTuple hTrans
  rcases ctorSpineRoot_of_is_cons_app_true (Term.Apply f a) hCons with
    ⟨root, hRoot⟩
  cases hRoot with
  | app y hPrev =>
      rcases ctorSpineRoot_root_cases hPrev with hTuple | hRest
      · have hPrevTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
          simpa [hTuple] using hPrev
        rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hPrevTuple with
          hNone | hOne
        · exact False.elim (hTrans hNone)
        · rcases hOne with ⟨head, hF⟩
          exact False.elim (hNotTuple head hF)
      · rcases hRest with hUnit | hDt
        · have hPrevUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
            simpa [hUnit] using hPrev
          exact False.elim
            (hTrans (ctorSpineRoot_tupleUnit_apply_type_none hPrevUnit))
        · rcases hDt with ⟨s, d, i, hRootDt⟩
          have hPrevDt : CtorSpineRoot f (Term.DtCons s d i) := by
            simpa [hRootDt] using hPrev
          have hDtSp : DtConsSpineRoot f s d i :=
            dtConsSpineRoot_of_ctor_dtCons hPrevDt
          exact dtConsSpineRoot_head_translation_of_apply_translation
            hDtSp a hTrans

theorem is_cons_app_apply_arg_has_smt_translation
    (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation a := by
  intro hCons hTrans
  rcases ctorSpineRoot_of_is_cons_app_true (Term.Apply f a) hCons with
    ⟨root, hRoot⟩
  cases hRoot with
  | app y hPrev =>
      rcases ctorSpineRoot_root_cases hPrev with hTuple | hRest
      · have hPrevTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
          simpa [hTuple] using hPrev
        rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hPrevTuple with
          hNone | hOne
        · exact False.elim (hTrans hNone)
        · rcases hOne with ⟨head, hF⟩
          subst f
          unfold RuleProofs.eo_has_smt_translation
          change
            __smtx_typeof
                (__eo_to_smt_tuple_prepend (__eo_to_smt head)
                  (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt a)) ≠
              SmtType.None at hTrans
          rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
              a head hTrans with
            ⟨c, hTailTy⟩
          rw [hTailTy]
          simp
      · rcases hRest with hUnit | hDt
        · have hPrevUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
            simpa [hUnit] using hPrev
          exact False.elim
            (hTrans (ctorSpineRoot_tupleUnit_apply_type_none hPrevUnit))
        · rcases hDt with ⟨s, d, i, hRootDt⟩
          have hPrevDt : CtorSpineRoot f (Term.DtCons s d i) := by
            simpa [hRootDt] using hPrev
          have hDtSp : DtConsSpineRoot f s d i :=
            dtConsSpineRoot_of_ctor_dtCons hPrevDt
          have hTo := dtConsSpineRoot_apply_generic hDtSp a
          have hGen : generic_apply_type (__eo_to_smt f) (__eo_to_smt a) :=
            generic_apply_type_of_non_datatype_head
              (dtConsSpineRoot_to_smt_ne_dt_sel hDtSp)
              (dtConsSpineRoot_to_smt_ne_dt_tester hDtSp)
          have hApplyNN :
              __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
                  (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
            unfold RuleProofs.eo_has_smt_translation at hTrans
            rw [hTo] at hTrans
            unfold generic_apply_type at hGen
            rw [hGen] at hTrans
            exact hTrans
          rcases typeof_apply_non_none_cases hApplyNN with
            ⟨A, B, hHead, hArg, hANN, hBNN⟩
          unfold RuleProofs.eo_has_smt_translation
          rw [hArg]
          exact hANN

theorem is_cons_app_apply_head_type_ne_result_of_not_tuple
    (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    (∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    __smtx_typeof (__eo_to_smt f) ≠
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) := by
  intro hCons hNotTuple hTrans
  rcases ctorSpineRoot_of_is_cons_app_true (Term.Apply f a) hCons with
    ⟨root, hRoot⟩
  cases hRoot with
  | app y hPrev =>
      rcases ctorSpineRoot_root_cases hPrev with hTuple | hRest
      · have hPrevTuple : CtorSpineRoot f (Term.UOp UserOp.tuple) := by
          simpa [hTuple] using hPrev
        rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hPrevTuple with
          hNone | hOne
        · exact False.elim (hTrans hNone)
        · rcases hOne with ⟨head, hF⟩
          exact False.elim (hNotTuple head hF)
      · rcases hRest with hUnit | hDt
        · have hPrevUnit : CtorSpineRoot f (Term.UOp UserOp.tuple_unit) := by
            simpa [hUnit] using hPrev
          exact False.elim
            (hTrans (ctorSpineRoot_tupleUnit_apply_type_none hPrevUnit))
        · rcases hDt with ⟨s, d, i, hRootDt⟩
          have hPrevDt : CtorSpineRoot f (Term.DtCons s d i) := by
            simpa [hRootDt] using hPrev
          have hDtSp : DtConsSpineRoot f s d i :=
            dtConsSpineRoot_of_ctor_dtCons hPrevDt
          have hTo := dtConsSpineRoot_apply_generic hDtSp a
          have hGen : generic_apply_type (__eo_to_smt f) (__eo_to_smt a) :=
            generic_apply_type_of_non_datatype_head
              (dtConsSpineRoot_to_smt_ne_dt_sel hDtSp)
              (dtConsSpineRoot_to_smt_ne_dt_tester hDtSp)
          have hApplyNN :
              __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) ≠
                SmtType.None := by
            unfold RuleProofs.eo_has_smt_translation at hTrans
            simpa [hTo] using hTrans
          have hNe :=
            smt_apply_head_type_ne_result hGen hApplyNN
          intro hEq
          apply hNe
          simpa [hTo] using hEq

private theorem mk_dt_cons_eq_same_ctor_spine
    (t s : Term) :
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    ∃ root, CtorSpineRoot t root ∧ CtorSpineRoot s root := by
  intro h
  fun_cases __mk_dt_cons_eq t s
  · exact False.elim (h (mk_dt_cons_eq_stuck_left s))
  · exact False.elim (h (mk_dt_cons_eq_stuck_right t))
  · rename_i a as b bs
    subst_vars
    refine ⟨Term.UOp UserOp.tuple, ?_, ?_⟩
    · exact CtorSpineRoot.app as
        (CtorSpineRoot.app a CtorSpineRoot.tuple)
    · exact CtorSpineRoot.app bs
        (CtorSpineRoot.app b CtorSpineRoot.tuple)
  · rename_i f a g b hNotTuple
    subst_vars
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right ≠
          Term.Stuck := by
      simpa [__mk_dt_cons_eq, right] using h
    have hLeft : __mk_dt_cons_eq f g ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    rcases mk_dt_cons_eq_same_ctor_spine f g hLeft with ⟨root, hf, hg⟩
    exact ⟨root, CtorSpineRoot.app a hf, CtorSpineRoot.app b hg⟩
  · rename_i c c2
    have hReq' := h
    simp_all (maxSteps := 1000000)
      [__mk_dt_cons_eq, __eo_requires, __eo_eq, __eo_ite, __eo_is_eq,
      __eo_is_ok, __eo_dt_selectors, __eo_dt_selectors_main, native_ite,
      native_teq, native_and, native_not, SmtEval.native_and,
      SmtEval.native_not]
    rcases hReq'.1 with hTuple | hUnit | hSelectors
    · subst t
      exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple⟩
    · subst t
      exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineRoot.tupleUnit⟩
    · cases t <;> simp at hSelectors
      case DtCons =>
        exact ⟨_, CtorSpineRoot.dtCons _ _ _⟩
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem mk_dt_cons_eq_ctor_spine_eq
    (t s : Term) :
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    ∃ root, CtorSpineEq t s root := by
  intro h
  fun_cases __mk_dt_cons_eq t s
  · exact False.elim (h (mk_dt_cons_eq_stuck_left s))
  · exact False.elim (h (mk_dt_cons_eq_stuck_right t))
  · rename_i a as b bs
    subst_vars
    refine ⟨Term.UOp UserOp.tuple, ?_⟩
    exact CtorSpineEq.app as bs
      (CtorSpineEq.app a b CtorSpineEq.tuple)
  · rename_i f a g b hNotTuple
    subst_vars
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right ≠
          Term.Stuck := by
      simpa [__mk_dt_cons_eq, right] using h
    have hLeft : __mk_dt_cons_eq f g ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    rcases mk_dt_cons_eq_ctor_spine_eq f g hLeft with ⟨root, hfg⟩
    exact ⟨root, CtorSpineEq.app a b hfg⟩
  · rename_i c c2
    have hReq' := h
    simp_all (maxSteps := 1000000)
      [__mk_dt_cons_eq, __eo_requires, __eo_eq, __eo_ite, __eo_is_eq,
      __eo_is_ok, __eo_dt_selectors, __eo_dt_selectors_main, native_ite,
      native_teq, native_and, native_not, SmtEval.native_and,
      SmtEval.native_not]
    rcases hReq'.1 with hTuple | hUnit | hSelectors
    · subst t
      exact ⟨Term.UOp UserOp.tuple, CtorSpineEq.tuple⟩
    · subst t
      exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineEq.tupleUnit⟩
    · cases t <;> simp at hSelectors
      case DtCons =>
        exact ⟨_, CtorSpineEq.dtCons _ _ _⟩
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

theorem dt_cons_apply_model_eval_eq_false_of_component
    (M : SmtModel) (hM : model_wf M)
    (f g a b : Term) :
    __mk_dt_cons_eq f g ≠ Term.Stuck ->
    (∀ x y,
      f = Term.Apply (Term.UOp UserOp.tuple) x ->
      g = Term.Apply (Term.UOp UserOp.tuple) y -> False) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f a) ->
    RuleProofs.eo_has_smt_translation (Term.Apply g b) ->
    (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g)) = SmtValue.Boolean false ∨
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false) ->
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b))) =
      SmtValue.Boolean false := by
  intro hMk hNotTuple hLeftTrans hRightTrans hComponent
  rcases mk_dt_cons_eq_ctor_spine_eq f g hMk with ⟨root, hSp⟩
  rcases ctorSpineEq_root_cases hSp with hRootTuple | hRest
  · have hSpTuple : CtorSpineEq f g (Term.UOp UserOp.tuple) := by
      simpa [hRootTuple] using hSp
    exact False.elim
      (ctorSpineEq_tuple_apply_translation_false
        hSpTuple hNotTuple hLeftTrans hRightTrans)
  rcases hRest with hRootUnit | hRootDt
  · have hSpUnit : CtorSpineEq f g (Term.UOp UserOp.tuple_unit) := by
      simpa [hRootUnit] using hSp
    exact False.elim
      (ctorSpineEq_tupleUnit_apply_translation_false
        (b := b) hSpUnit hLeftTrans)
  · rcases hRootDt with ⟨s, d, i, hRootDt⟩
    have hSpDt : CtorSpineEq f g (Term.DtCons s d i) := by
      simpa [hRootDt] using hSp
    exact dtCons_ctor_spine_eq_apply_eval_eq_false_of_component
      M hM a b hSpDt hLeftTrans hRightTrans hComponent

private theorem eval_eo_eq_is_boolean (M : SmtModel) (x y : Term) :
    ∃ b : Bool,
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) =
        SmtValue.Boolean b := by
  rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
  exact model_eval_eq_is_boolean
    (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y))

private theorem eval_and_bool_components
    (M : SmtModel) (x y : Term) :
    (∃ b : Bool,
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) =
          SmtValue.Boolean b) ->
      (∃ bx : Bool, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean bx) ∧
        (∃ byy : Bool, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean byy) := by
  intro hEval
  rcases hEval with ⟨b, hEval⟩
  rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9] at hEval
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
    simp [hx, hy, __smtx_model_eval_and, SmtEval.native_and] at hEval
  case Boolean.Boolean bx byy =>
    constructor
    · refine ⟨bx, ?_⟩
      rfl
    · refine ⟨byy, ?_⟩
      rfl

private theorem concat_rec_eval_eq_and
    (M : SmtModel) {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    (∃ b1 : Bool, __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Boolean b1) ->
    (∃ b2 : Bool, __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Boolean b2) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec c1 c2)) =
      __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt c1))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hC1 hC2 hEval1 hEval2
  induction hC1 generalizing c2 with
  | true =>
      rcases hEval2 with ⟨b2, hEval2⟩
      rw [and_concat_rec_true c2]
      rw [hEval2]
      cases b2 <;>
        simp [__smtx_model_eval.eq_1,
          __smtx_model_eval_and, SmtEval.native_and]
  | cons x xs hXs ih =>
      have hComps := eval_and_bool_components M x xs hEval1
      have hTail : CnfSupport.AndList (__eo_list_concat_rec xs c2) :=
        concat_rec_preserves_andList hXs hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        CnfSupport.andList_ne_stuck hTail
      rcases hComps with ⟨hEvalX, hEvalXs⟩
      rcases hEvalX with ⟨bx, hEvalX⟩
      rcases hEvalXs with ⟨bxs, hEvalXs⟩
      rcases hEval2 with ⟨b2, hEval2⟩
      have hEvalAndXs :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs)) =
            SmtValue.Boolean (native_and bx bxs) := by
        rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9, hEvalX, hEvalXs]
        simp [__smtx_model_eval_and, SmtEval.native_and]
      rw [and_concat_rec_cons x xs c2 hTailNe]
      rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9]
      rw [ih hC2 ⟨bxs, hEvalXs⟩ ⟨b2, hEval2⟩]
      rw [hEvalX, hEvalXs, hEval2, hEvalAndXs]
      cases bx <;> cases bxs <;> cases b2 <;>
        simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem concat_eval_eq_and
    (M : SmtModel) {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    (∃ b1 : Bool, __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Boolean b1) ->
    (∃ b2 : Bool, __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Boolean b2) ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.and) c1 c2)) =
      __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt c1))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hC1 hC2 hEval1 hEval2
  simp [__eo_list_concat, CnfSupport.andList_is_list_true hC1,
    CnfSupport.andList_is_list_true hC2, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]
  exact concat_rec_eval_eq_and M hC1 hC2 hEval1 hEval2

private theorem singleton_elim_eval_eq
    (M : SmtModel) {c : Term} :
    CnfSupport.AndList c ->
    (∃ b : Bool, __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean b) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hC hEval
  rw [__eo_list_singleton_elim, CnfSupport.andList_is_list_true hC]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hC with
  | true =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      cases hXs with
      | true =>
          have hComps := eval_and_bool_components M x (Term.Boolean true) hEval
          rcases hComps with ⟨hEvalX, _⟩
          rcases hEvalX with ⟨bx, hEvalX⟩
          have hSingleton :
              __eo_list_singleton_elim_2
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (Term.Boolean true)) =
              x := by
            simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite, native_ite,
              native_teq]
          have hEvalAndTrue :
              __smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (Term.Boolean true))) =
                __smtx_model_eval M (__eo_to_smt x) := by
            rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9, hEvalX]
            simp [__smtx_model_eval.eq_1,
              __smtx_model_eval_and, SmtEval.native_and]
          rw [hSingleton]
          exact hEvalAndTrue.symm
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite, native_ite,
            native_teq]

private theorem mk_dt_cons_eq_base_andList
    (c c2 : Term) :
    __eo_requires (__eo_eq c c2) (Term.Boolean true)
      (__eo_requires
        (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
            (__eo_is_ok (__eo_dt_selectors c))))
        (Term.Boolean true) (Term.Boolean true)) ≠ Term.Stuck ->
    CnfSupport.AndList
      (__eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true))) := by
  intro hReq
  have hReq' := hReq
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  have hBaseTrue :
      __eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true)) = Term.Boolean true := by
    rcases hReq' with ⟨hEq, _hEqNe, hCons, hConsNe⟩
    simp [__eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not, hEq, hCons, hConsNe]
  rw [hBaseTrue]
  exact CnfSupport.AndList.true

private theorem mk_dt_cons_eq_base_eval_eq
    (M : SmtModel) (c c2 : Term) :
    __eo_requires (__eo_eq c c2) (Term.Boolean true)
      (__eo_requires
        (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
            (__eo_is_ok (__eo_dt_selectors c))))
        (Term.Boolean true) (Term.Boolean true)) ≠ Term.Stuck ->
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_requires (__eo_eq c c2) (Term.Boolean true)
            (__eo_requires
              (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
                (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
                  (__eo_is_ok (__eo_dt_selectors c))))
              (Term.Boolean true) (Term.Boolean true)))) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hReq
  have hReq' := hReq
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  rcases hReq' with ⟨hEq, _hEqNe, hCons, hConsNe⟩
  have hEq' : c2 = c := eo_eq_eq_of_true hEq
  have hBaseTrue :
      __eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true)) = Term.Boolean true := by
    simp [__eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not, hEq, hCons, hConsNe]
  subst c2
  have hRefl :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt c)) = SmtValue.Boolean true :=
    RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt c))
  rw [hBaseTrue]
  rw [eo_to_smt_true_eq]
  rw [__smtx_model_eval.eq_1, hRefl]

private theorem mk_apply_and_preserves_andList
    (x xs : Term) :
    CnfSupport.AndList xs ->
    CnfSupport.AndList (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x) xs) := by
  intro hXs
  cases hXs with
  | true =>
      simp [__eo_mk_apply]
      exact CnfSupport.AndList.cons x (Term.Boolean true) CnfSupport.AndList.true
  | cons y ys hYs =>
      simp [__eo_mk_apply]
      exact CnfSupport.AndList.cons x
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) ys)
        (CnfSupport.AndList.cons y ys hYs)

private theorem mk_dt_cons_eq_andList_of_not_stuck
    (t s : Term) :
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    CnfSupport.AndList (__mk_dt_cons_eq t s) := by
  intro h
  fun_cases __mk_dt_cons_eq t s
  · exact False.elim (h (mk_dt_cons_eq_stuck_left s))
  · exact False.elim (h (mk_dt_cons_eq_stuck_right t))
  · rename_i a as b bs
    subst_vars
    have hTail : __mk_dt_cons_eq as bs ≠ Term.Stuck := by
      intro hTailStuck
      apply h
      exact by simp [__mk_dt_cons_eq, __eo_mk_apply, hTailStuck]
    exact mk_apply_and_preserves_andList
      (Term.Apply (Term.Apply Term.eq a) b)
      (__mk_dt_cons_eq as bs)
      (mk_dt_cons_eq_andList_of_not_stuck as bs hTail)
  · rename_i f a g b hNotTuple
    subst_vars
    have _hNotTuple := hNotTuple
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    change CnfSupport.AndList
      (__eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right)
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right ≠
          Term.Stuck := by
      simpa [__mk_dt_cons_eq] using h
    have hLeft : __mk_dt_cons_eq f g ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    have hLeftList : CnfSupport.AndList (__mk_dt_cons_eq f g) :=
      mk_dt_cons_eq_andList_of_not_stuck f g hLeft
    have hRightList : CnfSupport.AndList right :=
      CnfSupport.AndList.cons
        (Term.Apply (Term.Apply Term.eq a) b)
        (Term.Boolean true)
        CnfSupport.AndList.true
    exact concat_preserves_andList hLeftList hRightList
  · subst_vars
    exact mk_dt_cons_eq_base_andList _ _ (by simpa [__mk_dt_cons_eq] using h)
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem mk_dt_cons_eq_eval_eq
    (M : SmtModel) (hM : model_wf M) (t s : Term) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t) s) ->
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt s)) := by
  intro hBool h
  fun_cases __mk_dt_cons_eq t s
  · exact False.elim (h (mk_dt_cons_eq_stuck_left s))
  · exact False.elim (h (mk_dt_cons_eq_stuck_right t))
  · rename_i a as b bs
    subst_vars
    have hComponentBool :=
      tuple_eq_has_bool_type_components a as b bs hBool
    have hHeadBool :
        RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) :=
      hComponentBool.1
    have hTailBool :
        RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq as) bs) :=
      hComponentBool.2
    have hTail : __mk_dt_cons_eq as bs ≠ Term.Stuck := by
      intro hTailStuck
      apply h
      exact by simp [__mk_dt_cons_eq, __eo_mk_apply, hTailStuck]
    have hTailEval := mk_dt_cons_eq_eval_eq M hM as bs hTailBool hTail
    rcases eval_eo_eq_is_boolean M a b with ⟨b1, hEqABEval⟩
    have hMkApply :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
          (__mk_dt_cons_eq as bs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
          (__mk_dt_cons_eq as bs) := by
      cases hTailEq : __mk_dt_cons_eq as bs
      case Stuck =>
        exact False.elim (hTail hTailEq)
      all_goals simp [__eo_mk_apply]
    rw [hMkApply]
    rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9, hEqABEval, hTailEval]
    have hTupleEval := tuple_prepend_eval_eq_and M hM a as b bs hBool
    have hHeadEval :
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) =
            SmtValue.Boolean b1 := by
      simpa [eo_to_smt_eq_eq, smtx_eval_eq_term_eq] using hEqABEval
    rw [hTupleEval, hHeadEval]
  · rename_i f a g b hNotTuple
    subst_vars
    let left := __mk_dt_cons_eq f g
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    change __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.and) left right)) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b)))
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) left right ≠ Term.Stuck := by
      simpa [left, right, __mk_dt_cons_eq] using h
    have hLeft : left ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    rcases mk_dt_cons_eq_ctor_spine_eq f g hLeft with ⟨root, hSp⟩
    rcases ctorSpineEq_root_cases hSp with hRootTuple | hRest
    · have hSpTuple : CtorSpineEq f g (Term.UOp UserOp.tuple) := by
        simpa [hRootTuple] using hSp
      exact False.elim
        (ctorSpineEq_tuple_apply_bool_false hSpTuple hNotTuple hBool)
    rcases hRest with hRootUnit | hRootDt
    · have hSpUnit : CtorSpineEq f g (Term.UOp UserOp.tuple_unit) := by
        simpa [hRootUnit] using hSp
      exact False.elim
        (ctorSpineEq_tupleUnit_apply_bool_false hSpUnit hBool)
    rcases hRootDt with ⟨s0, d0, i0, hRootDt⟩
    have hSpDt : CtorSpineEq f g (Term.DtCons s0 d0 i0) := by
      simpa [hRootDt] using hSp
    have hComps :=
      dtCons_ctor_spine_eq_apply_bool_components a b hSpDt hBool
    have hLeftBool :
        RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq f) g) :=
      hComps.1
    have hArgBool :
        RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b) :=
      hComps.2
    have hLeftList : CnfSupport.AndList left :=
      mk_dt_cons_eq_andList_of_not_stuck f g hLeft
    have hRightList : CnfSupport.AndList right :=
      CnfSupport.AndList.cons
        (Term.Apply (Term.Apply Term.eq a) b)
        (Term.Boolean true)
        CnfSupport.AndList.true
    have hLeftEval := mk_dt_cons_eq_eval_eq M hM f g hLeftBool hLeft
    have hLeftEvalBool :
        ∃ bl : Bool, __smtx_model_eval M (__eo_to_smt left) = SmtValue.Boolean bl := by
      rw [hLeftEval]
      exact model_eval_eq_is_boolean
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g))
    rcases eval_eo_eq_is_boolean M a b with ⟨br, hEqABEval⟩
    have hArgEval :
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) =
            SmtValue.Boolean br := by
      simpa [eo_to_smt_eq_eq, smtx_eval_eq_term_eq] using hEqABEval
    have hRightEvalBool :
        ∃ br' : Bool, __smtx_model_eval M (__eo_to_smt right) = SmtValue.Boolean br' := by
      refine ⟨br, ?_⟩
      rw [eo_to_smt_and_eq, __smtx_model_eval.eq_9, hEqABEval]
      rw [eo_to_smt_true_eq, __smtx_model_eval.eq_1]
      simp [__smtx_model_eval_and, SmtEval.native_and]
    have hApplyEval :=
      dtCons_ctor_spine_eq_apply_eval_eq_and M hM a b hSpDt hBool
    rw [hApplyEval, hArgEval]
    rw [concat_eval_eq_and M hLeftList hRightList hLeftEvalBool hRightEvalBool]
    rw [hLeftEval, eo_to_smt_and_eq, __smtx_model_eval.eq_9, hEqABEval]
    rw [eo_to_smt_true_eq, __smtx_model_eval.eq_1]
    simp [__smtx_model_eval_and, SmtEval.native_and]
  · subst_vars
    exact mk_dt_cons_eq_base_eval_eq M _ _ (by simpa [__mk_dt_cons_eq] using h)
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf; omega

theorem dt_cons_eq_condition_rel
    (M : SmtModel) (hM : model_wf M) (t s : Term) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t) s) ->
    __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s) ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq t) s)))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)))) := by
  intro hBool hCond
  have hMk : __mk_dt_cons_eq t s ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hCond
    simp [__eo_list_singleton_elim, __eo_is_list, __eo_requires, native_ite, native_teq] at hCond
  have hList : CnfSupport.AndList (__mk_dt_cons_eq t s) :=
    mk_dt_cons_eq_andList_of_not_stuck t s hMk
  have hMkEval := mk_dt_cons_eq_eval_eq M hM t s hBool hMk
  have hMkEvalBool :
      ∃ b : Bool,
        __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) = SmtValue.Boolean b := by
    rw [hMkEval]
    exact model_eval_eq_is_boolean
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt s))
  have hCondEval :
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s))) =
        __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) :=
    singleton_elim_eval_eq M hList hMkEvalBool
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hCondEval, hMkEval, eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt s)))
