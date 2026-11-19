module

public import Cpc.Proofs.RuleSupport.TupleSpineSupport
import all Cpc.Proofs.RuleSupport.TupleSpineSupport
import all Cpc.Proofs.RuleSupport.DtConsEqSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-!
Support for the (non-tuple) `update` case of `dt-collapse-updater` when the
updated selector belongs to the constructor at the head of the updated term:
`(update s (C x0 ... xk) a) = (C x0 ... a ... xk)`.
-/

/-- `t` is `r` applied to the arguments `xs`, in order. -/
inductive DtAppSpine : Term -> Term -> List Term -> Prop
  | root (r : Term) : DtAppSpine r r []
  | app {f r : Term} {xs : List Term} (x : Term) :
      DtAppSpine f r xs -> DtAppSpine (Term.Apply f x) r (xs ++ [x])

private theorem dcu_spine_root (s : native_String) (d : DatatypeDecl)
    (i : native_Nat) :
    ∀ {t r : Term} {xs : List Term}, DtAppSpine t r xs ->
      r = Term.DtCons s d i -> DtConsSpineRoot t s d i := by
  intro t r xs hSp
  induction hSp with
  | root r =>
      intro hr
      subst hr
      exact DtConsSpineRoot.root s d i
  | app x _ ih =>
      intro hr
      exact DtConsSpineRoot.app x (ih hr)

private theorem dcu_spine_ne_stuck :
    ∀ {t r : Term} {xs : List Term}, DtAppSpine t r xs ->
      r ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro t r xs hSp
  induction hSp with
  | root r => intro hr; exact hr
  | app x _ _ => intro _ h; cases h

/-! ### Evaluation of constructor spines -/

private theorem dcu_spine_eval_components
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (d : DatatypeDecl) (i : native_Nat)
    (hRes : __eo_to_smt_reserved_datatype_name s = false) :
    ∀ {t r : Term} {xs : List Term}, DtAppSpine t r xs ->
      r = Term.DtCons s d i ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt t)) =
          SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i ∧
        vsm_num_apply_args (__smtx_model_eval M (__eo_to_smt t)) = xs.length ∧
        ∀ (q : Nat) (h : Term), xs[q]? = some h ->
          __smtx_apply_arg_nth_value (__smtx_model_eval M (__eo_to_smt t)) q
              xs.length =
            __smtx_model_eval M (__eo_to_smt h) := by
  intro t r xs hSp
  induction hSp with
  | root r =>
      intro hr _hNN
      subst hr
      have hEv :
          __smtx_model_eval M (__eo_to_smt (Term.DtCons s d i)) =
            SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i := by
        rw [eo_to_smt_dtCons_eq]
        simp [native_ite, hRes, __smtx_model_eval]
      refine ⟨?_, ?_, ?_⟩
      · rw [hEv]
        rfl
      · rw [hEv]
        rfl
      · intro q h hq
        simp at hq
  | @app f r0 xs0 x hSp ih =>
      intro hr hNN
      have hRoot := dcu_spine_root s d i hSp hr
      have hTo := dtConsSpineRoot_apply_generic hRoot x
      have hGen : generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hRoot)
          (dtConsSpineRoot_to_smt_ne_dt_tester hRoot)
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
              (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
        have hNN' := hNN
        rw [hTo] at hNN'
        unfold generic_apply_type at hGen
        rw [hGen] at hNN'
        exact hNN'
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hHead, _hX, _hANN, _hBNN⟩
      have hHeadNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
        rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
      rcases ih hr hHeadNN with ⟨hH, hC, hA⟩
      have hEval := dtConsSpineRoot_apply_eval_eq_apply M hM hRoot x hNN
      rw [hEval]
      refine ⟨?_, ?_, ?_⟩
      · simpa [__smtx_apply_head_value] using hH
      · simp [vsm_num_apply_args, hC]
      · intro q h hq
        simp only [List.length_append, List.length_singleton]
        by_cases hqx : q = xs0.length
        · subst hqx
          simp at hq
          subst hq
          simp [__smtx_apply_arg_nth_value, SmtEval.native_nateq, native_ite]
        · have hlt : q < xs0.length := by
            have := (List.getElem?_eq_some_iff.mp hq).1
            simp at this
            omega
          have hq' : xs0[q]? = some h := by
            rw [List.getElem?_append_left hlt] at hq
            exact hq
          simp [__smtx_apply_arg_nth_value, SmtEval.native_nateq, native_ite,
            hqx, hA q h hq']

/-! ### The EO-level shape of `$dt_collapse_updater_rhs` -/

private theorem dcu_collapse_rhs_root_stuck (r a : Term) (m : Int)
    (hNotApp : ∀ f x, r ≠ Term.Apply f x) :
    __dt_collapse_updater_rhs r a (Term.Numeral m) = Term.Stuck := by
  rw [__dt_collapse_updater_rhs.eq_def]
  split <;> first | exact absurd rfl (hNotApp _ _) | simp_all

private theorem dcu_collapse_rhs_zero (f x a : Term) (ha : a ≠ Term.Stuck) :
    __dt_collapse_updater_rhs (Term.Apply f x) a (Term.Numeral 0) =
      Term.Apply f a := by
  rw [__dt_collapse_updater_rhs.eq_def]
  split <;> simp_all

private theorem dcu_collapse_rhs_succ (f x a : Term) (m : Int)
    (ha : a ≠ Term.Stuck) (hm : m ≠ 0) :
    __dt_collapse_updater_rhs (Term.Apply f x) a (Term.Numeral m) =
      __eo_mk_apply (__dt_collapse_updater_rhs f a (Term.Numeral (m - 1))) x := by
  conv_lhs => rw [__dt_collapse_updater_rhs.eq_def]
  split <;> simp_all [__eo_add, native_zplus, SmtEval.native_zplus,
    Int.sub_eq_add_neg]

private theorem dcu_mk_apply_of_ne {x y : Term}
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  unfold __eo_mk_apply
  split <;> simp_all

private theorem dcu_collapse_rhs_spine (a : Term) (ha : a ≠ Term.Stuck) :
    ∀ {t r : Term} {xs : List Term}, DtAppSpine t r xs ->
      r ≠ Term.Stuck -> (∀ f x, r ≠ Term.Apply f x) ->
      ∀ m : Int, __dt_collapse_updater_rhs t a (Term.Numeral m) ≠ Term.Stuck ->
        0 ≤ m ∧ m < xs.length ∧
          DtAppSpine (__dt_collapse_updater_rhs t a (Term.Numeral m)) r
            (xs.set (xs.length - 1 - m.toNat) a) := by
  intro t r xs hSp
  induction hSp with
  | root r =>
      intro _hr hNotApp m hNe
      exact absurd (dcu_collapse_rhs_root_stuck r a m hNotApp) hNe
  | @app f r0 xs0 x hSp ih =>
      intro hr hNotApp m hNe
      by_cases hm : m = 0
      · subst hm
        rw [dcu_collapse_rhs_zero f x a ha]
        refine ⟨le_refl _, by simp <;> omega, ?_⟩
        have hSet : (xs0 ++ [x]).set ((xs0 ++ [x]).length - 1 - (0 : Int).toNat) a =
            xs0 ++ [a] := by
          simp
        rw [hSet]
        exact DtAppSpine.app a hSp
      · rw [dcu_collapse_rhs_succ f x a m ha hm] at hNe ⊢
        have hInnerNe :
            __dt_collapse_updater_rhs f a (Term.Numeral (m - 1)) ≠ Term.Stuck := by
          intro hStuck
          apply hNe
          rw [hStuck]
          simp [__eo_mk_apply]
        have hxNe : x ≠ Term.Stuck := by
          intro hStuck
          apply hNe
          rw [hStuck]
          cases __dt_collapse_updater_rhs f a (Term.Numeral (m - 1)) <;>
            simp [__eo_mk_apply]
        rcases ih hr hNotApp (m - 1) hInnerNe with ⟨hLo, hHi, hSp'⟩
        rw [dcu_mk_apply_of_ne hInnerNe hxNe]
        refine ⟨by omega, by simp <;> omega, ?_⟩
        have hIdx : (xs0 ++ [x]).length - 1 - m.toNat =
            xs0.length - 1 - (m - 1).toNat := by
          simp
          omega
        have hlt : xs0.length - 1 - (m - 1).toNat < xs0.length := by omega
        rw [hIdx, List.set_append_left _ _ hlt]
        exact DtAppSpine.app x hSp'

private theorem dcu_numeral_congr {x y : Int} (h : x = y) :
    Term.Numeral x = Term.Numeral y := by
  rw [h]

/-! ### Selector lists -/

private theorem dcu_get_selectors_of_app_root (T : Term) (hT : T ≠ Term.Stuck)
    (k : Nat) :
    ∀ t : Term, sizeOf t < k ->
      ∃ r xs, DtAppSpine t r xs ∧ (∀ f x, r ≠ Term.Apply f x) ∧
        __dt_get_selectors_of_app T t = __dt_get_selectors T r := by
  induction k with
  | zero => intro t hk; omega
  | succ k ih =>
      intro t hk
      by_cases hApp : ∃ f x, t = Term.Apply f x
      · rcases hApp with ⟨f, x, rfl⟩
        rcases ih f (by simp at hk; omega) with ⟨r, xs, hSp, hR, hEq⟩
        refine ⟨r, xs ++ [x], DtAppSpine.app x hSp, hR, ?_⟩
        rw [← hEq]
        rw [__dt_get_selectors_of_app.eq_def]
        split <;> simp_all
      · have hNotApp : ∀ f x, t ≠ Term.Apply f x := by
          intro f x h
          exact hApp ⟨f, x, h⟩
        refine ⟨t, [], DtAppSpine.root t, hNotApp, ?_⟩
        rw [__dt_get_selectors_of_app.eq_def]
        split
        · exact absurd rfl hT
        · cases T <;> first | rfl | exact absurd rfl hT
        · exact absurd rfl (hNotApp _ _)
        · rfl

private theorem dcu_find_rec_cons (x rest target : Term) (b : Int)
    (hT : target ≠ Term.Stuck) :
    __eo_list_find_rec
        (Term.Apply (Term.Apply Term.__eo_List_cons x) rest) target
        (Term.Numeral b) =
      __eo_ite (__eo_eq x target) (Term.Numeral b)
        (__eo_list_find_rec rest target (Term.Numeral (b + 1))) := by
  rw [__eo_list_find_rec.eq_def]
  split <;> simp_all [__eo_add, native_zplus, SmtEval.native_zplus]

private theorem dcu_find_rec_nil (target : Term) (b : Int)
    (hT : target ≠ Term.Stuck) :
    __eo_list_find_rec Term.__eo_List_nil target (Term.Numeral b) =
      Term.Numeral (-1) := by
  rw [__eo_list_find_rec.eq_def]
  split <;> simp_all

private def dcuK (d : Datatype) (ci : Nat) : Nat :=
  __smtx_dt_num_sels (__eo_to_smt_datatype d) ci

private theorem dcu_cons_selectors_len
    (s : native_String) (root : DatatypeDecl) (n : native_Nat) :
    ∀ (d : Datatype) (ci ai : Nat),
      __eo_datatype_cons_selectors_rec s root n d ci ai ≠ Term.Stuck ->
      __eo_list_len_rec (__eo_datatype_cons_selectors_rec s root n d ci ai) =
        Term.Numeral (dcuK d ci : Int)
  | Datatype.null, ci, ai, h => by
      cases ci <;> simp [__eo_datatype_cons_selectors_rec] at h
  | Datatype.sum DatatypeCons.unit d, 0, ai, h => by
      simp [__eo_datatype_cons_selectors_rec, __eo_list_len_rec, dcuK,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, h => by
      let rest :=
        __eo_datatype_cons_selectors_rec s root n
          (Datatype.sum c d) 0 (Nat.succ ai)
      have hRestNe : rest ≠ Term.Stuck := by
        intro hRest
        apply h
        simp only [__eo_datatype_cons_selectors_rec]
        change __eo_mk_apply _ rest = Term.Stuck
        rw [hRest]
        simp [__eo_mk_apply]
      have hList :
          __eo_datatype_cons_selectors_rec s root n
              (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
            Term.Apply
              (Term.Apply Term.__eo_List_cons (Term.DtSel s root n ai))
              rest := by
        simp only [__eo_datatype_cons_selectors_rec]
        exact dcu_mk_apply_of_ne (by simp) hRestNe
      have hRestLen :=
        dcu_cons_selectors_len s root n (Datatype.sum c d) 0 (Nat.succ ai)
          hRestNe
      rw [hList]
      simp only [__eo_list_len_rec]
      change __eo_add (Term.Numeral 1) (__eo_list_len_rec rest) = _
      rw [hRestLen]
      simp only [__eo_add, native_zplus, SmtEval.native_zplus, dcuK,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
      apply dcu_numeral_congr
      push_cast
      omega
  | Datatype.sum c d, Nat.succ ci, ai, h => by
      have hEq :
          __eo_datatype_cons_selectors_rec s root n (Datatype.sum c d)
              (Nat.succ ci) ai =
            __eo_datatype_cons_selectors_rec s root n d ci ai := by
        simp [__eo_datatype_cons_selectors_rec]
      have hK : dcuK (Datatype.sum c d) (Nat.succ ci) = dcuK d ci := by
        simp [dcuK, __eo_to_smt_datatype, __smtx_dt_num_sels]
      rw [hEq] at h ⊢
      rw [hK]
      exact dcu_cons_selectors_len s root n d ci ai h

/-- Find positions in the selector list of a datatype constructor. -/
private theorem dcu_cons_selectors_find
    (s : native_String) (root : DatatypeDecl) (n : native_Nat)
    (target : Term) (hT : target ≠ Term.Stuck) :
    ∀ (d : Datatype) (ci ai : Nat) (b : Int),
      __eo_is_neg
          (__eo_list_find_rec
            (__eo_datatype_cons_selectors_rec s root n d ci ai)
            target (Term.Numeral b)) =
        Term.Boolean false ->
      ∃ q : Nat, target = Term.DtSel s root n q ∧ ai ≤ q ∧
        q < ai + dcuK d ci ∧
        __eo_list_find_rec
            (__eo_datatype_cons_selectors_rec s root n d ci ai)
            target (Term.Numeral b) =
          Term.Numeral (b + ((q : Int) - (ai : Int)))
  | Datatype.null, ci, ai, b, h => by
      cases ci <;>
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec,
          __eo_is_neg] at h
  | Datatype.sum DatatypeCons.unit d, 0, ai, b, h => by
      exfalso
      have hNil :
          __eo_datatype_cons_selectors_rec s root n
              (Datatype.sum DatatypeCons.unit d) 0 ai = Term.__eo_List_nil := by
        simp [__eo_datatype_cons_selectors_rec]
      rw [hNil, dcu_find_rec_nil target b hT] at h
      simp [__eo_is_neg, native_zlt, SmtEval.native_zlt] at h
  | Datatype.sum (DatatypeCons.cons U c) d, 0, ai, b, h => by
      let rest :=
        __eo_datatype_cons_selectors_rec s root n
          (Datatype.sum c d) 0 (Nat.succ ai)
      have hRestNe : rest ≠ Term.Stuck := by
        intro hRest
        have hSt :
            __eo_datatype_cons_selectors_rec s root n
                (Datatype.sum (DatatypeCons.cons U c) d) 0 ai = Term.Stuck := by
          simp only [__eo_datatype_cons_selectors_rec]
          change __eo_mk_apply _ rest = Term.Stuck
          rw [hRest]
          simp [__eo_mk_apply]
        rw [hSt] at h
        simp [__eo_list_find_rec, __eo_is_neg] at h
      have hList :
          __eo_datatype_cons_selectors_rec s root n
              (Datatype.sum (DatatypeCons.cons U c) d) 0 ai =
            Term.Apply
              (Term.Apply Term.__eo_List_cons (Term.DtSel s root n ai))
              rest := by
        simp only [__eo_datatype_cons_selectors_rec]
        exact dcu_mk_apply_of_ne (by simp) hRestNe
      have hK : dcuK (Datatype.sum (DatatypeCons.cons U c) d) 0 =
          dcuK (Datatype.sum c d) 0 + 1 := by
        simp [dcuK, __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
          __smtx_dt_num_sels, __smtx_dtc_num_sels]
      rw [hList] at h ⊢
      rw [dcu_find_rec_cons _ _ _ _ hT] at h ⊢
      by_cases hHead : Term.DtSel s root n ai = target
      · subst hHead
        refine ⟨ai, rfl, le_refl _, by rw [hK]; omega, ?_⟩
        simp [__eo_eq, native_teq, __eo_ite, native_ite]
      · have hEqF : __eo_eq (Term.DtSel s root n ai) target = Term.Boolean false := by
          rw [__eo_eq.eq_def]
          split <;> simp_all [native_teq]
          intro h'
          exact hHead h'.symm
        have hIteF : ∀ x y : Term, __eo_ite (Term.Boolean false) x y = y := by
          intro x y
          simp [__eo_ite, native_ite, native_teq]
        rw [hEqF, hIteF] at h ⊢
        rcases dcu_cons_selectors_find s root n target hT (Datatype.sum c d) 0
            (Nat.succ ai) (b + 1) h with
          ⟨q, hq, hLe, hLt, hFind⟩
        refine ⟨q, hq, ?_, ?_, ?_⟩
        · omega
        · rw [hK]
          omega
        rw [hFind]
        apply dcu_numeral_congr
        push_cast
        omega
  | Datatype.sum c d, Nat.succ ci, ai, b, h => by
      have hEq :
          __eo_datatype_cons_selectors_rec s root n (Datatype.sum c d)
              (Nat.succ ci) ai =
            __eo_datatype_cons_selectors_rec s root n d ci ai := by
        simp [__eo_datatype_cons_selectors_rec]
      have hK : dcuK (Datatype.sum c d) (Nat.succ ci) = dcuK d ci := by
        simp [dcuK, __eo_to_smt_datatype, __smtx_dt_num_sels]
      rw [hEq] at h ⊢
      rw [hK]
      exact dcu_cons_selectors_find s root n target hT d ci ai b h

private theorem dcu_tuple_selectors_find_not_false
    (s : native_String) (root : DatatypeDecl) (n q : native_Nat) (k : Nat) :
    ∀ (T : Term) (b c : Int), sizeOf T < k ->
      __eo_is_neg
          (__eo_list_find_rec (__tuple_get_selectors_rec T (Term.Numeral b))
            (Term.DtSel s root n q) (Term.Numeral c)) ≠
        Term.Boolean false := by
  induction k with
  | zero => intro T b c hk; omega
  | succ k ih =>
      intro T b c hk h
      by_cases hS : __tuple_get_selectors_rec T (Term.Numeral b) = Term.Stuck
      · rw [hS] at h
        simp [__eo_list_find_rec, __eo_is_neg] at h
      rcases tsp_get_selectors_rec_shape T _ hS with rfl | ⟨T1, T2, rfl⟩
      · have hNil :
            __tuple_get_selectors_rec (Term.UOp UserOp.UnitTuple) (Term.Numeral b) =
              Term.__eo_List_nil := by
          simp [__tuple_get_selectors_rec]
        rw [hNil, dcu_find_rec_nil _ _ (by simp)] at h
        simp [__eo_is_neg, native_zlt, SmtEval.native_zlt] at h
      · let ss' := __tuple_get_selectors_rec T2 (Term.Numeral (b + 1))
        have hSels :
            __tuple_get_selectors_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                (Term.Numeral b) =
              __eo_mk_apply
                (Term.Apply Term.__eo_List_cons
                  (Term.UOp1 UserOp1.tuple_select (Term.Numeral b))) ss' := by
          simp [__tuple_get_selectors_rec, __eo_add, native_zplus,
            SmtEval.native_zplus, ss']
        have hSsNe : ss' ≠ Term.Stuck := by
          intro h'
          apply hS
          rw [hSels, h']
          simp [__eo_mk_apply]
        rw [hSels, dcu_mk_apply_of_ne (by simp) hSsNe,
          dcu_find_rec_cons _ _ _ _ (by simp)] at h
        have hEqF :
            __eo_eq (Term.UOp1 UserOp1.tuple_select (Term.Numeral b))
                (Term.DtSel s root n q) = Term.Boolean false := by
          simp [__eo_eq, native_teq]
        rw [hEqF] at h
        simp [__eo_ite, native_ite, native_teq] at h
        exact ih T2 (b + 1) (c + 1) (by simp at hk; omega) h

private theorem dcu_requires_self {x z : Term} (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not, hx]

private theorem dcu_get_selectors_find_dtsel (T r : Term)
    (s : native_String) (root : DatatypeDecl) (n q : native_Nat)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons (__dt_get_selectors T r)
            (Term.DtSel s root n q)) =
        Term.Boolean false) :
    r = Term.DtCons s root n ∧ q < dcuK (__eo_dd_resolve s root) n ∧
      __eo_list_find Term.__eo_List_cons (__dt_get_selectors T r)
          (Term.DtSel s root n q) = Term.Numeral (q : Int) ∧
      __eo_list_len Term.__eo_List_cons (__dt_get_selectors T r) =
        Term.Numeral (dcuK (__eo_dd_resolve s root) n : Int) := by
  have hFindNe :
      __eo_list_find Term.__eo_List_cons (__dt_get_selectors T r)
          (Term.DtSel s root n q) ≠ Term.Stuck := by
    intro h
    rw [h] at hFind
    simp [__eo_is_neg] at hFind
  have hIsList :
      __eo_is_list Term.__eo_List_cons (__dt_get_selectors T r) =
        Term.Boolean true :=
    tsp_requires_eq _ _ _ hFindNe
  have hFindEq :
      __eo_list_find Term.__eo_List_cons (__dt_get_selectors T r)
          (Term.DtSel s root n q) =
        __eo_list_find_rec (__dt_get_selectors T r) (Term.DtSel s root n q)
          (Term.Numeral 0) := by
    simp only [__eo_list_find]
    rw [hIsList]
    exact dcu_requires_self (by simp)
  have hLenEq :
      __eo_list_len Term.__eo_List_cons (__dt_get_selectors T r) =
        __eo_list_len_rec (__dt_get_selectors T r) := by
    simp only [__eo_list_len]
    rw [hIsList]
    exact dcu_requires_self (by simp)
  rw [hFindEq] at hFind
  rw [hFindEq, hLenEq]
  have hCls :
      (∃ T1 T2, __dt_get_selectors T r =
          __tuple_get_selectors_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
            (Term.Numeral 0)) ∨
        __dt_get_selectors T r = Term.__eo_List_nil ∨
        __dt_get_selectors T r = Term.Stuck ∨
        __dt_get_selectors T r = __eo_dt_selectors r := by
    rw [__dt_get_selectors.eq_def]
    split
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hCls with ⟨T1, T2, hSs⟩ | hSs | hSs | hSs
  · rw [hSs] at hFind
    exact absurd hFind
      (dcu_tuple_selectors_find_not_false s root n q _ _ 0 0 (Nat.lt_succ_self _))
  · rw [hSs, dcu_find_rec_nil _ _ (by simp)] at hFind
    simp [__eo_is_neg, native_zlt, SmtEval.native_zlt] at hFind
  · rw [hSs] at hFind
    simp [__eo_list_find_rec, __eo_is_neg] at hFind
  · rw [hSs] at hFind ⊢
    by_cases hr : ∃ s' d' i', r = Term.DtCons s' d' i'
    · rcases hr with ⟨s', d', i', rfl⟩
      simp only [__eo_dt_selectors] at hFind ⊢
      rcases dcu_cons_selectors_find s' d' i' (Term.DtSel s root n q) (by simp)
          (__eo_dd_resolve s' d') i' 0 0 hFind with
        ⟨q', hq', _, hLt, hFindQ⟩
      injection hq' with h1 h2 h3 h4
      subst h1
      subst h2
      subst h3
      subst h4
      have hSelsNe :
          __eo_datatype_cons_selectors_rec s root n (__eo_dd_resolve s root) n 0 ≠
            Term.Stuck := by
        intro h
        rw [h] at hFind
        simp [__eo_list_find_rec, __eo_is_neg] at hFind
      refine ⟨rfl, by simpa using hLt, by rw [hFindQ]; simp, ?_⟩
      exact dcu_cons_selectors_len s root n _ n 0 hSelsNe
    · exfalso
      have hSt : __eo_dt_selectors r = Term.Stuck := by
        rw [__eo_dt_selectors.eq_def]
        split
        · rfl
        · exact absurd ⟨_, _, _, rfl⟩ hr
        · simp [__eo_dt_selectors_main]
      rw [hSt] at hFind
      simp [__eo_list_find_rec, __eo_is_neg] at hFind

private theorem dcu_eoDtcNumSelsResolve (dd : DatatypeDecl) :
    ∀ c : DatatypeCons,
      __smtx_dtc_num_sels (__eo_to_smt_datatype_cons (__eo_dtc_resolve c dd)) =
        __smtx_dtc_num_sels (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit => by
      simp [__eo_dtc_resolve, __eo_to_smt_datatype_cons, __smtx_dtc_num_sels]
  | DatatypeCons.cons T c => by
      cases T <;>
        simp [__eo_dtc_resolve, __eo_to_smt_datatype_cons,
          __smtx_dtc_num_sels, dcu_eoDtcNumSelsResolve dd c]

private theorem dcu_eoDtNumSelsResolve (dd : DatatypeDecl) :
    ∀ (d : Datatype) (i : Nat),
      __smtx_dt_num_sels (__eo_to_smt_datatype (__eo_dt_resolve d dd)) i =
        __smtx_dt_num_sels (__eo_to_smt_datatype d) i
  | Datatype.null, i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels]
  | Datatype.sum c d, 0 => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        dcu_eoDtcNumSelsResolve dd c]
  | Datatype.sum c d, Nat.succ i => by
      simp [__eo_dt_resolve, __eo_to_smt_datatype, __smtx_dt_num_sels,
        dcu_eoDtNumSelsResolve dd d i]

private theorem dcuK_eq_smt (s : native_String) (d0 : DatatypeDecl) (i : Nat) :
    dcuK (__eo_dd_resolve s d0) i =
      __smtx_dt_num_sels
        (__smtx_dd_lookup s (__eo_to_smt_datatype_decl d0)) i := by
  simp only [dcuK, __eo_dd_resolve]
  rw [dcu_eoDtNumSelsResolve, TranslationProofs.eo_to_smt_dd_lookup]

private theorem dcu_updater_typeof_none_of_not_dt_sel
    (sel t u : SmtTerm) :
    (∀ s d i j, sel ≠ SmtTerm.DtSel s d i j) ->
    __smtx_typeof (__eo_to_smt_updater sel t u) = SmtType.None := by
  intro hSel
  cases sel <;> simp [__eo_to_smt_updater]
  case DtSel s d i j =>
    exact False.elim (hSel s d i j rfl)

/-- Semantic core of the found-selector `update` case of
`dt-collapse-updater`. -/
theorem dt_collapse_updater_found_rel
    (M : SmtModel) (hM : model_wf M) (sel t a rhs : Term)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons
            (__dt_get_selectors_of_app (__eo_typeof t) t) sel) =
        Term.Boolean false)
    (hRhs :
      __dt_collapse_updater_rhs t a
          (__eo_add
            (__eo_add
              (__eo_list_len Term.__eo_List_cons
                (__dt_get_selectors_of_app (__eo_typeof t) t))
              (__eo_neg
                (__eo_list_find Term.__eo_List_cons
                  (__dt_get_selectors_of_app (__eo_typeof t) t) sel)))
            (Term.Numeral (-1 : native_Int))) = rhs)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a))
          rhs)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update sel) t) a)))
      (__smtx_model_eval M (__eo_to_smt rhs)) := by
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hBool
  have hLhsNN := hTypes.2
  have hRhsNN : __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
    rw [← hTypes.1]
    exact hLhsNN
  change
    __smtx_typeof
        (__eo_to_smt_updater (__eo_to_smt sel) (__eo_to_smt t) (__eo_to_smt a)) ≠
      SmtType.None at hLhsNN
  -- the selector is a datatype selector
  have hIsDtSel : ∃ s D i j, __eo_to_smt sel = SmtTerm.DtSel s D i j := by
    by_contra hNot
    apply hLhsNN
    exact dcu_updater_typeof_none_of_not_dt_sel _ _ _
      (by intro s D i j h; exact hNot ⟨s, D, i, j, h⟩)
  rcases hIsDtSel with ⟨s, D, i, j, hSelSmt⟩
  rcases TranslationProofs.eo_to_smt_eq_dt_sel_cases sel s D i j hSelSmt with
    ⟨d0, hD, hSelEq, hReserved⟩ | ⟨z0, hSelEq, _hz0⟩
  swap
  · subst sel
    change SmtTerm._at_purify (__eo_to_smt z0) = SmtTerm.DtSel s D i j at hSelSmt
    cases hSelSmt
  subst hSelEq
  subst hD
  let DD := __eo_to_smt_datatype_decl d0
  have hUpdNN :
      __smtx_typeof
          (__eo_to_smt_updater (SmtTerm.DtSel s DD i j) (__eo_to_smt t)
            (__eo_to_smt a)) ≠ SmtType.None := by
    simpa [hSelSmt] using hLhsNN
  have hIdx :
      native_zlt (native_nat_to_int j)
          (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s DD) i)) =
        true :=
    TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
      s DD i j (__eo_to_smt t) (__eo_to_smt a) hUpdNN
  have hIdxProp :
      native_nat_to_int j <
        native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s DD) i) := by
    apply of_decide_eq_true
    simpa [native_zlt, SmtEval.native_zlt] using hIdx
  let N := __smtx_dt_num_sels (__smtx_dd_lookup s DD) i
  let cond :=
    SmtTerm.Apply (SmtTerm.DtTester s DD i) (__eo_to_smt t)
  let recTerm :=
    __eo_to_smt_updater_rec (SmtTerm.DtSel s DD i j) N (__eo_to_smt t)
      (__eo_to_smt a) (SmtTerm.DtCons s DD i)
  have hUpdaterEq :
      __eo_to_smt_updater (SmtTerm.DtSel s DD i j) (__eo_to_smt t)
          (__eo_to_smt a) =
        SmtTerm.ite cond recTerm (__eo_to_smt t) := by
    simp [cond, recTerm, N, __eo_to_smt_updater, native_ite, hIdxProp, hIdx]
  have hIteNN : term_has_non_none_type (SmtTerm.ite cond recTerm (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    rw [← hUpdaterEq]
    exact hUpdNN
  rcases ite_args_of_non_none hIteNN with ⟨_T, hCond, _hThen, _hElse, _hTNN⟩
  have hTesterNN : term_has_non_none_type cond := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  have hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype s DD :=
    dt_tester_arg_datatype_of_non_none hTesterNN
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hTTy]
    simp
  have hRecNN : __smtx_typeof recTerm ≠ SmtType.None :=
    tsp_smtx_ite_then_non_none _ _ _ hIteNN
  -- EO side: the head of `t` and the selector position
  have hTyNe : __eo_typeof t ≠ Term.Stuck := by
    intro h
    rw [h] at hFind
    simp [__dt_get_selectors_of_app, __eo_list_find, __eo_is_list,
      __eo_requires, __eo_is_neg, native_ite, native_teq] at hFind
  rcases dcu_get_selectors_of_app_root (__eo_typeof t) hTyNe (sizeOf t + 1) t
      (by omega) with ⟨r, xs, hSp, hRNotApp, hSelsEq⟩
  rw [hSelsEq] at hFind hRhs
  rcases dcu_get_selectors_find_dtsel (__eo_typeof t) r s d0 i j hFind with
    ⟨hr, hjK, hFindEq, hLenEq⟩
  rw [hFindEq, hLenEq] at hRhs
  have hK := dcuK_eq_smt s d0 i
  have hIdxEq :
      __eo_add
          (__eo_add (Term.Numeral (dcuK (__eo_dd_resolve s d0) i : Int))
            (__eo_neg (Term.Numeral (j : Int))))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral ((dcuK (__eo_dd_resolve s d0) i : Int) - j - 1) := by
    simp only [__eo_add, __eo_neg, native_zplus, SmtEval.native_zplus,
      native_zneg, SmtEval.native_zneg]
    apply dcu_numeral_congr
    omega
  rw [hIdxEq] at hRhs
  have hRhsNe : rhs ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation rhs hRhsNN
  have haNe : a ≠ Term.Stuck := by
    intro h
    subst h
    apply hRhsNe
    rw [← hRhs]
    simp [__dt_collapse_updater_rhs]
  subst hr
  rcases dcu_collapse_rhs_spine a haNe hSp (by simp) hRNotApp _
      (by rw [hRhs]; exact hRhsNe) with ⟨hLo, hHi, hRhsSp⟩
  rw [hRhs] at hRhsSp
  -- evaluation of `t` and of `rhs`
  rcases dcu_spine_eval_components M hM s d0 i hReserved hSp rfl hTNN with
    ⟨hTHead, hTCount, hTArgs⟩
  rcases dcu_spine_eval_components M hM s d0 i hReserved hRhsSp rfl hRhsNN with
    ⟨hRHead, hRCount, hRArgs⟩
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Datatype s DD := by
    rw [smt_model_eval_preserves_type_of_non_none M hM _ hTNN, hTTy]
  have hTCount' :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hTHead hTEvalTy
  rw [dt_num_sels_resolve] at hTCount'
  have hLenN : xs.length = N := by
    rw [← hTCount]
    exact hTCount'
  have hKN : dcuK (__eo_dd_resolve s d0) i = N := hK
  have hPos : xs.length - 1 - ((dcuK (__eo_dd_resolve s d0) i : Int) - j - 1).toNat =
      j := by
    rw [hKN, hLenN]
    have : (j : Int) < N := by rw [← hKN]; exact_mod_cast hjK
    omega
  rw [hPos] at hRhsSp hRArgs hRCount
  -- evaluation of the left-hand side
  rcases tsp_updater_rec_eval_components M hM s DD i j N (__eo_to_smt t)
      (__eo_to_smt a) hRecNN with ⟨hUHead, hUCount, hUArgs⟩
  have hTester :
      __smtx_model_eval M cond = SmtValue.Boolean true := by
    simp [cond, DD, __smtx_model_eval, __smtx_model_eval_dt_tester, hTHead,
      native_veq]
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update
            (Term.DtSel s d0 i j)) t) a)) =
        __smtx_model_eval M recTerm := by
    change
      __smtx_model_eval M
          (__eo_to_smt_updater (__eo_to_smt (Term.DtSel s d0 i j))
            (__eo_to_smt t) (__eo_to_smt a)) = _
    rw [hSelSmt, hUpdaterEq, smtx_eval_ite_term_eq, hTester]
    simp [__smtx_model_eval_ite]
  rw [hLhsEval]
  have hValEq :
      __smtx_model_eval M recTerm = __smtx_model_eval M (__eo_to_smt rhs) := by
    apply vsm_apply_ext
    · rw [hUHead, hRHead]
    · rw [hUCount, hRCount, List.length_set, hLenN]
    · intro q hq
      rw [hUCount] at hq ⊢
      rw [hRCount, List.length_set, hLenN]
      have hqx : q < (xs.set j a).length := by
        rw [List.length_set, hLenN]
        exact hq
      have hget := List.getElem?_eq_getElem hqx
      have hRA := hRArgs q _ hget
      rw [List.length_set, hLenN] at hRA
      rw [hRA, hUArgs q hq]
      by_cases hqj : q = j
      · subst hqj
        simp [native_nateq, SmtEval.native_nateq, native_ite]
      · have hjq : j ≠ q := fun h => hqj h.symm
        simp [native_nateq, SmtEval.native_nateq, native_ite, hjq,
          List.getElem_set_ne hjq]
        have hxq : q < xs.length := by rw [hLenN]; exact hq
        have hTA := hTArgs q _ (List.getElem?_eq_getElem hxq)
        rw [hLenN] at hTA
        rw [← hTA]
        simp [__smtx_model_eval, __smtx_model_eval_dt_sel, hTHead, native_veq,
          native_ite, N, DD]
  rw [hValEq]
  exact RuleProofs.smt_value_rel_refl _
