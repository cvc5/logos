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
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [TranslationProofs.smtx_typeof_none]

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem eq_true_of_requires_true_not_stuck {x B : Term} :
    __eo_requires x (Term.Boolean true) B ≠ Term.Stuck ->
    x = Term.Boolean true := by
  intro hReq
  cases x <;> cases B <;>
    simp [__eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] at hReq ⊢
  all_goals assumption

private theorem eo_and_eq_true_cases_local (x y : Term) :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_and, __eo_requires, native_ite,
    native_teq, native_and, native_not, SmtEval.native_not] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

private theorem eo_eq_eq_true_of_eq_local {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX _hY
  subst y
  simp [__eo_eq, native_teq]

private theorem eo_eq_eq_false_of_ne_local {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  have hNeYX : y ≠ x := by
    intro h
    exact hNe h.symm
  simp [__eo_eq, native_teq, hNeYX]

private def quant_var_lhs (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F

private def quant_var_rhs (y F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) F

private def quant_var_formula (x y F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (quant_var_lhs x F))
    (quant_var_rhs y F)

private abbrev QuantBinder := native_String × SmtType

private def smtExistsOfBinders : List QuantBinder -> SmtTerm -> SmtTerm
  | [], body => body
  | b :: bs, body => SmtTerm.exists b.1 b.2 (smtExistsOfBinders bs body)

private theorem native_model_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w =
      native_model_push M s T w := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else
                (if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then v
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else values k)
            nativeFuns
      congr
      funext k
      by_cases hk : k = ({ isVar := true, name := s, ty := T } : SmtModelKey)
      · simp [hk]
      · simp [hk]

private theorem native_model_push_comm
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hNe :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push (native_model_push M s2 T2 v2) s1 T1 v1 := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else
                (if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
              else
                (if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
                else values k))
            nativeFuns
      congr
      funext k
      by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
      · subst k
        by_cases h2 :
            ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
              { isVar := true, name := s2, ty := T2 }
        · exact False.elim (hNe h2)
        · simp [h2]
      · by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
        · subst k
          have h21 :
              ¬ ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) =
                { isVar := true, name := s1, ty := T1 } := by
            intro h
            exact hNe h.symm
          simp [h21]
        · simp [h1, h2]

private theorem smtExistsOfBinders_cons_congr
    (M : SmtModel) (b : QuantBinder) (t u : SmtTerm) :
    (∀ M2, __smtx_model_eval M2 t = __smtx_model_eval M2 u) ->
    __smtx_model_eval M (smtExistsOfBinders [b] t) =
      __smtx_model_eval M (smtExistsOfBinders [b] u) := by
  rcases b with ⟨s, T⟩
  intro hEval
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) t =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) u =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hT⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hT⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hU⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hU⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, hPropEq]

private theorem smtExistsOfBinders_swap
    (M : SmtModel) (b1 b2 : QuantBinder) (tail : List QuantBinder)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b1 :: b2 :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b2 :: b1 :: tail) body) := by
  rcases b1 with ⟨s1, T1⟩
  rcases b2 with ⟨s2, T2⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T1 ∧
        __smtx_value_canonical v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T2 ∧
            __smtx_value_canonical v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s1 T1 v1) s2 T2 v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v2 : SmtValue,
      __smtx_typeof_value v2 = T2 ∧
        __smtx_value_canonical v2 = true ∧
        ∃ v1 : SmtValue,
          __smtx_typeof_value v1 = T1 ∧
            __smtx_value_canonical v1 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s2 T2 v2) s1 T1 v1)
                rest =
              SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    by_cases hKey :
        ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
          { isVar := true, name := s2, ty := T2 }
    · cases hKey
      constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
    · constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        refine ⟨v2, hv2, hc2, v1, hv1, hc1, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
      · intro hSat
        rcases hSat with ⟨v2, hv2, hc2, v1, hv1, hc1, hEval⟩
        refine ⟨v1, hv1, hc1, v2, hv2, hc2, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_eval_perm
    (body : SmtTerm) {xs ys : List QuantBinder}
    (hperm : xs.Perm ys) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders xs body) =
      __smtx_model_eval M (smtExistsOfBinders ys body) := by
  induction hperm with
  | nil =>
      intro M
      rfl
  | cons b _h ih =>
      intro M
      exact smtExistsOfBinders_cons_congr M b
        (smtExistsOfBinders _ body) (smtExistsOfBinders _ body) ih
  | swap b1 b2 tail =>
      intro M
      exact (smtExistsOfBinders_swap M b1 b2 tail body).symm
  | trans _h1 _h2 ih1 ih2 =>
      intro M
      exact (ih1 M).trans (ih2 M)

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private theorem eoListOfTerms_ne_stuck (xs : List Term) :
    eoListOfTerms xs ≠ Term.Stuck := by
  cases xs <;> simp [eoListOfTerms]

private theorem eoListOfTerms_is_list_true (xs : List Term) :
    __eo_is_list Term.__eo_List_cons (eoListOfTerms xs) = Term.Boolean true := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_ok, __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons _ xs ih =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
      simpa [__eo_is_list, eoListOfTerms_ne_stuck xs] using ih

private theorem eo_get_elements_rec_eoListOfTerms (xs : List Term) :
    __eo_get_elements_rec (eoListOfTerms xs) = eoListOfTerms xs := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_get_elements_rec]
  | cons _ xs ih =>
      simp [eoListOfTerms, __eo_get_elements_rec, __eo_mk_apply,
        eoListOfTerms_ne_stuck, ih]

private theorem eo_list_erase_rec_eoListOfTerms_eq
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_list_erase_rec (eoListOfTerms xs) e =
      eoListOfTerms (xs.erase e) := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_list_erase_rec]
  | cons x xs ih =>
      have hx : x ≠ Term.Stuck := hxs x (by simp)
      have htail : ∀ t ∈ xs, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (by simp [ht])
      by_cases hxe : x = e
      · subst e
        simp [eoListOfTerms, __eo_list_erase_rec, __eo_ite,
          eo_eq_eq_true_of_eq_local rfl hx hx, List.erase_cons_head,
          native_ite, native_teq]
      · have hEqTerm : __eo_eq x e = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local hxe hx he
        have hTailEq := ih htail
        have hBeq : ¬(x == e) = true := by
          simp [hxe]
        rw [List.erase_cons_tail hBeq]
        simp [eoListOfTerms, __eo_list_erase_rec, __eo_ite, __eo_mk_apply,
          hEqTerm, hTailEq, eoListOfTerms_ne_stuck, native_ite, native_teq]

private theorem eo_list_erase_rec_eoList_mem_of_changed
    {xs : List Term} {e : Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (he : e ≠ Term.Stuck) :
    __eo_not (__eo_eq (__eo_list_erase_rec (eoListOfTerms xs) e)
        (eoListOfTerms xs)) = Term.Boolean true ->
    e ∈ xs := by
  intro hChanged
  by_cases hMem : e ∈ xs
  · exact hMem
  · have hEraseList : xs.erase e = xs := (List.erase_eq_self_iff).2 hMem
    have hEraseTerm := eo_list_erase_rec_eoListOfTerms_eq hxs he
    rw [hEraseList] at hEraseTerm
    have hEqTerm :
        __eo_eq (__eo_list_erase_rec (eoListOfTerms xs) e)
            (eoListOfTerms xs) = Term.Boolean true :=
      eo_eq_eq_true_of_eq_local hEraseTerm
        (by
          rw [hEraseTerm]
          exact eoListOfTerms_ne_stuck xs)
        (eoListOfTerms_ne_stuck xs)
    simp [__eo_not, hEqTerm, native_not] at hChanged

private theorem raw_minclude_rec_eq_not_flag_true
    {y z orig : Term} :
    y ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    orig ≠ Term.Stuck ->
    __eo_list_minclude_rec y z (__eo_not (__eo_eq y orig)) =
      Term.Boolean true ->
    __eo_not (__eo_eq y orig) = Term.Boolean true := by
  intro hY hZ hOrig hIncl
  by_cases hEq : y = orig
  · have hEqTerm : __eo_eq y orig = Term.Boolean true :=
      eo_eq_eq_true_of_eq_local hEq hY hOrig
    have hFlag :
        __eo_not (__eo_eq y orig) = Term.Boolean false := by
      simp [__eo_not, hEqTerm, native_not]
    rw [hFlag] at hIncl
    cases y <;> cases z <;> simp [__eo_list_minclude_rec] at hIncl hY hZ
  · have hEqTerm : __eo_eq y orig = Term.Boolean false :=
      eo_eq_eq_false_of_ne_local hEq hY hOrig
    simp [__eo_not, hEqTerm, native_not]

private theorem raw_minclude_rec_eoList_perm_append
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_minclude_rec (eoListOfTerms xs) (eoListOfTerms ys)
        (Term.Boolean true) = Term.Boolean true ->
    ∃ zs, xs.Perm (ys ++ zs) := by
  induction ys generalizing xs with
  | nil =>
      intro _hIncl
      exact ⟨xs, by simp⟩
  | cons y ys ih =>
      intro hIncl
      have hy : y ≠ Term.Stuck := hys y (by simp)
      have hysTail : ∀ t ∈ ys, t ≠ Term.Stuck := by
        intro t ht
        exact hys t (by simp [ht])
      let erased := __eo_list_erase_rec (eoListOfTerms xs) y
      have hInclRaw :
          __eo_list_minclude_rec erased (eoListOfTerms ys)
              (__eo_not (__eo_eq erased (eoListOfTerms xs))) =
            Term.Boolean true := by
        simpa [eoListOfTerms, __eo_list_minclude_rec, erased,
          eoListOfTerms_ne_stuck] using hIncl
      have hEraseEq : erased = eoListOfTerms (xs.erase y) := by
        simpa [erased] using eo_list_erase_rec_eoListOfTerms_eq hxs hy
      have hErasedNe : erased ≠ Term.Stuck := by
        rw [hEraseEq]
        exact eoListOfTerms_ne_stuck (xs.erase y)
      have hFlag :
          __eo_not (__eo_eq erased (eoListOfTerms xs)) = Term.Boolean true :=
        raw_minclude_rec_eq_not_flag_true hErasedNe
          (eoListOfTerms_ne_stuck ys) (eoListOfTerms_ne_stuck xs) hInclRaw
      have hTailIncl :
          __eo_list_minclude_rec (eoListOfTerms (xs.erase y))
              (eoListOfTerms ys) (Term.Boolean true) = Term.Boolean true := by
        rw [hFlag] at hInclRaw
        simpa [hEraseEq] using hInclRaw
      have hyMem : y ∈ xs := by
        apply eo_list_erase_rec_eoList_mem_of_changed hxs hy
        simpa [erased] using hFlag
      have hEraseNonStuck : ∀ t ∈ xs.erase y, t ≠ Term.Stuck := by
        intro t ht
        exact hxs t (List.mem_of_mem_erase ht)
      rcases ih hEraseNonStuck hysTail hTailIncl with ⟨zs, hPermTail⟩
      exact ⟨zs,
        (List.perm_cons_erase hyMem).trans (List.Perm.cons y hPermTail)⟩

private def IsQuantVarTerm : Term -> Prop
  | Term.Var (Term.String _) _ => True
  | _ => False

private def quantTermBinder : Term -> QuantBinder
  | Term.Var (Term.String s) T => (s, __eo_to_smt_type T)
  | _ => (native_string_lit "", SmtType.None)

private theorem quantVarTerm_ne_stuck {t : Term} :
    IsQuantVarTerm t -> t ≠ Term.Stuck := by
  intro h
  cases t <;> simp [IsQuantVarTerm] at h ⊢

private theorem eo_to_smt_exists_bool_as_eoList
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ ts, xs = eoListOfTerms ts ∧ ∀ t ∈ ts, IsQuantVarTerm t := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    exact ⟨[], rfl, by simp⟩
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
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) =
                SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            rcases eo_to_smt_exists_bool_as_eoList a body hSub with
              ⟨ts, hTail, hAllTail⟩
            refine ⟨Term.Var (Term.String s) T :: ts, ?_, ?_⟩
            · simp [eoListOfTerms, hTail]
            · intro t ht
              simp at ht
              rcases ht with ht | ht
              · subst t
                simp [IsQuantVarTerm]
              · exact hAllTail t ht
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

private theorem eo_to_smt_exists_eoListOfTerms_binders
    (xs : List Term) (body : SmtTerm)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __eo_to_smt_exists (eoListOfTerms xs) body =
      smtExistsOfBinders (xs.map quantTermBinder) body := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, smtExistsOfBinders]
  | cons x xs ih =>
      have hx : IsQuantVarTerm x := hxs x (by simp)
      have htail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hxs t (by simp [ht])
      cases x <;> simp [IsQuantVarTerm] at hx
      case Var name T =>
        cases name <;> simp at hx
        case String s =>
          simp [eoListOfTerms, smtExistsOfBinders, quantTermBinder,
            ih htail]

private theorem term_lists_perm_of_list_meq
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, t ≠ Term.Stuck)
    (hys : ∀ t ∈ ys, t ≠ Term.Stuck) :
    __eo_list_meq Term.__eo_List_cons (eoListOfTerms xs) (eoListOfTerms ys) =
      Term.Boolean true ->
    xs.Perm ys := by
  intro hMeq
  have hAnd :
      __eo_and
          (__eo_list_minclude_rec (eoListOfTerms xs) (eoListOfTerms ys)
            (Term.Boolean true))
          (__eo_list_minclude_rec (eoListOfTerms ys) (eoListOfTerms xs)
            (Term.Boolean true)) =
        Term.Boolean true := by
    simpa [__eo_list_meq, eoListOfTerms_is_list_true,
      eo_get_elements_rec_eoListOfTerms, __eo_requires, native_ite,
      native_teq, native_not, SmtEval.native_not] using hMeq
  have hBoth :=
    eo_and_eq_true_cases_local
      (__eo_list_minclude_rec (eoListOfTerms xs) (eoListOfTerms ys)
        (Term.Boolean true))
      (__eo_list_minclude_rec (eoListOfTerms ys) (eoListOfTerms xs)
        (Term.Boolean true)) hAnd
  rcases raw_minclude_rec_eoList_perm_append hxs hys hBoth.1 with
    ⟨zs, hPermXY⟩
  rcases raw_minclude_rec_eoList_perm_append hys hxs hBoth.2 with
    ⟨ws, hPermYX⟩
  have hLenXY := hPermXY.length_eq
  have hLenYX := hPermYX.length_eq
  simp [List.length_append] at hLenXY hLenYX
  have hZLen : zs.length = 0 := by
    omega
  have hZ : zs = [] := List.eq_nil_of_length_eq_zero hZLen
  simpa [hZ] using hPermXY

private theorem quant_var_forall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (quant_var_lhs x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  unfold quant_var_lhs
  change __smtx_typeof SmtTerm.None = SmtType.None
  simp [TranslationProofs.smtx_typeof_none]

private theorem quant_var_rhs_non_nil_of_non_none
    (y F : Term) :
    __smtx_typeof (__eo_to_smt (quant_var_rhs y F)) ≠ SmtType.None ->
    y ≠ Term.__eo_List_nil := by
  intro hNN hy
  subst y
  apply hNN
  unfold quant_var_rhs
  change __smtx_typeof SmtTerm.None = SmtType.None
  simp [TranslationProofs.smtx_typeof_none]

private theorem smtx_model_eval_forall_eoList_perm
    (M : SmtModel) (F : Term)
    {xs ys : List Term}
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t)
    (hys : ∀ t ∈ ys, IsQuantVarTerm t)
    (hperm : xs.Perm ys)
    (hxsNonempty : xs ≠ [])
    (hysNonempty : ys ≠ []) :
    __smtx_model_eval M (__eo_to_smt (quant_var_lhs (eoListOfTerms xs) F)) =
      __smtx_model_eval M (__eo_to_smt (quant_var_rhs (eoListOfTerms ys) F)) := by
  have hBindPerm : (xs.map quantTermBinder).Perm (ys.map quantTermBinder) :=
    hperm.map quantTermBinder
  have hExistsEval :=
    smtExistsOfBinders_eval_perm (SmtTerm.not (__eo_to_smt F)) hBindPerm M
  have hxNil : eoListOfTerms xs ≠ Term.__eo_List_nil := by
    intro h
    cases xs with
    | nil =>
        exact hxsNonempty rfl
    | cons _ _ =>
        simp [eoListOfTerms] at h
  have hyNil : eoListOfTerms ys ≠ Term.__eo_List_nil := by
    intro h
    cases ys with
    | nil =>
        exact hysNonempty rfl
    | cons _ _ =>
        simp [eoListOfTerms] at h
  unfold quant_var_lhs quant_var_rhs
  rw [eo_to_smt_forall_eq _ _ hxNil, eo_to_smt_forall_eq _ _ hyNil]
  rw [eo_to_smt_exists_eoListOfTerms_binders xs
      (SmtTerm.not (__eo_to_smt F)) hxs]
  rw [eo_to_smt_exists_eoListOfTerms_binders ys
      (SmtTerm.not (__eo_to_smt F)) hys]
  simp [__smtx_model_eval, hExistsEval]

private theorem smtx_model_eval_quant_var_formula
    (M : SmtModel) (x y F : Term) :
    RuleProofs.eo_has_bool_type (quant_var_formula x y F) ->
    __eo_list_meq Term.__eo_List_cons x y = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt (quant_var_lhs x F)) =
      __smtx_model_eval M (__eo_to_smt (quant_var_rhs y F)) := by
  intro hBool hMeq
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (quant_var_lhs x F) (quant_var_rhs y F) hBool with
    ⟨hSameTy, hLhsNN⟩
  have hRhsNN :
      __smtx_typeof (__eo_to_smt (quant_var_rhs y F)) ≠ SmtType.None := by
    intro hRhsNone
    apply hLhsNN
    rw [hSameTy]
    exact hRhsNone
  have hxNonNil : x ≠ Term.__eo_List_nil :=
    quant_var_forall_non_nil_of_non_none x F hLhsNN
  have hyNonNil : y ≠ Term.__eo_List_nil :=
    quant_var_rhs_non_nil_of_non_none y F hRhsNN
  have hInnerXTy :
      __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hLhsNN' := hLhsNN
    unfold quant_var_lhs at hLhsNN'
    rw [eo_to_smt_forall_eq _ _ hxNonNil] at hLhsNN'
    exact smtx_typeof_not_arg_of_non_none _ hLhsNN'
  have hInnerYTy :
      __smtx_typeof (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hRhsNN' := hRhsNN
    unfold quant_var_rhs at hRhsNN'
    rw [eo_to_smt_forall_eq _ _ hyNonNil] at hRhsNN'
    exact smtx_typeof_not_arg_of_non_none _ hRhsNN'
  rcases eo_to_smt_exists_bool_as_eoList x (SmtTerm.not (__eo_to_smt F))
      hInnerXTy with
    ⟨xs, hxEq, hxsAll⟩
  rcases eo_to_smt_exists_bool_as_eoList y (SmtTerm.not (__eo_to_smt F))
      hInnerYTy with
    ⟨ys, hyEq, hysAll⟩
  have hxsNonempty : xs ≠ [] := by
    intro hNil
    apply hxNonNil
    rw [hxEq, hNil]
    rfl
  have hysNonempty : ys ≠ [] := by
    intro hNil
    apply hyNonNil
    rw [hyEq, hNil]
    rfl
  have hxsNonStuck : ∀ t ∈ xs, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hxsAll t ht)
  have hysNonStuck : ∀ t ∈ ys, t ≠ Term.Stuck := by
    intro t ht
    exact quantVarTerm_ne_stuck (hysAll t ht)
  have hPerm : xs.Perm ys :=
    term_lists_perm_of_list_meq hxsNonStuck hysNonStuck
      (by simpa [hxEq, hyEq] using hMeq)
  simpa [hxEq, hyEq] using
    smtx_model_eval_forall_eoList_perm M F hxsAll hysAll hPerm
      hxsNonempty hysNonempty

private theorem quant_var_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_var_reordering x1 ≠ Term.Stuck ->
    ∃ x y F,
      x1 = quant_var_formula x y F ∧
      __eo_prog_quant_var_reordering x1 = quant_var_formula x y F ∧
      __eo_list_meq Term.__eo_List_cons x y = Term.Boolean true := by
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
                  | Apply forallHead F =>
                      cases forallHead with
                      | Apply forallOp x =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  cases rhs with
                                  | Apply rhsForallHead F2 =>
                                      cases rhsForallHead with
                                      | Apply rhsForallOp y =>
                                          cases rhsForallOp with
                                          | UOp rhsOpForall =>
                                              cases rhsOpForall with
                                              | «forall» =>
                                                  have hReq :
                                                      __eo_requires (__eo_eq F F2)
                                                          (Term.Boolean true)
                                                          (__eo_requires
                                                            (__eo_list_meq
                                                              Term.__eo_List_cons x y)
                                                            (Term.Boolean true)
                                                            (quant_var_formula x y F)) ≠
                                                        Term.Stuck := by
                                                    simpa [quant_var_formula, quant_var_lhs,
                                                      quant_var_rhs,
                                                      __eo_prog_quant_var_reordering] using hProg
                                                  have hF2 : F2 = F :=
                                                    RuleProofs.eq_of_requires_eq_true_not_stuck
                                                      F F2
                                                      (__eo_requires
                                                        (__eo_list_meq
                                                          Term.__eo_List_cons x y)
                                                        (Term.Boolean true)
                                                        (quant_var_formula x y F)) hReq
                                                  subst F2
                                                  have hFF :
                                                      __eo_eq F F = Term.Boolean true :=
                                                    eq_true_of_requires_true_not_stuck
                                                      (by simpa using hReq)
                                                  have hInnerNe :
                                                      __eo_requires
                                                          (__eo_list_meq
                                                            Term.__eo_List_cons x y)
                                                          (Term.Boolean true)
                                                          (quant_var_formula x y F) ≠
                                                        Term.Stuck := by
                                                    intro hInner
                                                    rw [hInner] at hReq
                                                    simp [__eo_requires, hFF, native_ite,
                                                      native_teq, native_not,
                                                      SmtEval.native_not] at hReq
                                                  have hMeq :
                                                      __eo_list_meq Term.__eo_List_cons x y =
                                                        Term.Boolean true :=
                                                    eq_true_of_requires_true_not_stuck
                                                      hInnerNe
                                                  refine ⟨x, y, F, rfl, ?_, hMeq⟩
                                                  change __eo_prog_quant_var_reordering
                                                      (quant_var_formula x y F) =
                                                    quant_var_formula x y F
                                                  simp [quant_var_formula, quant_var_lhs,
                                                    quant_var_rhs,
                                                    __eo_prog_quant_var_reordering,
                                                    hFF, hMeq, __eo_requires, native_ite,
                                                    native_teq, native_not, SmtEval.native_not]
                                              | _ =>
                                                  simp [__eo_prog_quant_var_reordering] at hProg
                                          | _ =>
                                              simp [__eo_prog_quant_var_reordering] at hProg
                                      | _ =>
                                          simp [__eo_prog_quant_var_reordering] at hProg
                                  | _ =>
                                      simp [__eo_prog_quant_var_reordering] at hProg
                              | _ =>
                                  simp [__eo_prog_quant_var_reordering] at hProg
                          | _ =>
                              simp [__eo_prog_quant_var_reordering] at hProg
                      | _ =>
                          simp [__eo_prog_quant_var_reordering] at hProg
                  | _ =>
                      simp [__eo_prog_quant_var_reordering] at hProg
              | _ =>
                  simp [__eo_prog_quant_var_reordering] at hProg
          | _ =>
              simp [__eo_prog_quant_var_reordering] at hProg
      | _ =>
          simp [__eo_prog_quant_var_reordering] at hProg
  | _ =>
      simp [__eo_prog_quant_var_reordering] at hProg

public theorem cmd_step_quant_var_reordering_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_reordering args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_var_reordering args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_reordering args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.quant_var_reordering args premises ≠
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_var_reordering a1 ≠ Term.Stuck := by
                change __eo_prog_quant_var_reordering a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_var_shape_of_not_stuck a1 hProgQuant with
                ⟨x, y, F, ha1, hProgEq, hMeq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation (quant_var_formula x y F) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quant_var_formula x y F) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_var_reordering a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (quant_var_formula x y F) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quant_var_formula x y F) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_var_reordering a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (quant_var_lhs x F) (quant_var_rhs y F)
                · exact hFormulaBool
                · have hEvalEq :=
                    smtx_model_eval_quant_var_formula M x y F hFormulaBool hMeq
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt (quant_var_rhs y F)))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_var_reordering a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
