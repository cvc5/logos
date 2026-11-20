module

public import Cpc.Proofs.RuleSupport.SkolemizeSupport
import all Cpc.Proofs.RuleSupport.SkolemizeSupport
public import Cpc.Proofs.Translation.Lambda
import all Cpc.Proofs.Translation.Lambda

/-!
# Support for the `beta-reduce` rule

`beta-reduce` proves `(= a b)` where `$beta_reduce a @list.nil` is `b`. The
program walks down the application spine of `a`, collecting its arguments,
until it reaches the head `(lambda us body)`, and returns the simultaneous
substitution of the arguments for `us` in `body`.

A lambda applied to exactly as many arguments as it binds translates to the
parallel `let` of its body (`LamSpine.eo_to_smt_full`). The `let` evaluates
its body in the model that pushes each variable's value; with distinct keys,
that is the model `pushSubstModel` the substitution engine evaluates the body
in (`substitute_simul_eval`), only pushed in the opposite order.

Every other shape the program accepts gives a conclusion with no SMT
translation, which the rule's hypotheses exclude:
* fewer arguments than variables: the translation is a `let` around a `lam`,
  which has no type (`spine_args_ge_vars`);
* more arguments than variables: the translation's type is a proper part of
  the body's, while the substitution's type is the body's
  (`spine_over_applied`).
-/

public section

open Eo
open SmtEval
open Smtm
open TranslationProofs
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace BetaReduceRule

/-! ## EO lists as Lean lists -/

/-- The EO list of the terms `l` in front of the list `acc`. -/
@[expose] def eoListApp : List Term -> Term -> Term
  | [], acc => acc
  | a :: l, acc => Term.Apply (Term.Apply Term.__eo_List_cons a) (eoListApp l acc)

/-- What `__beta_reduce` accumulates: the arguments `r`, listed last first, in
application order in front of `acc`. -/
@[expose] def revAcc : List Term -> Term -> Term
  | [], acc => acc
  | a :: r, acc => revAcc r (Term.Apply (Term.Apply Term.__eo_List_cons a) acc)

theorem eoListApp_append (l1 l2 : List Term) (acc : Term) :
    eoListApp (l1 ++ l2) acc = eoListApp l1 (eoListApp l2 acc) := by
  induction l1 with
  | nil => rfl
  | cons a l ih => simp [eoListApp, ih]

theorem revAcc_eq (r : List Term) (acc : Term) :
    revAcc r acc = eoListApp r.reverse acc := by
  induction r generalizing acc with
  | nil => rfl
  | cons a r ih =>
      rw [revAcc, ih, List.reverse_cons, eoListApp_append]
      rfl

/-- The EO variable `s : T`. -/
@[expose] def mkVar (p : native_String × Term) : Term :=
  Term.Var (Term.String p.1) p.2

/-- The EO list of the variables `vs`. -/
@[expose] def eoVarList (vs : List (native_String × Term)) : Term :=
  eoListApp (vs.map mkVar) Term.__eo_List_nil

theorem eoVarList_cons (p : native_String × Term) (vs : List (native_String × Term)) :
    eoVarList (p :: vs) =
      Term.Apply (Term.Apply Term.__eo_List_cons (mkVar p)) (eoVarList vs) := rfl

theorem lamVars_exists :
    ∀ (us : Term) (n : Nat), lamVars us n = true ->
      ∃ vs : List (native_String × Term), vs.length = n ∧ us = eoVarList vs
  | Term.__eo_List_nil, 0, _ => ⟨[], rfl, rfl⟩
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) us, n + 1, h => by
      obtain ⟨vs, hlen, rfl⟩ := lamVars_exists us n h
      exact ⟨(s, T) :: vs, by simp [hlen], rfl⟩
  | Term.__eo_List_nil, _ + 1, h => by cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) _)) _, 0, h => by
      cases h

theorem lamVars_eoVarList (vs : List (native_String × Term)) :
    lamVars (eoVarList vs) vs.length = true := by
  induction vs with
  | nil => rfl
  | cons p vs ih => exact ih

theorem eoVarEnv_eoVarList (vs : List (native_String × Term)) :
    EoVarEnv (eoVarList vs) vs := by
  induction vs with
  | nil => exact EoVarEnv.nil
  | cons p vs ih => exact EoVarEnv.cons ih

theorem lamNth_eoVarList :
    ∀ (vs : List (native_String × Term)) (i : Nat) (h : i < vs.length),
      lamNth (eoVarList vs) i = mkVar vs[i]
  | p :: vs, 0, _ => rfl
  | p :: vs, i + 1, h => lamNth_eoVarList vs i (by simp at h; omega)

/-- Where `us` begins with `m` variables, it begins with each fewer number. -/
theorem lamVarsPrefix_of_lamVars_le :
    ∀ (us : Term) (m k : Nat), lamVars us m = true -> k ≤ m ->
      lamVarsPrefix us k = true
  | _, _, 0, _, _ => by simp [lamVarsPrefix]
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) us,
      m + 1, k + 1, h, hk => by
      simp only [lamVarsPrefix]
      exact lamVarsPrefix_of_lamVars_le us m k h (by omega)
  | Term.__eo_List_nil, 0, _ + 1, _, hk => by omega
  | Term.__eo_List_nil, _ + 1, _ + 1, h, _ => by cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) _)) _,
      0, _ + 1, h, _ => by cases h

/-- A list of exactly `m` variables does not begin with more than `m`. -/
theorem lamVarsPrefix_false_of_lamVars_lt :
    ∀ (us : Term) (m k : Nat), lamVars us m = true -> m < k ->
      lamVarsPrefix us k = false
  | Term.__eo_List_nil, 0, k + 1, _, _ => by simp [lamVarsPrefix]
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) us,
      m + 1, k + 1, h, hk => by
      simp only [lamVarsPrefix]
      exact lamVarsPrefix_false_of_lamVars_lt us m k h (by omega)
  | _, _, 0, _, hk => by omega
  | Term.__eo_List_nil, _ + 1, _, h, _ => by cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) _)) _,
      0, _, h, _ => by cases h

/-- Dropping fewer than all the variables of a list of variables leaves a
variable in front. -/
theorem eoListDrop_cons_of_lamVars_lt :
    ∀ (us : Term) (m k : Nat), lamVars us m = true -> k < m ->
      ∃ s T vs, eoListDrop k us =
        Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) us,
      m + 1, 0, h, _ => ⟨s, T, us, rfl⟩
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) us,
      m + 1, k + 1, h, hk => by
      simp only [eoListDrop]
      exact eoListDrop_cons_of_lamVars_lt us m k h (by omega)
  | Term.__eo_List_nil, 0, _, _, hk => by omega
  | Term.__eo_List_nil, _ + 1, _, h, _ => by cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) _)) _,
      0, _, h, _ => by cases h

/-! ## Bindings and models -/

/-- The bindings of the variables to the arguments of `l`, in front of `bs`. -/
@[expose] def bindsApp : List ((native_String × Term) × Term) -> SmtBindings -> SmtBindings
  | [], bs => bs
  | ((s, T), a) :: l, bs => SmtBindings.cons s (__eo_to_smt_type T) (__eo_to_smt a) (bindsApp l bs)

theorem bindsApp_append (l1 l2 : List ((native_String × Term) × Term)) (bs : SmtBindings) :
    bindsApp (l1 ++ l2) bs = bindsApp l1 (bindsApp l2 bs) := by
  induction l1 with
  | nil => rfl
  | cons p l ih => obtain ⟨⟨s, T⟩, a⟩ := p; simp [bindsApp, ih]

/-- The bindings a spine makes, in terms of the variables it binds. -/
theorem lamBindings_eoVarList (vs : List (native_String × Term)) :
    ∀ (r : List Term) (bs : SmtBindings), r.length ≤ vs.length ->
      lamBindings (eoVarList vs) r bs = bindsApp ((vs.take r.length).zip r.reverse) bs
  | [], bs, _ => by simp [lamBindings, bindsApp]
  | a :: r, bs, hlen => by
      simp only [List.length_cons] at hlen
      have hlt : r.length < vs.length := by omega
      change lamBindings (eoVarList vs) r
          (lamBinding (lamNth (eoVarList vs) r.length) (__eo_to_smt a) bs) = _
      rw [lamBindings_eoVarList vs r _ (by omega), lamNth_eoVarList vs r.length hlt]
      rw [List.length_cons, List.take_succ_eq_append_getElem hlt, List.reverse_cons,
        List.zip_append (by simp; omega), bindsApp_append]
      rfl

/-- Pushing the values of a list of keyed values, first first. -/
@[expose] def pushL (N : SmtModel) : List (native_String × SmtType × SmtValue) -> SmtModel
  | [] => N
  | (s, T, v) :: l => pushL (native_model_push N s T v) l

theorem pushL_append (N : SmtModel) (l1 l2 : List (native_String × SmtType × SmtValue)) :
    pushL N (l1 ++ l2) = pushL (pushL N l1) l2 := by
  induction l1 generalizing N with
  | nil => rfl
  | cons p l ih => obtain ⟨s, T, v⟩ := p; simp [pushL, ih]

/-- The keyed values a list of bindings evaluates to in `M`. -/
@[expose] def evalBinds (M : SmtModel) (l : List ((native_String × Term) × Term)) :
    List (native_String × SmtType × SmtValue) :=
  l.map (fun p => (p.1.1, __eo_to_smt_type p.1.2, __smtx_model_eval M (__eo_to_smt p.2)))

theorem push_bindings_bindsApp (M : SmtModel) :
    ∀ (N : SmtModel) (l : List ((native_String × Term) × Term)) (bs : SmtBindings),
      __smtx_model_eval.push_bindings M N (bindsApp l bs) =
        __smtx_model_eval.push_bindings M (pushL N (evalBinds M l)) bs
  | N, [], bs => rfl
  | N, ((s, T), a) :: l, bs => by
      rw [bindsApp, model_push_bindings_cons, push_bindings_bindsApp M _ l bs]
      rfl

theorem pushSubstModel_eoVarList (M : SmtModel) :
    ∀ (vs : List (native_String × Term)) (args : List Term) (tail : Term),
      vs.length = args.length ->
      InstantiateRule.pushSubstModel M (eoVarList vs) (eoListApp args tail) =
        pushL M (evalBinds M (vs.zip args)).reverse
  | [], [], tail, _ => by
      cases tail <;> rfl
  | (s, T) :: vs, a :: args, tail, hlen => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      change native_model_push
          (InstantiateRule.pushSubstModel M (eoVarList vs) (eoListApp args tail)) s
          (__eo_to_smt_type T) (__smtx_model_eval M (__eo_to_smt a)) = _
      rw [pushSubstModel_eoVarList M vs args tail hlen]
      simp [evalBinds, List.zip_cons_cons, List.map_cons, List.reverse_cons, pushL_append, pushL]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- The model key of a keyed value. -/
@[expose] def keyOf (p : native_String × SmtType × SmtValue) : SmtModelKey :=
  { isVar := true, name := p.1, ty := p.2.1 }

theorem native_model_push_comm
    (M : SmtModel) (s1 : native_String) (T1 : SmtType) (v1 : SmtValue)
    (s2 : native_String) (T2 : SmtType) (v2 : SmtValue)
    (h : ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
      { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push (native_model_push M s2 T2 v2) s1 T1 v1 := by
  simp only [native_model_push]
  congr 1
  funext k
  by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
  · rw [ite_eq_left h2, ite_eq_right (by rw [h2]; exact fun hc => h hc.symm), ite_eq_left h2]
  · rw [ite_eq_right h2]
    by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2]

/-- A push commutes past pushes of other keys. -/
theorem pushL_push_comm (N : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    ∀ (l : List (native_String × SmtType × SmtValue)),
      (∀ q ∈ l, keyOf q ≠ { isVar := true, name := s, ty := T }) ->
      pushL (native_model_push N s T v) l = native_model_push (pushL N l) s T v
  | [], _ => rfl
  | (s', T', v') :: l, h => by
      simp only [pushL]
      rw [native_model_push_comm N s T v s' T' v'
        (fun hk => h (s', T', v') List.mem_cons_self hk.symm)]
      exact pushL_push_comm _ s T v l (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Pushing keyed values with distinct keys does not depend on their order. -/
theorem pushL_reverse_of_distinct (N : SmtModel) :
    ∀ (l : List (native_String × SmtType × SmtValue)),
      SkolemizeRule.DistinctList (l.map keyOf) ->
      pushL N l.reverse = pushL N l
  | [], _ => rfl
  | (s, T, v) :: l, h => by
      cases h with
      | cons hnot htail =>
          rw [List.reverse_cons, pushL_append, pushL_reverse_of_distinct N l htail]
          simp only [pushL]
          rw [pushL_push_comm N s T v l]
          · rfl
          · intro q hq hk
            exact hnot (List.mem_map.2 ⟨q, hq, hk⟩)

/-! ## Lists of typed bindings -/

theorem bindsApp_mem :
    ∀ (l : List ((native_String × Term) × Term)) (bs : SmtBindings),
      ∀ p ∈ l, SmtBindings.Mem (bindsApp l bs) p.1.1 (__eo_to_smt_type p.1.2) (__eo_to_smt p.2)
  | [], _, p, hp => absurd hp List.not_mem_nil
  | ((s, T), a) :: l, bs, p, hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact SmtBindings.Mem.head _ _ _ _
      · exact SmtBindings.Mem.tail _ _ _ (bindsApp_mem l bs p hp)

private theorem smtx_type_wf_none : __smtx_type_wf SmtType.None = false := by
  decide +kernel

theorem actuals_of_typed (tail : Term) :
    ∀ (vs : List (native_String × Term)) (args : List Term),
      vs.length = args.length ->
      (∀ p ∈ vs.zip args, __smtx_typeof (__eo_to_smt p.2) = __eo_to_smt_type p.1.2 ∧
        __smtx_type_wf (__eo_to_smt_type p.1.2) = true) ->
      SubstActualsHaveSmtTypes (eoVarList vs) (eoListApp args tail)
  | [], args, _, _ => SubstActualsHaveSmtTypes.nil _
  | (s, T) :: vs, a :: args, hlen, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨hTy, hWf⟩ := h ((s, T), a) (by simp)
      have hTrans : RuleProofs.eo_has_smt_translation a := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hTy]
        intro hNone
        rw [hNone, smtx_type_wf_none] at hWf
        cases hWf
      exact SubstActualsHaveSmtTypes.cons hWf hTrans hTy
        (actuals_of_typed tail vs args hlen (fun p hp => h p (by simp [hp])))
  | _ :: _, [], h, _ => by simp at h

theorem eoListApp_all_translations :
    ∀ (args : List Term), (∀ a ∈ args, __smtx_typeof (__eo_to_smt a) ≠ SmtType.None) ->
      EoListAllHaveSmtTranslation (eoListApp args Term.__eo_List_nil)
  | [], _ => trivial
  | a :: args, h =>
      ⟨h a List.mem_cons_self,
        eoListApp_all_translations args (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))⟩

theorem distinctList_map {α β : Type} (g : α -> β) :
    ∀ (l : List α), SkolemizeRule.DistinctList l ->
      (∀ x ∈ l, ∀ y ∈ l, g x = g y -> x = y) ->
      SkolemizeRule.DistinctList (l.map g)
  | [], _, _ => SkolemizeRule.DistinctList.nil
  | x :: l, SkolemizeRule.DistinctList.cons hx hl, hinj => by
      refine SkolemizeRule.DistinctList.cons ?_ (distinctList_map g l hl
        (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)))
      intro hmem
      obtain ⟨y, hy, hgy⟩ := List.mem_map.1 hmem
      have := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hgy
      subst this
      exact hx hy

/-- Distinct EO variables of well-formed types have distinct model keys. -/
theorem distinct_keys (M : SmtModel) (vs : List (native_String × Term)) (args : List Term)
    (hlen : vs.length = args.length)
    (hDistinct : SkolemizeRule.DistinctList vs)
    (hWf : ∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) :
    SkolemizeRule.DistinctList ((evalBinds M (vs.zip args)).map keyOf) := by
  have hkeys : (evalBinds M (vs.zip args)).map keyOf =
      vs.map (fun p => ({ isVar := true, name := p.1, ty := __eo_to_smt_type p.2 } : SmtModelKey)) := by
    have : (evalBinds M (vs.zip args)).map keyOf =
        ((vs.zip args).map Prod.fst).map
          (fun p => ({ isVar := true, name := p.1, ty := __eo_to_smt_type p.2 } : SmtModelKey)) := by
      simp [evalBinds, keyOf, List.map_map, Function.comp_def]
    rw [this, List.map_fst_zip (by omega)]
  rw [hkeys]
  refine distinctList_map _ vs hDistinct ?_
  rintro ⟨s, T⟩ hx ⟨s', T'⟩ hy hk
  simp only [SmtModelKey.mk.injEq, true_and] at hk
  obtain ⟨rfl, hT⟩ := hk
  have hTT : T = T' :=
    TranslationProofs.eo_to_smt_type_injective_of_wf rfl hT.symm (hWf _ hx)
  rw [hTT]

/-! ## `__beta_reduce` along a spine -/

theorem lamT_ne_lambda_apply (us body xs : Term) :
    Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body ≠
      Term.Apply (Term.UOp UserOp.lambda) xs := by
  intro h
  injection h with h1
  cases h1

/-- A spine is not the lambda symbol applied to its variable list alone. -/
theorem spine_ne_lambda_apply {f us body : Term} {r : List Term} (h : LamSpine f us body r)
    (xs : Term) : f ≠ Term.Apply (Term.UOp UserOp.lambda) xs := by
  cases h with
  | lam => exact lamT_ne_lambda_apply _ _ _
  | app a hf =>
      intro he
      injection he with he
      obtain ⟨g, c, b, rfl⟩ := hf.shape
      cases he

theorem beta_reduce_lam (us body ss : Term) (hss : ss ≠ Term.Stuck) :
    __beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body) ss =
      __eo_requires (__eo_eq (__eo_list_setof Term.__eo_List_cons us) us) (Term.Boolean true)
        (__substitute_simul_rec (Term.Boolean false) body us ss Term.__eo_List_nil) := by
  cases ss <;> first | exact absurd rfl hss | rfl

theorem beta_reduce_app (f a acc : Term) (hacc : acc ≠ Term.Stuck)
    (hnil : acc ≠ Term.__eo_List_nil)
    (hf : ∀ xs, f ≠ Term.Apply (Term.UOp UserOp.lambda) xs) :
    __beta_reduce (Term.Apply f a) acc =
      __beta_reduce f (Term.Apply (Term.Apply Term.__eo_List_cons a) acc) := by
  unfold __beta_reduce
  split
  · exact absurd rfl hacc
  · exact absurd rfl hnil
  · rename_i xs t _
    exact absurd rfl (hf xs)
  · rfl
  · rename_i hne _
    exact absurd rfl (hne f a)

theorem beta_reduce_app_nil (f a : Term)
    (hf : ∀ xs, f ≠ Term.Apply (Term.UOp UserOp.lambda) xs)
    (hf1 : ∀ x xs t, f ≠ Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
      (Term.Apply (Term.Apply Term.__eo_List_cons x) xs)) t) :
    __beta_reduce (Term.Apply f a) Term.__eo_List_nil =
      __beta_reduce f (Term.Apply (Term.Apply Term.__eo_List_cons a) Term.__eo_List_nil) := by
  unfold __beta_reduce
  split
  · rename_i h; cases h
  · rename_i x xs t _
    exact absurd rfl (hf1 x xs t)
  · rename_i xs t _
    exact absurd rfl (hf xs)
  · rfl
  · rename_i hne _
    exact absurd rfl (hne f a)

theorem beta_reduce_app_lam1 (x body a : Term) :
    __beta_reduce
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
          (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)) body) a)
        Term.__eo_List_nil =
      __beta_reduce
        (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
          (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)) body)
        (Term.Apply (Term.Apply Term.__eo_List_cons a) Term.__eo_List_nil) := by
  rw [beta_reduce_lam _ _ _ (by intro h; cases h)]
  simp [__beta_reduce, __eo_ite, __eo_eq, native_ite, native_teq]

theorem revAcc_ne_stuck (r : List Term) (acc : Term) (h : acc ≠ Term.Stuck) :
    revAcc r acc ≠ Term.Stuck := by
  rw [revAcc_eq]
  cases r.reverse with
  | nil => exact h
  | cons a l => intro he; cases he

/-- Along a spine, `__beta_reduce` collects the arguments. -/
theorem spine_beta_reduce {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    ∀ acc, acc ≠ Term.Stuck -> acc ≠ Term.__eo_List_nil ->
      __beta_reduce t acc =
        __beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body) (revAcc r acc) := by
  induction h with
  | lam => intros; rfl
  | @app f us body r a hf ih =>
      intro acc h1 h2
      rw [beta_reduce_app f a acc h1 h2 (spine_ne_lambda_apply hf)]
      exact ih _ (by intro h; cases h) (by intro h; cases h)

/-- From the top, a spine that applies its lambda to at least as many arguments
as it binds variables collects them all. -/
theorem spine_beta_reduce_nil {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    {m : Nat} (hv : lamVars us m = true) (hm : m ≤ r.length) :
    __beta_reduce t Term.__eo_List_nil =
      __beta_reduce (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body)
        (revAcc r Term.__eo_List_nil) := by
  cases h with
  | lam => rfl
  | @app f _ _ r a hf =>
      cases hf with
      | lam =>
          simp only [List.length_cons, List.length_nil] at hm
          by_cases hcons : ∃ x xs, us = Term.Apply (Term.Apply Term.__eo_List_cons x) xs
          · obtain ⟨x, xs, rfl⟩ := hcons
            have hm1 : m = 1 := by
              cases m with
              | zero => cases hv
              | succ m => omega
            subst hm1
            obtain ⟨vs, hlen, hvs⟩ := lamVars_exists _ 1 hv
            match vs, hlen, hvs with
            | [p], _, hvs =>
                injection hvs with hvs hxs
                injection hvs with _ hx
                subst hx hxs
                exact beta_reduce_app_lam1 _ body a
          · rw [beta_reduce_app_nil _ a (fun xs => lamT_ne_lambda_apply _ _ xs)]
            · rfl
            · intro x xs t he
              injection he with he
              injection he with _ he
              exact hcons ⟨x, xs, he⟩
      | @app g _ _ r' b hg =>
          rw [beta_reduce_app_nil _ a (spine_ne_lambda_apply (LamSpine.app b hg))]
          · exact spine_beta_reduce (LamSpine.app b hg) _ (by intro h; cases h)
              (by intro h; cases h)
          · intro x xs t he
            injection he with he
            exact spine_ne_lambda_apply hg _ he

/-- Only a spine is reduced. -/
theorem spine_of_beta_reduce_ne_stuck :
    ∀ (t acc : Term), __beta_reduce t acc ≠ Term.Stuck ->
      ∃ us body r, LamSpine t us body r
  | t, acc, h => by
      unfold __beta_reduce at h
      split at h
      · exact absurd rfl h
      · exact ⟨_, _, _, LamSpine.app _ (LamSpine.lam _ _)⟩
      · exact ⟨_, _, _, LamSpine.lam _ _⟩
      · rename_i f a ss _ _
        obtain ⟨us, body, r, hs⟩ := spine_of_beta_reduce_ne_stuck f _ h
        exact ⟨us, body, a :: r, LamSpine.app a hs⟩
      · exact absurd rfl h
termination_by t => sizeOf t

/-! ## Typed spines -/

/-- A typed spine applies its lambda to at least as many arguments as it binds
variables. -/
theorem spine_args_ge_vars {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    ∃ m, lamVars us m = true ∧ m ≤ r.length := by
  obtain ⟨⟨m, hv⟩, -, -⟩ := h.parts_typed_any hNN
  refine ⟨m, hv, ?_⟩
  by_contra hlt
  have hlt : r.length < m := by omega
  have hpre := lamVarsPrefix_of_lamVars_le us m r.length hv hlt.le
  obtain ⟨s, T, vs, hD⟩ := eoListDrop_cons_of_lamVars_lt us m r.length hv hlt
  rw [h.eo_to_smt_prefix.1 hpre, hD, curry_cons] at hNN
  exact hNN (smtx_typeof_pending ⟨_, _, _, _, rfl⟩)

theorem smtx_typeof_apply_result {F X A B : SmtType}
    (hF : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) (hX : X = A)
    (hNN : __smtx_typeof_apply F X ≠ SmtType.None) :
    __smtx_typeof_apply F X = B ∧ sizeOf B < sizeOf F := by
  subst hX
  rcases hF with rfl | rfl <;>
    refine ⟨?_, by simp; omega⟩ <;>
    simp [__smtx_typeof_apply, native_ite, native_Teq] at hNN ⊢ <;>
    first | exact hNN.2 | skip

/-- The variables a typed spine binds, the bindings of its arguments to them,
and, when it has more arguments than variables, a type that is a proper part of
its body's. -/
theorem spine_prefix_typed {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    ∀ m, lamVars us m = true -> m ≤ r.length ->
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      ∃ extra rm, r = extra ++ rm ∧ rm.length = m ∧
        term_has_non_none_type
          (SmtTerm.bind (lamBindings us rm SmtBindings.nil) (__eo_to_smt body)) ∧
        (m < r.length ->
          sizeOf (__smtx_typeof (__eo_to_smt t)) < sizeOf (__smtx_typeof (__eo_to_smt body))) := by
  induction h with
  | lam us body =>
      intro m hv hm hNN
      simp only [List.length_nil, Nat.le_zero] at hm
      subst hm
      refine ⟨[], [], rfl, rfl, ?_, fun h => absurd h (by simp)⟩
      have hus : us = Term.__eo_List_nil := by
        cases us <;> first | rfl | (cases hv) | skip
        all_goals (rename_i; first | cases hv | skip)
      subst hus
      exact hNN
  | @app f us body r a hf ih =>
      intro m hv hm hNN
      simp only [List.length_cons] at hm
      by_cases hmr : m = r.length + 1
      · refine ⟨[], a :: r, rfl, by simp [hmr], ?_, fun h => by simp at h; omega⟩
        have hv' : lamVars us (a :: r).length = true := by simpa [hmr] using hv
        have hfull := (LamSpine.app a hf).eo_to_smt_full hv'
        rw [hfull] at hNN
        exact hNN
      · have hmr' : m ≤ r.length := by omega
        have hnp : ¬ SmtPendingLam (__eo_to_smt f) := by
          intro hp
          have hpre := lamVarsPrefix_of_pending_app a hf hp
          rw [lamVarsPrefix_false_of_lamVars_lt us m _ hv (by simp; omega)] at hpre
          cases hpre
        have hApp : __eo_to_smt (Term.Apply f a) =
            SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a) := by
          rw [hf.eo_to_smt_app a, eo_to_smt_apply_of_not_pending _ hnp]
        have hTy : __smtx_typeof (__eo_to_smt (Term.Apply f a)) =
            __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f)) (__smtx_typeof (__eo_to_smt a)) := by
          rw [hApp]
          rcases hf.eo_to_smt_bind_or_apply with ⟨bs, b, hg⟩ | ⟨g, x, hg⟩ <;> rw [hg] <;> rfl
        have hNN' := hNN
        rw [hTy] at hNN'
        obtain ⟨A, B, hF, hX, hA, _⟩ := typeof_apply_non_none_cases hNN'
        obtain ⟨hRes, hSize⟩ := smtx_typeof_apply_result hF hX hNN'
        have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
          rcases hF with hF | hF <;> rw [hF] <;> simp
        obtain ⟨extra, rm, hr, hlen, htyped, hlt⟩ := ih m hv hmr' hFNN
        refine ⟨a :: extra, rm, by simp [hr], hlen, htyped, fun _ => ?_⟩
        have hfle : sizeOf (__smtx_typeof (__eo_to_smt f)) ≤
            sizeOf (__smtx_typeof (__eo_to_smt body)) := by
          by_cases hm' : m < r.length
          · exact (hlt hm').le
          · have hmeq : m = r.length := by omega
            subst hmeq
            have hfull := hf.eo_to_smt_full hv
            have hFNN' : term_has_non_none_type (__eo_to_smt f) := hFNN
            rw [hfull] at hFNN' ⊢
            rw [bind_term_typeof_of_non_none hFNN']
        rw [hTy, hRes]
        omega

/-! ## The rule -/

theorem eq_operands_same_smt_type (x y : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

/-- The semantic content of `beta-reduce`: where `(= a b)` has a translation and
`a` beta-reduces to `b`, the two evaluate alike. -/
theorem beta_reduce_eval (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hEqTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
    (hBeta : __beta_reduce a Term.__eo_List_nil = b) :
    __smtx_model_eval M (__eo_to_smt a) = __smtx_model_eval M (__eo_to_smt b) := by
  obtain ⟨hSame, hANN⟩ := eq_operands_same_smt_type a b hEqTrans
  have hBNN : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := hSame ▸ hANN
  have hbS : b ≠ Term.Stuck := by
    intro hb
    subst hb
    exact hBNN rfl
  obtain ⟨us, body, r, hs⟩ :=
    spine_of_beta_reduce_ne_stuck a Term.__eo_List_nil (by rw [hBeta]; exact hbS)
  obtain ⟨m, hv, hm⟩ := spine_args_ge_vars hs hANN
  have hb := spine_beta_reduce_nil hs hv hm
  rw [hBeta, beta_reduce_lam _ _ _ (revAcc_ne_stuck r _ (by intro h; cases h))] at hb
  have hReq : __eo_requires (__eo_eq (__eo_list_setof Term.__eo_List_cons us) us)
      (Term.Boolean true)
      (__substitute_simul_rec (Term.Boolean false) body us (revAcc r Term.__eo_List_nil)
        Term.__eo_List_nil) ≠ Term.Stuck := by
    rw [← hb]; exact hbS
  have hSet : __eo_list_setof Term.__eo_List_cons us = us :=
    support_eq_of_eo_eq_true _ _ (support_eo_requires_cond_eq_of_non_stuck hReq)
  have hbEq : b = __substitute_simul_rec (Term.Boolean false) body us
      (revAcc r Term.__eo_List_nil) Term.__eo_List_nil := by
    rw [hb]; exact instantiate_eo_requires_result_eq_of_ne_stuck hReq
  obtain ⟨vs, hvlen, rfl⟩ := lamVars_exists us m hv
  have hDistinct := SkolemizeRule.distinct_of_setof_guard (eoVarEnv_eoVarList vs) hSet
  obtain ⟨-, hBodyNN, hArgsNN⟩ := hs.parts_typed_any hANN
  obtain ⟨extra, rm, hr, hrmlen, htyped, hlt⟩ := spine_prefix_typed hs m hv hm hANN
  rw [lamBindings_eoVarList vs rm SmtBindings.nil (by omega),
    show vs.take rm.length = vs by rw [hrmlen, ← hvlen, List.take_length]] at htyped
  have hzipLen : vs.length = rm.reverse.length := by simp [hrmlen, hvlen]
  have hFacts : ∀ p ∈ vs.zip rm.reverse,
      __smtx_typeof (__eo_to_smt p.2) = __eo_to_smt_type p.1.2 ∧
        __smtx_type_wf (__eo_to_smt_type p.1.2) = true := fun p hp =>
    ⟨bind_binding_type_of_non_none htyped (bindsApp_mem _ _ p hp),
      bind_binding_type_wf_of_non_none htyped (bindsApp_mem _ _ p hp)⟩
  have hVarsWf : ∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hmem : (vs[i], rm.reverse[i]'(by omega)) ∈ vs.zip rm.reverse := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    exact (hFacts _ hmem).2
  have hL : revAcc r Term.__eo_List_nil =
      eoListApp rm.reverse (eoListApp extra.reverse Term.__eo_List_nil) := by
    rw [revAcc_eq, hr, List.reverse_append, eoListApp_append]
  have hActuals : SubstActualsHaveSmtTypes (eoVarList vs) (revAcc r Term.__eo_List_nil) := by
    rw [hL]
    exact actuals_of_typed _ vs rm.reverse hzipLen hFacts
  have hTs : EoListAllHaveSmtTranslation (revAcc r Term.__eo_List_nil) := by
    rw [revAcc_eq]
    exact eoListApp_all_translations _ (fun x hx => hArgsNN x (List.mem_reverse.1 hx))
  have hBodyTrans : RuleProofs.eo_has_smt_translation body := hBodyNN
  have hbTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) body (eoVarList vs)
        (revAcc r Term.__eo_List_nil) Term.__eo_List_nil) := by
    rw [← hbEq]; exact hBNN
  by_cases hmk : m < r.length
  · -- More arguments than variables: the types cannot agree.
    exfalso
    have hbTyNe : __eo_typeof (substResult false body (eoVarList vs)
        (revAcc r Term.__eo_List_nil) Term.__eo_List_nil) ≠ Term.Stuck :=
      SubstituteSupport.eo_typeof_ne_stuck_of_has_smt_translation _ hbTrans
    have hPres :=
      substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck body (eoVarList vs)
        (revAcc r Term.__eo_List_nil) Term.__eo_List_nil
        (EoVarEnvPerm.of_exact (eoVarEnv_eoVarList vs))
        (EoVarEnvPerm.of_exact EoVarEnv.nil) hBodyTrans hTs hActuals hbTyNe
    have hbTy : __smtx_typeof (__eo_to_smt b) = __smtx_typeof (__eo_to_smt body) := by
      rw [TranslationProofs.eo_to_smt_typeof_matches_translation b hBNN,
        TranslationProofs.eo_to_smt_typeof_matches_translation body hBodyNN, hbEq]
      exact congrArg __eo_to_smt_type hPres.1
    have := hlt hmk
    rw [hSame, hbTy] at this
    omega
  · have hmeq : m = r.length := by omega
    have hextra : extra = [] := by
      have := congrArg List.length hr
      simp at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hextra
    simp only [List.nil_append] at hr
    subst hr
    have hfull := hs.eo_to_smt_full (by rw [← hrmlen]; rw [hmeq] at hv; exact hv)
    rw [hfull, lamBindings_eoVarList vs rm SmtBindings.nil (by omega),
      show vs.take rm.length = vs by rw [hrmlen, ← hvlen, List.take_length],
      smtx_model_eval_bind_eq, push_bindings_bindsApp, model_push_bindings_nil,
      ← pushL_reverse_of_distinct M _ (distinct_keys M vs rm.reverse hzipLen hDistinct hVarsWf),
      ← pushSubstModel_eoVarList M vs rm.reverse Term.__eo_List_nil hzipLen, hbEq,
      InstantiateRule.substitute_simul_eval M hM body (eoVarList vs)
        (revAcc rm Term.__eo_List_nil) hBodyTrans hTs hActuals hbTrans, revAcc_eq]

end BetaReduceRule
