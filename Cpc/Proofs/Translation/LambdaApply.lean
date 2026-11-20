module

public import Cpc.Proofs.Translation.Lambda
import all Cpc.Proofs.Translation.Lambda

/-!
# Applications of lambdas, as lists

Lemmas about lambda spines (`LamSpine`) stated over Lean lists: the variables
a lambda binds as a list of EO variable keys, its arguments in application
order, the bindings of a spine that applies its lambda to all its variables,
and the models those bindings push. Shared by the substitution engine and the
`beta-reduce` rule.
-/

public section

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace LamSpineSupport

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
      obtain ⟨vs, hlen, rfl⟩ := lamVars_exists us n (by
        simp only [lamVars, Bool.and_eq_true] at h; exact h.2)
      exact ⟨(s, T) :: vs, by simp [hlen], rfl⟩
  | Term.__eo_List_nil, _ + 1, h => by cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) _)) _, 0, h => by
      cases h

theorem lamVars_eoVarList (vs : List (native_String × Term))
    (hwf : ∀ p ∈ vs, lamVarWf p.2 = true) :
    lamVars (eoVarList vs) vs.length = true := by
  induction vs with
  | nil => rfl
  | cons p vs ih =>
      obtain ⟨s, T⟩ := p
      simp only [List.length_cons]
      change (lamVarWf T && lamVars (eoVarList vs) vs.length) = true
      rw [hwf (s, T) List.mem_cons_self, ih (fun q hq => hwf q (List.mem_cons_of_mem _ hq))]
      rfl

/-- The variables of a list of variables a lambda may bind are ones it may
bind. -/
theorem lamVars_wf_of_eoVarList :
    ∀ (vs : List (native_String × Term)) {n : Nat}, lamVars (eoVarList vs) n = true ->
      ∀ p ∈ vs, lamVarWf p.2 = true
  | [], _, _, p, hp => absurd hp List.not_mem_nil
  | (s, T) :: vs, 0, h, _, _ => by cases h
  | (s, T) :: vs, n + 1, h, p, hp => by
      change (lamVarWf T && lamVars (eoVarList vs) n) = true at h
      simp only [Bool.and_eq_true] at h
      rcases List.mem_cons.1 hp with rfl | hp
      · exact h.1
      · exact lamVars_wf_of_eoVarList vs h.2 p hp

/-- Two lists of variables of the same types are both ones a lambda may bind
or neither is. -/
theorem lamVars_eoVarList_of_types (vs vs' : List (native_String × Term))
    (hTys : vs'.map Prod.snd = vs.map Prod.snd)
    (h : lamVars (eoVarList vs) vs.length = true) :
    lamVars (eoVarList vs') vs.length = true := by
  have hlen : vs'.length = vs.length := by simpa using congrArg List.length hTys
  rw [← hlen]
  apply lamVars_eoVarList
  intro p hp
  have hmem : p.2 ∈ vs.map Prod.snd := hTys ▸ List.mem_map_of_mem hp
  obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hmem
  rw [← hqe]
  exact lamVars_wf_of_eoVarList vs h q hq

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
      simp only [lamVars, Bool.and_eq_true] at h
      simp only [lamVarsPrefix, h.1, Bool.true_and]
      exact lamVarsPrefix_of_lamVars_le us m k h.2 (by omega)
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
      simp only [lamVars, Bool.and_eq_true] at h
      simp only [lamVarsPrefix, h.1, Bool.true_and]
      exact lamVarsPrefix_false_of_lamVars_lt us m k h.2 (by omega)
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
      simp only [lamVars, Bool.and_eq_true] at h
      simp only [eoListDrop]
      exact eoListDrop_cons_of_lamVars_lt us m k h.2 (by omega)
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
@[expose] noncomputable def evalBinds (M : SmtModel) (l : List ((native_String × Term) × Term)) :
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

/-! ## Lists of typed bindings -/

theorem bindsApp_mem :
    ∀ (l : List ((native_String × Term) × Term)) (bs : SmtBindings),
      ∀ p ∈ l, SmtBindings.Mem (bindsApp l bs) p.1.1 (__eo_to_smt_type p.1.2) (__eo_to_smt p.2)
  | [], _, p, hp => absurd hp List.not_mem_nil
  | ((s, T), a) :: l, bs, p, hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · exact SmtBindings.Mem.head _ _ _ _
      · exact SmtBindings.Mem.tail _ _ _ (bindsApp_mem l bs p hp)

/-! ## Spines as Lean lists -/

/-- The lambda `(lambda us body)`. -/
@[expose] def lamT (us body : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body

/-- `h` applied to the arguments `r`, listed last first. -/
@[expose] def mkSpine (h : Term) : List Term -> Term
  | [] => h
  | a :: r => Term.Apply (mkSpine h r) a

theorem lamSpine_mkSpine (us body : Term) :
    ∀ r : List Term, LamSpine (mkSpine (lamT us body) r) us body r
  | [] => LamSpine.lam us body
  | a :: r => LamSpine.app a (lamSpine_mkSpine us body r)

theorem LamSpine.eq_mkSpine {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    t = mkSpine (lamT us body) r := by
  induction h with
  | lam => rfl
  | app a _ ih => rw [ih]; rfl

/-- The keyed values pushed for the variables `vs`, given their values. -/
@[expose] def keyVals : List (native_String × Term) -> List SmtValue ->
    List (native_String × SmtType × SmtValue)
  | (s, T) :: vs, v :: vals => (s, __eo_to_smt_type T, v) :: keyVals vs vals
  | _, _ => []

theorem evalBinds_eq_keyVals (M : SmtModel) :
    ∀ (vs : List (native_String × Term)) (l : List Term),
      evalBinds M (vs.zip l) =
        keyVals vs (l.map (fun a => __smtx_model_eval M (__eo_to_smt a)))
  | [], l => by cases l <;> rfl
  | (s, T) :: vs, [] => rfl
  | (s, T) :: vs, a :: l => by
      simp only [List.zip_cons_cons, List.map_cons, keyVals]
      rw [← evalBinds_eq_keyVals M vs l]
      rfl

/-- The translation of a spine applied to all of its variables, as the model
its `let` pushes. -/
theorem push_bindings_lamBindings_eoVarList (M : SmtModel)
    (vs : List (native_String × Term)) (r : List Term) (hlen : r.length = vs.length) :
    __smtx_model_eval.push_bindings M M (lamBindings (eoVarList vs) r SmtBindings.nil) =
      pushL M (keyVals vs (r.reverse.map (fun a => __smtx_model_eval M (__eo_to_smt a)))) := by
  rw [lamBindings_eoVarList vs r SmtBindings.nil (by omega),
    show vs.take r.length = vs by rw [hlen, List.take_length],
    push_bindings_bindsApp, model_push_bindings_nil, evalBinds_eq_keyVals]

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
  rw [h.eo_to_smt_prefix.1 hpre, hD] at hNN
  cases hw : lamVarWf T
  · rw [curry_cons_of_not_wf _ _ _ _ hw] at hNN
    exact hNN (by rw [smtx_typeof_bind_eq, smtx_typeof_none]; exact smtx_typeof_bindings_none _)
  · rw [curry_cons_of_wf _ _ _ _ hw] at hNN
    exact hNN (smtx_typeof_pending ⟨_, _, _, _, rfl⟩)

theorem smtx_typeof_apply_result {F X A B : SmtType}
    (hF : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) (hX : X = A)
    (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B ∧ sizeOf B < sizeOf F := by
  subst hX
  rcases hF with rfl | rfl <;>
    exact ⟨by simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA],
      by first | simp | (simp; omega)⟩

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
      obtain ⟨vs, hl, hus⟩ := lamVars_exists us 0 hv
      rw [List.length_eq_zero_iff] at hl
      subst hl
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
        obtain ⟨hRes, hSize⟩ := smtx_typeof_apply_result hF hX hA
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

/-- The translation of an application of a spine whose lambda does not wait
for an argument is the SMT application. -/
theorem eo_to_smt_mkSpine_apply_of_lamVars_lt {us body : Term} {m : Nat}
    (hv : lamVars us m = true) (a : Term) (r : List Term) (hlt : m < r.length + 1) :
    __eo_to_smt (mkSpine (lamT us body) (a :: r)) =
      SmtTerm.Apply (__eo_to_smt (mkSpine (lamT us body) r))
        (__eo_to_smt a) := by
  have hs := lamSpine_mkSpine us body r
  have hnp : ¬ TranslationProofs.SmtPendingLam
      (__eo_to_smt (mkSpine (lamT us body) r)) := by
    intro hp
    have hpre := lamVarsPrefix_of_pending_app a hs hp
    rw [lamVarsPrefix_false_of_lamVars_lt us m _ hv (by simpa using hlt)] at hpre
    cases hpre
  change __eo_to_smt (Term.Apply (mkSpine (lamT us body) r) a) = _
  rw [hs.eo_to_smt_app a, TranslationProofs.eo_to_smt_apply_of_not_pending _ hnp]

theorem smtx_typeof_mkSpine_apply {us body : Term} (a : Term) (r : List Term) :
    __smtx_typeof (SmtTerm.Apply
        (__eo_to_smt (mkSpine (lamT us body) r))
        (__eo_to_smt a)) =
      __smtx_typeof_apply
        (__smtx_typeof (__eo_to_smt (mkSpine (lamT us body) r)))
        (__smtx_typeof (__eo_to_smt a)) := by
  rcases (lamSpine_mkSpine us body r).eo_to_smt_bind_or_apply with
    ⟨bs, b, hg⟩ | ⟨g, x, hg⟩ <;> rw [hg] <;> rfl

end LamSpineSupport
