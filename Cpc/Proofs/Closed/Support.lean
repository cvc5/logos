module

import Lean
public import Cpc.Proofs.Common
import all Cpc.Proofs.Common
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions
public import Cpc.Proofs.RuleSupport.Contract
import all Cpc.Proofs.RuleSupport.Contract

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev SmtVarKey : Type := native_String × SmtType

/-- Agreement on the currently bound SMT variables. -/
def model_agrees_on_vars (vars : List SmtVarKey) (M N : SmtModel) : Prop :=
  ∀ s T, (s, T) ∈ vars ->
    native_model_var_lookup M s T = native_model_var_lookup N s T

/-- Agreement on globals plus a finite bound-variable environment. -/
structure model_agrees_on_env (vars : List SmtVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq : model_agrees_on_vars vars M N

theorem model_agrees_on_env_refl (vars : List SmtVarKey) (M : SmtModel) :
  model_agrees_on_env vars M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T hMem; rfl⟩

theorem model_agrees_on_env_nil_of_globals
    {M N : SmtModel} :
  model_agrees_on_globals M N ->
    model_agrees_on_env [] M N :=
by
  intro hAgree
  exact ⟨hAgree, by intro s T hMem; cases hMem⟩

theorem model_agrees_on_globals_push
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
  model_agrees_on_globals M (native_model_push M s T v) :=
by
  exact
    ⟨by
      intro s' T'
      simp [native_model_lookup, model_key, native_model_push],
    by
      intro fid A B
      simp [model_fun_lookup, model_key, native_model_push]⟩

theorem model_agrees_on_globals_push₂
    {M N : SmtModel} {s : native_String} {T : SmtType} {v : SmtValue} :
  model_agrees_on_globals M N ->
  model_agrees_on_globals (native_model_push M s T v) (native_model_push N s T v) :=
by
  intro hAgree
  exact
    ⟨by
      intro s' T'
      simpa [native_model_lookup, model_key, native_model_push]
        using hAgree.1 s' T',
    by
      intro fid A B
      simpa [model_fun_lookup, model_key, native_model_push]
        using hAgree.2 fid A B⟩

theorem model_agrees_on_env_push_same
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue} :
  model_agrees_on_env vars M N ->
  model_agrees_on_env ((s, T) :: vars)
    (native_model_push M s T v) (native_model_push N s T v) :=
by
  intro hAgree
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hMem
  cases hMem with
  | head =>
      simp [native_model_var_lookup, native_model_push]
  | tail _ hTail =>
      by_cases hKey :
          ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
            { isVar := true, name := s, ty := T }
      · cases hKey
        simp [native_model_var_lookup, native_model_push]
      · simpa [native_model_var_lookup, native_model_push, hKey]
          using hAgree.vars_eq s' T' hTail

theorem native_model_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    (s : native_String) (T : SmtType) :
  native_model_lookup M s T =
    native_model_lookup N s T :=
by
  exact hAgree.globals.1 s T

theorem native_model_fun_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    (fid : native_String) (T U : SmtType) :
  model_fun_lookup M fid T U =
    model_fun_lookup N fid T U :=
by
  exact hAgree.globals.2 fid T U

theorem native_model_var_lookup_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_on_env vars M N)
    {s : native_String} {T : SmtType}
    (hMem : (s, T) ∈ vars) :
  native_model_var_lookup M s T =
    native_model_var_lookup N s T :=
by
  exact hAgree.vars_eq s T hMem

theorem native_eval_fun_apply_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (fid : native_String) (T U : SmtType) (i : SmtValue) :
  native_eval_fun_apply M fid T U i =
    native_eval_fun_apply N fid T U i :=
by
  by_cases hDefault : fid = native_default_fun_id
  · simp [native_eval_fun_apply, hDefault]
  · simp [native_eval_fun_apply, hDefault, hAgree.2 fid T U]

theorem smtx_model_eval_apply_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (f i : SmtValue) :
  __smtx_model_eval_apply M f i =
    __smtx_model_eval_apply N f i :=
by
  cases f <;> cases i <;>
    simp [__smtx_model_eval_apply, native_eval_fun_apply_eq_of_globals hAgree]

theorem smtx_seq_nth_wrong_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (s : SmtSeq) (n : native_Int) (T : SmtType) :
  __smtx_seq_nth_wrong M s n T =
    __smtx_seq_nth_wrong N s n T :=
by
  cases T <;> simp [__smtx_seq_nth_wrong, hAgree.1]

theorem smtx_seq_nth_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (v n : SmtValue) :
  __smtx_seq_nth M v n =
    __smtx_seq_nth N v n :=
by
  cases v <;> cases n <;>
    simp [__smtx_seq_nth, smtx_seq_nth_wrong_eq_of_globals hAgree]

theorem smtx_model_eval_dt_sel_eq_of_globals
    {M N : SmtModel} (hAgree : model_agrees_on_globals M N)
    (s : native_String) (d : SmtDatatypeDecl) (n m : native_Nat) (v : SmtValue) :
  __smtx_model_eval_dt_sel M s d n m v =
    __smtx_model_eval_dt_sel N s d n m v :=
by
  cases v <;>
    simp [__smtx_model_eval_dt_sel, smtx_model_eval_apply_eq_of_globals hAgree,
      hAgree.1 (native_wrong_apply_sel_id n m)
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m))]

theorem native_eval_texists_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  (native_eval_exists M s T body : SmtValue) =
    (native_eval_exists N s T body : SmtValue) :=
by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v] using hEval⟩
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

theorem native_eval_tforall_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  (native_eval_forall M s T body : SmtValue) =
    (native_eval_forall N s T body : SmtValue) :=
by
  classical
  let PM : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PN : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h v hTy hCanon
      simpa [hBody v] using h v hTy hCanon
    · intro h v hTy hCanon
      simpa [← hBody v] using h v hTy hCanon
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

theorem native_eval_tchoice_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  (native_eval_choice M s T body : SmtValue) =
    (native_eval_choice N s T body : SmtValue) :=
by
  classical
  let PredM : SmtValue -> Prop := fun v =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  let PredN : SmtValue -> Prop := fun v =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) body = SmtValue.Boolean true
  let PTy : Prop :=
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v
  change
    (if hSat : ∃ v : SmtValue, PredM v then Classical.choose hSat
      else if hTy : PTy then Classical.choose hTy else SmtValue.NotValue) =
    (if hSat : ∃ v : SmtValue, PredN v then Classical.choose hSat
      else if hTy : PTy then Classical.choose hTy else SmtValue.NotValue)
  have hPredEq : PredM = PredN := by
    funext v
    apply propext
    constructor
    · intro h
      exact ⟨h.1, h.2.1, by simpa [hBody v] using h.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, by simpa [← hBody v] using h.2.2⟩
  rw [hPredEq]

/-- SMT term closedness relative to a stack of bound variables. -/
def SmtTermClosedIn (vars : List SmtVarKey) : SmtTerm -> Prop
  | SmtTerm.None => True
  | SmtTerm.Boolean _ => True
  | SmtTerm.Numeral _ => True
  | SmtTerm.Rational _ => True
  | SmtTerm.String _ => True
  | SmtTerm.Binary _ _ => True
  | SmtTerm.Apply f x => SmtTermClosedIn vars f ∧ SmtTermClosedIn vars x
  | SmtTerm.Var s T => (s, T) ∈ vars
  | SmtTerm.ite c t e =>
      SmtTermClosedIn vars c ∧ SmtTermClosedIn vars t ∧ SmtTermClosedIn vars e
  | SmtTerm.eq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.exists s T body => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.forall s T body => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.choice s T body => SmtTermClosedIn ((s, T) :: vars) body
  | SmtTerm.bind s T x1 x2 =>
      SmtTermClosedIn vars x1 ∧ SmtTermClosedIn ((s, T) :: vars) x2
  | SmtTerm.map_diff x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.seq_diff x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.DtCons _ _ _ => True
  | SmtTerm.DtSel _ _ _ _ => True
  | SmtTerm.DtTester _ _ _ => True
  | SmtTerm.UConst _ _ => True
  | SmtTerm.not x => SmtTermClosedIn vars x
  | SmtTerm.or x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.and x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.imp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.xor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm._at_purify x => SmtTermClosedIn vars x
  | SmtTerm.plus x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.neg x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mult x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.lt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.leq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.gt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.geq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.to_real x => SmtTermClosedIn vars x
  | SmtTerm.to_int x => SmtTermClosedIn vars x
  | SmtTerm.is_int x => SmtTermClosedIn vars x
  | SmtTerm.abs x => SmtTermClosedIn vars x
  | SmtTerm.uneg x => SmtTermClosedIn vars x
  | SmtTerm.div x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mod x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.divisible x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.int_pow2 x => SmtTermClosedIn vars x
  | SmtTerm.int_log2 x => SmtTermClosedIn vars x
  | SmtTerm.div_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.mod_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.select x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.store x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.extract x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.repeat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnot x => SmtTermClosedIn vars x
  | SmtTerm.bvand x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnand x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvxor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvxnor x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvcomp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvneg x => SmtTermClosedIn vars x
  | SmtTerm.bvadd x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvmul x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvudiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvurem x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsub x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsdiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsrem x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsmod x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvult x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvule x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvugt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvuge x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvslt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsle x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsgt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsge x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvshl x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvlshr x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvashr x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.zero_extend x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.sign_extend x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.rotate_left x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.rotate_right x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvuaddo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvnego x => SmtTermClosedIn vars x
  | SmtTerm.bvsaddo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvumulo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsmulo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvusubo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvssubo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.bvsdivo x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.seq_empty _ => True
  | SmtTerm.str_len x => SmtTermClosedIn vars x
  | SmtTerm.str_concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_substr x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_contains x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_replace x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_indexof x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_at x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_prefixof x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_suffixof x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_rev x => SmtTermClosedIn vars x
  | SmtTerm.str_update x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_to_lower x => SmtTermClosedIn vars x
  | SmtTerm.str_to_upper x => SmtTermClosedIn vars x
  | SmtTerm.str_to_code x => SmtTermClosedIn vars x
  | SmtTerm.str_from_code x => SmtTermClosedIn vars x
  | SmtTerm.str_is_digit x => SmtTermClosedIn vars x
  | SmtTerm.str_to_int x => SmtTermClosedIn vars x
  | SmtTerm.str_from_int x => SmtTermClosedIn vars x
  | SmtTerm.str_lt x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_leq x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.str_replace_all x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_replace_re x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_replace_re_all x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_indexof_re x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_indexof_re_split x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.re_allchar => True
  | SmtTerm.re_none => True
  | SmtTerm.re_all => True
  | SmtTerm.str_to_re x => SmtTermClosedIn vars x
  | SmtTerm.re_mult x => SmtTermClosedIn vars x
  | SmtTerm.re_plus x => SmtTermClosedIn vars x
  | SmtTerm.re_exp x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_opt x => SmtTermClosedIn vars x
  | SmtTerm.re_comp x => SmtTermClosedIn vars x
  | SmtTerm.re_range x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_concat x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_inter x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_union x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_diff x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.re_loop x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.str_in_re x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.seq_unit x => SmtTermClosedIn vars x
  | SmtTerm.seq_nth x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm._at_strings_occur_index x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm._at_strings_occur_index_re x y z =>
      SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y ∧ SmtTermClosedIn vars z
  | SmtTerm.set_empty _ => True
  | SmtTerm.set_singleton x => SmtTermClosedIn vars x
  | SmtTerm.set_union x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_inter x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_minus x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_member x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.set_subset x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.qdiv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.qdiv_total x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.int_to_bv x y => SmtTermClosedIn vars x ∧ SmtTermClosedIn vars y
  | SmtTerm.ubv_to_int x => SmtTermClosedIn vars x
  | SmtTerm.sbv_to_int x => SmtTermClosedIn vars x

theorem SmtTermClosedIn.mono
    {t : SmtTerm} {vars vars' : List SmtVarKey}
    (hSub : ∀ s T, (s, T) ∈ vars -> (s, T) ∈ vars')
    (hClosed : SmtTermClosedIn vars t) :
  SmtTermClosedIn vars' t :=
by
  let rec go (t : SmtTerm) {vars vars' : List SmtVarKey}
      (hSub : ∀ s T, (s, T) ∈ vars -> (s, T) ∈ vars')
      (hClosed : SmtTermClosedIn vars t) :
    SmtTermClosedIn vars' t :=
  by
    cases t <;> simp [SmtTermClosedIn] at hClosed ⊢
    case Var s T =>
      exact hSub s T hClosed
    case «exists» s T body =>
      exact go body (by
        intro s' T' hMem
        cases hMem with
        | head => exact List.Mem.head _
        | tail _ hTail => exact List.Mem.tail _ (hSub s' T' hTail)) hClosed
    case «forall» s T body =>
      exact go body (by
        intro s' T' hMem
        cases hMem with
        | head => exact List.Mem.head _
        | tail _ hTail => exact List.Mem.tail _ (hSub s' T' hTail)) hClosed
    case choice s T body =>
      exact go body (by
        intro s' T' hMem
        cases hMem with
        | head => exact List.Mem.head _
        | tail _ hTail => exact List.Mem.tail _ (hSub s' T' hTail)) hClosed
    case bind s T x1 x2 =>
      refine ⟨go x1 hSub hClosed.1, go x2 (by
        intro s' T' hMem
        cases hMem with
        | head => exact List.Mem.head _
        | tail _ hTail => exact List.Mem.tail _ (hSub s' T' hTail)) hClosed.2⟩
    all_goals try exact go _ hSub hClosed
    all_goals try exact ⟨go _ hSub hClosed.1, go _ hSub hClosed.2⟩
    all_goals try exact ⟨go _ hSub hClosed.1, go _ hSub hClosed.2.1,
      go _ hSub hClosed.2.2⟩
  exact go t hSub hClosed

theorem SmtTermClosedIn.weaken_cons
    {t : SmtTerm} {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    (hClosed : SmtTermClosedIn vars t) :
  SmtTermClosedIn ((s, T) :: vars) t :=
by
  exact SmtTermClosedIn.mono
    (t := t) (vars := vars) (vars' := (s, T) :: vars)
    (by intro s' T' hMem; exact List.Mem.tail _ hMem)
    hClosed

theorem SmtTermClosedIn.exists_env
    (t : SmtTerm) :
    ∃ vars : List SmtVarKey, SmtTermClosedIn vars t := by
  let rec go (t : SmtTerm) :
      ∃ vars : List SmtVarKey, SmtTermClosedIn vars t := by
    cases t <;> simp [SmtTermClosedIn]
    case Var s T =>
      exact ⟨[(s, T)], by simp⟩
    case «exists» s T body =>
      rcases go body with ⟨vars, hClosed⟩
      exact ⟨vars, SmtTermClosedIn.weaken_cons hClosed⟩
    case «forall» s T body =>
      rcases go body with ⟨vars, hClosed⟩
      exact ⟨vars, SmtTermClosedIn.weaken_cons hClosed⟩
    case choice s T body =>
      rcases go body with ⟨vars, hClosed⟩
      exact ⟨vars, SmtTermClosedIn.weaken_cons hClosed⟩
    case bind s T x1 x2 =>
      rcases go x1 with ⟨varsX, hX⟩
      rcases go x2 with ⟨varsY, hY⟩
      refine ⟨varsX ++ varsY, ?_, ?_⟩
      · exact SmtTermClosedIn.mono
          (vars := varsX) (vars' := varsX ++ varsY)
          (by intro s T hMem; exact List.mem_append_left _ hMem) hX
      · exact SmtTermClosedIn.mono
          (vars := varsY) (vars' := (s, T) :: (varsX ++ varsY))
          (by intro s' T' hMem;
              exact List.Mem.tail _ (List.mem_append_right _ hMem)) hY
    all_goals try
      first
      | exact ⟨[], trivial⟩
      | rename_i x
        rcases go x with ⟨vars, hClosed⟩
        exact ⟨vars, hClosed⟩
      | rename_i x y
        rcases go x with ⟨varsX, hX⟩
        rcases go y with ⟨varsY, hY⟩
        refine ⟨varsX ++ varsY, ?_⟩
        constructor
        · exact SmtTermClosedIn.mono
            (vars := varsX) (vars' := varsX ++ varsY)
            (by intro s T hMem; exact List.mem_append_left _ hMem) hX
        · exact SmtTermClosedIn.mono
            (vars := varsY) (vars' := varsX ++ varsY)
            (by intro s T hMem; exact List.mem_append_right _ hMem) hY
    all_goals try
      rename_i x y z
      rcases go x with ⟨varsX, hX⟩
      rcases go y with ⟨varsY, hY⟩
      rcases go z with ⟨varsZ, hZ⟩
      refine ⟨(varsX ++ varsY) ++ varsZ, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · exact SmtTermClosedIn.mono
          (vars := varsX) (vars' := (varsX ++ varsY) ++ varsZ)
          (by
            intro s T hMem
            exact List.mem_append_left varsZ (List.mem_append_left varsY hMem)) hX
      · exact SmtTermClosedIn.mono
          (vars := varsY) (vars' := (varsX ++ varsY) ++ varsZ)
          (by
            intro s T hMem
            exact List.mem_append_left varsZ (List.mem_append_right varsX hMem)) hY
      · exact SmtTermClosedIn.mono
          (vars := varsZ) (vars' := (varsX ++ varsY) ++ varsZ)
          (by
            intro s T hMem
            exact List.mem_append_right (varsX ++ varsY) hMem) hZ
  exact go t

theorem eo_and_eq_true_cases {a b : Term} :
  __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true :=
by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at h ⊢
  case Binary.Binary =>
    split at h <;> contradiction

theorem eo_is_closed_eq_true_rec_nil
    {P : Term}
    (hClosed : __eo_is_closed P = Term.Boolean true) :
  __eo_is_closed_rec P Term.__eo_List_nil = Term.Boolean true :=
by
  cases P
  case Stuck =>
    cases hClosed
  all_goals
    simp [__eo_is_closed] at hClosed
    exact hClosed

/-- Relation between an EO list of variables and the corresponding SMT binder stack. -/
inductive EoSmtVarEnv : Term -> List SmtVarKey -> Prop where
  | nil :
      EoSmtVarEnv Term.__eo_List_nil []
  | cons {s : native_String} {T env : Term} {vars : List SmtVarKey} :
      EoSmtVarEnv env vars ->
        EoSmtVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env)
          ((s, __eo_to_smt_type T) :: vars)

theorem EoSmtVarEnv.get_nil_ok :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        __eo_is_ok (__eo_get_nil_rec Term.__eo_List_cons env) =
          Term.Boolean true
  | _, _, EoSmtVarEnv.nil =>
      by
        simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
          __eo_is_ok, native_ite, native_teq, native_not]
  | _, _, EoSmtVarEnv.cons hTail =>
      by
        simpa [__eo_get_nil_rec, __eo_requires, __eo_is_ok,
          native_ite, native_teq, native_not] using hTail.get_nil_ok

theorem EoSmtVarEnv.is_list :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        __eo_is_list Term.__eo_List_cons env = Term.Boolean true
  | _, _, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_is_list] using EoSmtVarEnv.get_nil_ok EoSmtVarEnv.nil
        | cons hTail =>
            simpa [__eo_is_list] using
              EoSmtVarEnv.get_nil_ok (EoSmtVarEnv.cons hTail)

theorem EoSmtVarEnv.cons_mk_apply
    {s : native_String} {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  EoSmtVarEnv
    (__eo_mk_apply
      (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      env)
    ((s, __eo_to_smt_type T) :: vars) :=
by
  cases hEnv with
  | nil =>
      simpa [__eo_mk_apply] using
        EoSmtVarEnv.cons (s := s) (T := T) EoSmtVarEnv.nil
  | cons hTail =>
      simpa [__eo_mk_apply] using
        EoSmtVarEnv.cons (s := s) (T := T)
          (EoSmtVarEnv.cons hTail)

theorem EoSmtVarEnv.concat_rec :
    ∀ {vs env : Term} {binderVars vars : List SmtVarKey},
      EoSmtVarEnv vs binderVars ->
        EoSmtVarEnv env vars ->
          EoSmtVarEnv (__eo_list_concat_rec vs env) (binderVars ++ vars)
  | _, _, _, _, EoSmtVarEnv.nil, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec] using EoSmtVarEnv.nil
        | cons hTail =>
            simpa [__eo_list_concat_rec] using EoSmtVarEnv.cons hTail
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec, List.cons_append]
              using EoSmtVarEnv.cons_mk_apply
                (s := s) (T := T)
                (EoSmtVarEnv.concat_rec hTail EoSmtVarEnv.nil)
        | cons hEnvTail =>
            simpa [__eo_list_concat_rec, List.cons_append]
              using EoSmtVarEnv.cons_mk_apply
                (s := s) (T := T)
                (EoSmtVarEnv.concat_rec hTail (EoSmtVarEnv.cons hEnvTail))

theorem EoSmtVarEnv.concat :
    ∀ {vs env : Term} {binderVars vars : List SmtVarKey},
      EoSmtVarEnv vs binderVars ->
        EoSmtVarEnv env vars ->
          EoSmtVarEnv
            (__eo_list_concat Term.__eo_List_cons vs env)
            (binderVars ++ vars)
  | _, _, _, _, hVs, hEnv =>
      by
        have hVsList := hVs.is_list
        have hEnvList := hEnv.is_list
        simpa [__eo_list_concat, __eo_requires, hVsList, hEnvList,
          native_ite, native_teq, native_not]
          using EoSmtVarEnv.concat_rec hVs hEnv

theorem EoSmtVarEnv.mem_of_closed_var :
    ∀ {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term},
      EoSmtVarEnv env vars ->
        __eo_is_closed_rec (Term.Var (Term.String s) T) env =
          Term.Boolean true ->
          (s, __eo_to_smt_type T) ∈ vars
  | _, _, _, _, EoSmtVarEnv.nil, hClosed =>
      by
        simp [__eo_is_closed_rec] at hClosed
  | _, _, s, T, EoSmtVarEnv.cons (s := s') (T := T') hTail, hClosed =>
      by
        by_cases hVarEq :
            Term.Var (Term.String s') T' =
              Term.Var (Term.String s) T
        · injection hVarEq with hName hTy
          injection hName with hs
          cases hs
          cases hTy
          simp
        · right
          exact EoSmtVarEnv.mem_of_closed_var hTail (by
            simpa [__eo_is_closed_rec, __eo_ite, __eo_eq, hVarEq,
              native_ite, native_teq] using hClosed)

/-- Two SMT variable stacks expose the same bound variables. -/
def SmtVarEnvEquiv (xs ys : List SmtVarKey) : Prop :=
  ∀ key, key ∈ xs ↔ key ∈ ys

theorem SmtVarEnvEquiv.refl (xs : List SmtVarKey) :
  SmtVarEnvEquiv xs xs :=
by
  intro key
  rfl

theorem SmtVarEnvEquiv.reverse (xs : List SmtVarKey) :
  SmtVarEnvEquiv xs xs.reverse :=
by
  intro key
  simp

theorem SmtVarEnvEquiv.append
    {xs xs' ys ys' : List SmtVarKey}
    (hxs : SmtVarEnvEquiv xs xs')
    (hys : SmtVarEnvEquiv ys ys') :
  SmtVarEnvEquiv (xs ++ ys) (xs' ++ ys') :=
by
  intro key
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).1 h))
    · exact List.mem_append.2 (Or.inr ((hys key).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).2 h))
    · exact List.mem_append.2 (Or.inr ((hys key).2 h))

/--
Order-insensitive EO/SMT environment relation.

`__eo_is_closed_rec` only cares whether a variable appears in the EO list, while
SMT quantifier translation reverses binder order as it nests binders. This
wrapper lets those two views share the same membership facts.
-/
def EoSmtVarEnvPerm (env : Term) (vars : List SmtVarKey) : Prop :=
  ∃ exactVars, EoSmtVarEnv env exactVars ∧ SmtVarEnvEquiv exactVars vars

theorem EoSmtVarEnvPerm.of_exact
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  EoSmtVarEnvPerm env vars :=
by
  exact ⟨vars, hEnv, SmtVarEnvEquiv.refl vars⟩

theorem EoSmtVarEnvPerm.mem_of_closed_var
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  (s, __eo_to_smt_type T) ∈ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  exact (hEquiv (s, __eo_to_smt_type T)).1
    (EoSmtVarEnv.mem_of_closed_var hExact hClosed)

theorem EoSmtVarEnvPerm.concat_rev
    {vs env : Term} {binderVars vars : List SmtVarKey}
    (hVs : EoSmtVarEnv vs binderVars)
    (hEnv : EoSmtVarEnvPerm env vars) :
  EoSmtVarEnvPerm
    (__eo_list_concat Term.__eo_List_cons vs env)
    (binderVars.reverse ++ vars) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  refine ⟨binderVars ++ exactVars, EoSmtVarEnv.concat hVs hExact, ?_⟩
  exact SmtVarEnvEquiv.append
    (SmtVarEnvEquiv.reverse binderVars)
    hEquiv

theorem eo_is_closed_rec_apply_uop_arg_eq_true
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact (eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)).2
  | cons hTail =>
      exact (eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)).2

theorem eo_is_closed_rec_apply_eq_true_cases_of_not_quantifier
    {f x env : Term} {vars : List SmtVarKey}
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Apply f x) env =
        Term.Boolean true) :
  __eo_is_closed_rec f env = Term.Boolean true ∧
    __eo_is_closed_rec x env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      cases f
      case Apply g y =>
        cases g
        case UOp op =>
          cases op
          case «forall» =>
            exfalso
            exact hNotForall y rfl
          case «exists» =>
            exfalso
            exact hNotExists y rfl
          all_goals
            exact eo_and_eq_true_cases
              (by simpa [__eo_is_closed_rec] using hClosed)
        all_goals
          exact eo_and_eq_true_cases
            (by simpa [__eo_is_closed_rec] using hClosed)
      all_goals
        exact eo_and_eq_true_cases
          (by simpa [__eo_is_closed_rec] using hClosed)
  | cons hTail =>
      cases f
      case Apply g y =>
        cases g
        case UOp op =>
          cases op
          case «forall» =>
            exfalso
            exact hNotForall y rfl
          case «exists» =>
            exfalso
            exact hNotExists y rfl
          all_goals
            exact eo_and_eq_true_cases
              (by simpa [__eo_is_closed_rec] using hClosed)
        all_goals
          exact eo_and_eq_true_cases
            (by simpa [__eo_is_closed_rec] using hClosed)
      all_goals
        exact eo_and_eq_true_cases
          (by simpa [__eo_is_closed_rec] using hClosed)

theorem eo_is_closed_rec_binary_uop_eq_true_cases
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hEnv' : EoSmtVarEnvPerm Term.__eo_List_nil vars :=
        ⟨_, EoSmtVarEnv.nil, hEquiv⟩
      have hOuter := eo_and_eq_true_cases
        (by
          simpa [__eo_is_closed_rec, hNotForall, hNotExists]
            using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.2, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by
          simpa [__eo_is_closed_rec, hNotForall, hNotExists]
            using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.2, hOuter.2⟩

theorem eo_is_closed_rec_ternary_uop_eq_true_cases
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true ∧
      __eo_is_closed_rec z env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner :=
        eo_is_closed_rec_binary_uop_eq_true_cases hNotForall hNotExists
          ⟨_, EoSmtVarEnv.nil, hEquiv⟩ hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner :=
        eo_is_closed_rec_binary_uop_eq_true_cases hNotForall hNotExists
          ⟨_, EoSmtVarEnv.cons hTail, hEquiv⟩ hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩

theorem eo_is_closed_rec_quaternary_uop_eq_true_cases
    {op : UserOp} {w x y z env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) x) y) z)
        env = Term.Boolean true) :
  __eo_is_closed_rec w env = Term.Boolean true ∧
    __eo_is_closed_rec x env = Term.Boolean true ∧
      __eo_is_closed_rec y env = Term.Boolean true ∧
        __eo_is_closed_rec z env = Term.Boolean true :=
by
  have hOuter :=
    eo_is_closed_rec_apply_eq_true_cases_of_not_quantifier
      (f := Term.Apply
        (Term.Apply (Term.Apply (Term.UOp op) w) x) y)
      (by intro vs h; cases h)
      (by intro vs h; cases h)
      hEnv hClosed
  have hInner :=
    eo_is_closed_rec_ternary_uop_eq_true_cases
      hNotForall hNotExists hEnv hOuter.1
  exact ⟨hInner.1, hInner.2.1, hInner.2.2, hOuter.2⟩

theorem eo_is_closed_rec_uop1_eq_true
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 op x) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      simpa [__eo_is_closed_rec] using hClosed
  | cons hTail =>
      simpa [__eo_is_closed_rec] using hClosed

theorem eo_is_closed_rec_uop2_eq_true_cases
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
  | cons hTail =>
      exact eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)

theorem eo_is_closed_rec_uop3_eq_true_cases
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true ∧
      __eo_is_closed_rec z env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩

theorem eo_is_closed_rec_apply_uop1_eq_true_cases
    {op : UserOp1} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op x) y) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      exact ⟨hOuter.1, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      exact ⟨hOuter.1, hOuter.2⟩

theorem eo_is_closed_rec_apply_uop2_eq_true_cases
    {op : UserOp2} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op x y) z) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true ∧
      __eo_is_closed_rec z env = Term.Boolean true :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩
  | cons hTail =>
      have hOuter := eo_and_eq_true_cases
        (by simpa [__eo_is_closed_rec] using hClosed)
      have hInner := eo_and_eq_true_cases hOuter.1
      exact ⟨hInner.1, hInner.2, hOuter.2⟩

theorem eo_is_closed_rec_apply_apply_uop1_eq_true_cases
    {op : UserOp1} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) env =
        Term.Boolean true) :
  __eo_is_closed_rec x env = Term.Boolean true ∧
    __eo_is_closed_rec y env = Term.Boolean true ∧
      __eo_is_closed_rec z env = Term.Boolean true :=
by
  have hOuter :=
    eo_is_closed_rec_apply_eq_true_cases_of_not_quantifier
      (f := Term.Apply (Term.UOp1 op x) y)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hClosed
  have hInner :=
    eo_is_closed_rec_apply_uop1_eq_true_cases hEnv hOuter.1
  exact ⟨hInner.1, hInner.2, hOuter.2⟩

theorem smtTermClosedIn_eo_to_smt_boolean
    (vars : List SmtVarKey) (b : native_Bool) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Boolean b)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_numeral
    (vars : List SmtVarKey) (n : native_Int) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Numeral n)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_rational
    (vars : List SmtVarKey) (r : native_Rat) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Rational r)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_string
    (vars : List SmtVarKey) (s : native_String) :
  SmtTermClosedIn vars (__eo_to_smt (Term.String s)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_binary
    (vars : List SmtVarKey) (w n : native_Int) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Binary w n)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_var_string
    {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hMem : (s, __eo_to_smt_type T) ∈ vars) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact hMem

theorem smtTermClosedIn_eo_to_smt_var_string_of_closed_rec
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnv env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact smtTermClosedIn_eo_to_smt_var_string
    (EoSmtVarEnv.mem_of_closed_var hEnv hClosed)

theorem smtTermClosedIn_eo_to_smt_var_string_of_closed_rec_perm
    {env : Term} {vars : List SmtVarKey} {s : native_String} {T : Term}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  exact smtTermClosedIn_eo_to_smt_var_string
    (EoSmtVarEnvPerm.mem_of_closed_var hEnv hClosed)

theorem smtTermClosedIn_eo_to_smt_var_of_closed_rec_perm
    {env : Term} {vars : List SmtVarKey} {name T : Term}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed :
      __eo_is_closed_rec (Term.Var name T) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Var name T)) :=
by
  cases name <;> try trivial
  case String s =>
    exact smtTermClosedIn_eo_to_smt_var_string_of_closed_rec_perm hEnv hClosed

theorem smtTermClosedIn_eo_to_smt_uop
    (vars : List SmtVarKey) (op : UserOp) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp op)) :=
by
  cases op <;> trivial

theorem smtTermClosedIn_eo_to_smt_dtcons
    (vars : List SmtVarKey) (s : native_String) (d : DatatypeDecl)
    (i : native_Nat) :
  SmtTermClosedIn vars (__eo_to_smt (Term.DtCons s d i)) :=
by
  change SmtTermClosedIn vars
    (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
      (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i))
  cases __eo_to_smt_reserved_datatype_name s <;> trivial

theorem smtTermClosedIn_eo_to_smt_dtsel
    (vars : List SmtVarKey) (s : native_String) (d : DatatypeDecl)
    (i j : native_Nat) :
  SmtTermClosedIn vars (__eo_to_smt (Term.DtSel s d i j)) :=
by
  change SmtTermClosedIn vars
    (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
      (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
  cases __eo_to_smt_reserved_datatype_name s <;> trivial

theorem smtTermClosedIn_eo_to_smt_uconst
    (vars : List SmtVarKey) (i : native_Nat) (T : Term) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UConst i T)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_tester
    {vars : List SmtVarKey} {t : SmtTerm} :
  SmtTermClosedIn vars (__eo_to_smt_tester t) :=
by
  cases t <;> trivial

theorem smtTermClosedIn_eo_to_smt_not
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_to_real
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_to_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_is_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_abs
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_uneg
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_int_pow2
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_pow2) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_int_log2
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_log2) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_int_ispow2
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_ispow2) x)) :=
by
  exact ⟨⟨hx, trivial⟩, ⟨hx, hx⟩⟩

theorem smtTermClosedIn_eo_to_smt_int_div_by_zero
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_mod_by_zero
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_bvnot
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_bvneg
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_bvnego
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_bvredand
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredand) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_bvredor
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_str_len
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_rev
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_to_lower
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_to_upper
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_to_code
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_from_code
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_is_digit
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_to_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_from_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_str_to_re
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_re_mult
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_re_plus
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_re_opt
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_re_comp
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_seq_unit
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_set_singleton
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_set_choose
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_set_is_empty
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_set_is_singleton
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) :=
by
  exact ⟨hx, ⟨hx, trivial⟩⟩

theorem smtTermClosedIn_eo_to_smt_qdiv_by_zero
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) :=
by
  exact ⟨hx, trivial⟩

theorem smtTermClosedIn_eo_to_smt_ubv_to_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_sbv_to_int
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_bvsize
    (vars : List SmtVarKey) (x : Term) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) :=
by
  change SmtTermClosedIn vars
    (native_ite
      (native_zleq 0
        (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
      (SmtTerm._at_purify
        (SmtTerm.Numeral
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
      SmtTerm.None)
  cases native_zleq 0
      (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) <;>
    simp [native_ite, SmtTermClosedIn]

theorem smtTermClosedIn_eo_to_smt_seq_empty
    (vars : List SmtVarKey) (x : Term) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 UserOp1.seq_empty x)) :=
by
  change SmtTermClosedIn vars (__eo_to_smt_seq_empty (__eo_to_smt_type x))
  cases __eo_to_smt_type x <;> trivial

theorem smtTermClosedIn_eo_to_smt_set_empty
    (vars : List SmtVarKey) (x : Term) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 UserOp1.set_empty x)) :=
by
  change SmtTermClosedIn vars (__eo_to_smt_set_empty (__eo_to_smt_type x))
  cases __eo_to_smt_type x <;> trivial

theorem smtTermClosedIn_eo_to_smt_array_deq_diff
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_array_deq_diff x y)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_array_deq_diff (__eo_to_smt x)
      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
      (__smtx_typeof (__eo_to_smt y)))
  generalize hTx : __smtx_typeof (__eo_to_smt x) = Tx
  cases Tx <;> try trivial
  case Map _ _ =>
    generalize hTy : __smtx_typeof (__eo_to_smt y) = Ty
    cases Ty <;> trivial

theorem smtTermClosedIn_eo_to_smt_at_bv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) :=
by
  exact ⟨hy, hx⟩

theorem smtTermClosedIn_eo_to_smt_sets_deq_diff
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_sets_deq_diff x y)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
      (__smtx_typeof (__eo_to_smt y)))
  generalize hTx : __smtx_typeof (__eo_to_smt x) = Tx
  cases Tx <;> try trivial
  case Set _ =>
    generalize hTy : __smtx_typeof (__eo_to_smt y) = Ty
    cases Ty <;> trivial

theorem smtTermClosedIn_eo_to_smt_strings_deq_diff
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_strings_deq_diff x y)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y))
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_strings_stoi_result
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term._at_strings_stoi_result x) y)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.ite (SmtTerm.eq (__eo_to_smt y) (SmtTerm.Numeral 0))
      (SmtTerm.Numeral 0)
      (SmtTerm.str_to_int
        (SmtTerm.str_substr (__eo_to_smt x)
          (SmtTerm.Numeral 0) (__eo_to_smt y))))
  exact ⟨⟨hy, trivial⟩, trivial, ⟨hx, trivial, hy⟩⟩

theorem smtTermClosedIn_eo_to_smt_strings_stoi_non_digit
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_strings_stoi_non_digit x)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.str_indexof_re (__eo_to_smt x)
      (SmtTerm.re_inter SmtTerm.re_allchar
        (SmtTerm.re_comp
          (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
            (SmtTerm.String (native_string_lit "9")))))
      (SmtTerm.Numeral 0))
  exact ⟨hx, ⟨trivial, ⟨trivial, trivial⟩⟩, trivial⟩

theorem smtTermClosedIn_eo_to_smt_strings_itos_result
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term._at_strings_itos_result x) y)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.ite (SmtTerm.eq (__eo_to_smt y) (SmtTerm.Numeral 0))
      (SmtTerm.Numeral 0)
      (SmtTerm.str_to_int
        (SmtTerm.str_substr (SmtTerm.str_from_int (__eo_to_smt x))
          (SmtTerm.Numeral 0) (__eo_to_smt y))))
  exact ⟨⟨hy, trivial⟩, trivial, ⟨hx, trivial, hy⟩⟩

theorem smtTermClosedIn_eo_to_smt_strings_num_occur
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.neg
      (SmtTerm.str_len
        (SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y)
          (SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 1))))
      (SmtTerm.str_len
        (SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y)
          (SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0)))))
  exact
    ⟨⟨hx, hy, hx, trivial, trivial⟩,
      ⟨hx, hy, hx, trivial, trivial⟩⟩

theorem smtTermClosedIn_eo_to_smt_strings_num_occur_re
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply
        (Term.UOp UserOp._at_strings_num_occur_re) x) y)) :=
by
  change SmtTermClosedIn vars
    (SmtTerm.neg
      (SmtTerm.str_len
        (SmtTerm.str_replace_re_all (__eo_to_smt x) (__eo_to_smt y)
          (SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 1))))
      (SmtTerm.str_len
        (SmtTerm.str_replace_re_all (__eo_to_smt x) (__eo_to_smt y)
          (SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0)))))
  exact
    ⟨⟨hx, hy, hx, trivial, trivial⟩,
      ⟨hx, hy, hx, trivial, trivial⟩⟩

theorem smtTermClosedIn_eo_to_smt_strings_occur_index
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply
        (Term.UOp UserOp._at_strings_occur_index) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_strings_occur_index_re
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply
        (Term.UOp UserOp._at_strings_occur_index_re) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_strings_replace_all_result
    {vars : List SmtVarKey} {x y z w : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z))
    (hw : SmtTermClosedIn vars (__eo_to_smt w)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.Apply
        (Term.UOp UserOp._at_strings_replace_all_result) x) y) z) w)) :=
by
  exact ⟨⟨hx, ⟨hx, hy, hw⟩, hx⟩, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_strings_replace_re_all_result
    {vars : List SmtVarKey} {x y z w : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z))
    (hw : SmtTermClosedIn vars (__eo_to_smt w)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.Apply
        (Term.UOp UserOp._at_strings_replace_re_all_result) x) y) z) w)) :=
by
  exact ⟨⟨hx, ⟨hx, hy, hw⟩, hx⟩, hy, hz⟩


theorem smtTermClosedIn_eo_to_smt_witness_string_length
    {vars : List SmtVarKey} {x y z : Term}
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.UOp3 UserOp3._at_witness_string_length x y z)) :=
by
  change SmtTermClosedIn vars
    (native_ite (__eo_to_smt_nat_is_valid y)
      (native_ite (__eo_to_smt_nat_is_valid z)
        (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type x)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type x)))
            (__eo_to_smt y)))
        SmtTerm.None)
      SmtTerm.None)
  cases __eo_to_smt_nat_is_valid y <;> try trivial
  cases __eo_to_smt_nat_is_valid z <;> try trivial
  have hy' :
      SmtTermClosedIn
        ((native_string_lit "@x", __eo_to_smt_type x) :: vars)
        (__eo_to_smt y) :=
    SmtTermClosedIn.weaken_cons hy
  exact ⟨List.Mem.head _, hy'⟩

theorem smtTermClosedIn_eo_to_smt_re_unfold_pos_component
    {vars : List SmtVarKey} :
  ∀ {s r : SmtTerm},
    SmtTermClosedIn vars s ->
      SmtTermClosedIn vars r ->
        ∀ n,
          SmtTermClosedIn vars
            (__eo_to_smt_re_unfold_pos_component s r n) :=
by
  intro s r hs hr n
  induction n generalizing s r with
  | zero =>
      cases r <;> try
        simp [__eo_to_smt_re_unfold_pos_component, SmtTermClosedIn]
      case re_concat r1 r2 =>
        exact
          ⟨hs, hr.1, hr.2⟩
  | succ n ih =>
      cases r <;> try
        simp [__eo_to_smt_re_unfold_pos_component, SmtTermClosedIn]
      case re_concat r1 r2 =>
        let split := SmtTerm.str_indexof_re_split s r1 r2
        have hSplit :
            SmtTermClosedIn vars
              split :=
          ⟨hs, hr.1, hr.2⟩
        have hSuffix :
            SmtTermClosedIn vars
              (SmtTerm.str_substr s
                split
                (SmtTerm.neg (SmtTerm.str_len s) split)) :=
          ⟨hs, hSplit, ⟨hs, hSplit⟩⟩
        simpa [__eo_to_smt_re_unfold_pos_component, split] using
          ih hSuffix hr.2

theorem smtTermClosedIn_eo_to_smt_exists_nil
    {vars : List SmtVarKey} {F : SmtTerm}
    (hF : SmtTermClosedIn vars F) :
  SmtTermClosedIn vars (__eo_to_smt_exists Term.__eo_List_nil F) :=
by
  exact hF

theorem smtTermClosedIn_eo_to_smt_exists_cons
    {vars : List SmtVarKey} {s : native_String} {T : Term}
    {vs : Term} {F : SmtTerm}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs F)) :
  SmtTermClosedIn vars
    (__eo_to_smt_exists
      (Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) vs)
      F) :=
by
  rw [TranslationProofs.eo_to_smt_exists_cons]
  exact hBody

theorem smtTermClosedIn_eo_to_smt_exists_of_env_or_none :
    ∀ {vs : Term} {vars : List SmtVarKey} {F : SmtTerm},
      (∀ {binderVars : List SmtVarKey},
        EoSmtVarEnv vs binderVars ->
          SmtTermClosedIn (binderVars.reverse ++ vars) F) ->
        SmtTermClosedIn vars (__eo_to_smt_exists vs F)
  | Term.__eo_List_nil, vars, F, hBody =>
      by
        simpa using hBody EoSmtVarEnv.nil
  | Term.Apply f x, vars, F, hBody =>
      by
        cases f <;> try trivial
        case Apply g y =>
          cases g <;> try trivial
          case __eo_List_cons =>
            cases y <;> try trivial
            case Var name T =>
              cases name <;> try trivial
              case String s =>
                exact smtTermClosedIn_eo_to_smt_exists_cons
                  (s := s) (T := T)
                  (smtTermClosedIn_eo_to_smt_exists_of_env_or_none
                    (vs := x) (vars := (s, __eo_to_smt_type T) :: vars)
                    (F := F)
                    (by
                      intro binderVars hVs
                      simpa [List.reverse_cons, List.append_assoc]
                        using hBody (EoSmtVarEnv.cons hVs)))
  | Term.UOp _, vars, F, hBody => by trivial
  | Term.UOp1 _ _, vars, F, hBody => by trivial
  | Term.UOp2 _ _ _, vars, F, hBody => by trivial
  | Term.UOp3 _ _ _ _, vars, F, hBody => by trivial
  | Term.__eo_List, vars, F, hBody => by trivial
  | Term.__eo_List_cons, vars, F, hBody => by trivial
  | Term.Bool, vars, F, hBody => by trivial
  | Term.Boolean _, vars, F, hBody => by trivial
  | Term.Numeral _, vars, F, hBody => by trivial
  | Term.Rational _, vars, F, hBody => by trivial
  | Term.String _, vars, F, hBody => by trivial
  | Term.Binary _ _, vars, F, hBody => by trivial
  | Term.Type, vars, F, hBody => by trivial
  | Term.Stuck, vars, F, hBody => by trivial
  | Term.FunType, vars, F, hBody => by trivial
  | Term.Var _ _, vars, F, hBody => by trivial
  | Term.DatatypeType _ _, vars, F, hBody => by trivial
  | Term.DatatypeTypeRef _, vars, F, hBody => by trivial
  | Term.DtcAppType _ _, vars, F, hBody => by trivial
  | Term.DtCons _ _ _, vars, F, hBody => by trivial
  | Term.DtSel _ _ _ _, vars, F, hBody => by trivial
  | Term.USort _, vars, F, hBody => by trivial
  | Term.UConst _ _, vars, F, hBody => by trivial

theorem smtTermClosedIn_eo_to_smt_exists_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {F : SmtTerm},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) F ->
          SmtTermClosedIn vars (__eo_to_smt_exists vs F)
  | _, _, _, _, EoSmtVarEnv.nil, hF =>
      by
        simpa using hF
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hF =>
      by
        exact smtTermClosedIn_eo_to_smt_exists_cons
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env hTail (by
            simpa [List.reverse_cons, List.append_assoc] using hF))

/-- Inversion of `__eo_to_smt_exists` closedness: if the fully-quantified body
is closed in `vars`, then the inner body `F` is closed once the (deterministic)
binder keys `bv` of `vs` are prepended. -/
theorem smtTermClosedIn_eo_to_smt_exists_env_of :
    ∀ {vs : Term} {vars bv : List SmtVarKey} {F : SmtTerm},
      EoSmtVarEnv vs bv ->
        SmtTermClosedIn vars (__eo_to_smt_exists vs F) ->
          SmtTermClosedIn (bv.reverse ++ vars) F
  | _, _, _, F, EoSmtVarEnv.nil, h => by simpa using h
  | _, vars, _, F, @EoSmtVarEnv.cons s T env vars0 hEnv, h => by
      have h' :
          SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
            (__eo_to_smt_exists env F) := h
      have hIH := smtTermClosedIn_eo_to_smt_exists_env_of hEnv h'
      simpa [List.reverse_cons, List.append_assoc] using hIH

/-- Closedness of the skolemization output.  The hypothesis is the environment
form: for the (deterministic) binder keys `bv` of `vs`, the body `G` is closed
with those keys prepended. -/
theorem smtTermClosedIn_eo_to_smt_quantifiers_skolemize :
    ∀ {vs : Term} {G : SmtTerm} {n : native_Nat} {vars : List SmtVarKey},
      (∀ {bv : List SmtVarKey},
        EoSmtVarEnv vs bv -> SmtTermClosedIn (bv.reverse ++ vars) G) ->
        SmtTermClosedIn vars (__eo_to_smt_quantifiers_skolemize vs G n)
  | Term.Apply f x, G, n, vars, hEnv => by
      cases f <;> try trivial
      case Apply g y =>
        cases g <;> try trivial
        case __eo_List_cons =>
          cases y <;> try trivial
          case Var name T =>
            cases name <;> try trivial
            case String s =>
              cases n with
              | zero =>
                  show SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
                    (__eo_to_smt_exists x G)
                  apply smtTermClosedIn_eo_to_smt_exists_of_env_or_none
                  intro bv2 hbv2
                  have h := hEnv (EoSmtVarEnv.cons hbv2)
                  simpa [List.reverse_cons, List.append_assoc] using h
              | succ n' =>
                  show SmtTermClosedIn vars
                    (__eo_to_smt_quantifiers_skolemize x
                      (SmtTerm.bind s (__eo_to_smt_type T)
                        (SmtTerm.choice s (__eo_to_smt_type T)
                          (__eo_to_smt_exists x G)) G) n')
                  apply smtTermClosedIn_eo_to_smt_quantifiers_skolemize (vs := x)
                  intro bv2 hbv2
                  refine ⟨?_, ?_⟩
                  · show SmtTermClosedIn
                      ((s, __eo_to_smt_type T) :: (bv2.reverse ++ vars))
                      (__eo_to_smt_exists x G)
                    apply smtTermClosedIn_eo_to_smt_exists_of_env_or_none
                    intro bv3 hbv3
                    have h := hEnv (EoSmtVarEnv.cons hbv3)
                    refine SmtTermClosedIn.mono ?_ (by
                      simpa [List.reverse_cons, List.append_assoc] using h)
                    intro a b hMem
                    simp only [List.mem_append, List.mem_cons,
                      List.mem_reverse] at hMem ⊢
                    rcases hMem with h | h | h <;> simp [h]
                  · have h := hEnv (EoSmtVarEnv.cons hbv2)
                    refine SmtTermClosedIn.mono ?_ (by
                      simpa [List.reverse_cons, List.append_assoc] using h)
                    intro a b hMem
                    simp only [List.mem_append, List.mem_cons,
                      List.mem_reverse] at hMem ⊢
                    rcases hMem with h | h | h <;> simp [h]
  | Term.__eo_List_nil, G, n, vars, hEnv => by trivial
  | Term.UOp _, G, n, vars, hEnv => by trivial
  | Term.UOp1 _ _, G, n, vars, hEnv => by trivial
  | Term.UOp2 _ _ _, G, n, vars, hEnv => by trivial
  | Term.UOp3 _ _ _ _, G, n, vars, hEnv => by trivial
  | Term.__eo_List, G, n, vars, hEnv => by trivial
  | Term.__eo_List_cons, G, n, vars, hEnv => by trivial
  | Term.Bool, G, n, vars, hEnv => by trivial
  | Term.Boolean _, G, n, vars, hEnv => by trivial
  | Term.Numeral _, G, n, vars, hEnv => by trivial
  | Term.Rational _, G, n, vars, hEnv => by trivial
  | Term.String _, G, n, vars, hEnv => by trivial
  | Term.Binary _ _, G, n, vars, hEnv => by trivial
  | Term.Type, G, n, vars, hEnv => by trivial
  | Term.Stuck, G, n, vars, hEnv => by trivial
  | Term.FunType, G, n, vars, hEnv => by trivial
  | Term.Var _ _, G, n, vars, hEnv => by trivial
  | Term.DatatypeType _ _, G, n, vars, hEnv => by trivial
  | Term.DatatypeTypeRef _, G, n, vars, hEnv => by trivial
  | Term.DtcAppType _ _, G, n, vars, hEnv => by trivial
  | Term.DtCons _ _ _, G, n, vars, hEnv => by trivial
  | Term.DtSel _ _ _ _, G, n, vars, hEnv => by trivial
  | Term.USort _, G, n, vars, hEnv => by trivial
  | Term.UConst _ _, G, n, vars, hEnv => by trivial

theorem smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall
    {vars : List SmtVarKey} {xs body idx : Term}
    (hForall :
      SmtTermClosedIn vars
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx)) :=
by
  change SmtTermClosedIn vars
    (native_ite (__eo_to_smt_nat_is_valid idx)
      (__eo_to_smt_quantifiers_skolemize xs (SmtTerm.not (__eo_to_smt body))
        (__eo_to_smt_nat idx))
      SmtTerm.None)
  cases __eo_to_smt_nat_is_valid idx
  · simp [native_ite, SmtTermClosedIn]
  · simp [native_ite]
    cases xs
    case __eo_List_nil =>
      simp [__eo_to_smt_quantifiers_skolemize, SmtTermClosedIn]
    all_goals
      apply smtTermClosedIn_eo_to_smt_quantifiers_skolemize
      intro bv hbv
      change SmtTermClosedIn vars
        (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body))) at hForall
      exact smtTermClosedIn_eo_to_smt_exists_env_of hbv hForall

theorem smtTermClosedIn_eo_to_smt_tuple_select_smt
    {vars : List SmtVarKey} (T : SmtType) {n t : SmtTerm}
    (hn : SmtTermClosedIn vars n)
    (ht : SmtTermClosedIn vars t) :
  SmtTermClosedIn vars (__eo_to_smt_tuple_select T n t) :=
by
  cases T <;> try trivial
  case Datatype s dd =>
    cases dd <;> try trivial
    case cons s2 d dd2 =>
      cases dd2 <;> try trivial
      cases n <;> try trivial
      case nil.Numeral i =>
        change SmtTermClosedIn vars
          (native_ite
            (native_and
              (native_and (native_streq s (native_string_lit "@Tuple"))
                (native_streq s2 (native_string_lit "@Tuple")))
              (native_zleq 0 i))
            (SmtTerm.Apply
              (SmtTerm.DtSel (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl d) native_nat_zero
                (native_int_to_nat i))
              t)
            SmtTerm.None)
        cases native_and
            (native_and (native_streq s (native_string_lit "@Tuple"))
              (native_streq s2 (native_string_lit "@Tuple")))
            (native_zleq 0 i) <;>
          simp [native_ite, SmtTermClosedIn, ht]

theorem smtTermClosedIn_eo_to_smt_is
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is x) y)) :=
by
  exact ⟨smtTermClosedIn_eo_to_smt_tester, hy⟩

theorem smtTermClosedIn_eo_to_smt_tuple_select
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select x) y)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt y))
      (__eo_to_smt x) (__eo_to_smt y))
  exact smtTermClosedIn_eo_to_smt_tuple_select_smt
    (__smtx_typeof (__eo_to_smt y)) hx hy

theorem smtTermClosedIn_eo_to_smt_updater_rec
    {vars : List SmtVarKey} {sel t u acc : SmtTerm}
    (ht : SmtTermClosedIn vars t)
    (hu : SmtTermClosedIn vars u)
    (hAcc : SmtTermClosedIn vars acc) :
  ∀ n, SmtTermClosedIn vars
    (__eo_to_smt_updater_rec sel n t u acc) :=
by
  intro n
  induction n generalizing acc with
  | zero =>
      cases sel <;>
        simp [__eo_to_smt_updater_rec, SmtTermClosedIn, hAcc]
  | succ n ih =>
      cases sel <;>
        simp [__eo_to_smt_updater_rec, SmtTermClosedIn]
      case DtSel s d i m =>
        change SmtTermClosedIn vars
          (SmtTerm.Apply
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u acc)
            (native_ite (native_nateq m n) u
              (SmtTerm.Apply (SmtTerm.DtSel s d i n) t)))
        constructor
        · exact ih hAcc
        · cases native_nateq m n <;>
            simp [native_ite, SmtTermClosedIn, ht, hu]

theorem smtTermClosedIn_eo_to_smt_updater
    {vars : List SmtVarKey} {sel t u : SmtTerm}
    (ht : SmtTermClosedIn vars t)
    (hu : SmtTermClosedIn vars u) :
  SmtTermClosedIn vars (__eo_to_smt_updater sel t u) :=
by
  cases sel <;> try
    simp [__eo_to_smt_updater, SmtTermClosedIn]
  case DtSel s d i m =>
    change SmtTermClosedIn vars
      (native_ite
        (native_zlt (native_nat_to_int m)
          (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)))
        (SmtTerm.ite (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m)
            (__smtx_dt_num_sels (__smtx_dd_lookup s d) i) t u (SmtTerm.DtCons s d i))
          t)
        SmtTerm.None)
    cases native_zlt (native_nat_to_int m)
        (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) <;> try trivial
    exact
      ⟨⟨trivial, ht⟩,
        smtTermClosedIn_eo_to_smt_updater_rec ht hu
          (by
            exact
              (trivial :
                SmtTermClosedIn vars (SmtTerm.DtCons s d i)))
          (__smtx_dt_num_sels (__smtx_dd_lookup s d) i),
        ht⟩

theorem smtTermClosedIn_eo_to_smt_update
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update x) y) z)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_updater (__eo_to_smt x) (__eo_to_smt y)
      (__eo_to_smt z))
  exact smtTermClosedIn_eo_to_smt_updater hy hz

theorem smtTermClosedIn_eo_to_smt_tuple_update_smt
    {vars : List SmtVarKey} (T : SmtType) {n t u : SmtTerm}
    (hn : SmtTermClosedIn vars n)
    (ht : SmtTermClosedIn vars t)
    (hu : SmtTermClosedIn vars u) :
  SmtTermClosedIn vars (__eo_to_smt_tuple_update T n t u) :=
by
  cases T <;> try trivial
  case Datatype s dd =>
    cases dd <;> try trivial
    case cons s2 d dd2 =>
      cases dd2 <;> try trivial
      cases n <;> try trivial
      case nil.Numeral i =>
        change SmtTermClosedIn vars
          (native_ite
            (native_and
              (native_and (native_streq s (native_string_lit "@Tuple"))
                (native_streq s2 (native_string_lit "@Tuple")))
              (native_zleq 0 i))
            (__eo_to_smt_updater
              (SmtTerm.DtSel (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl d)
                native_nat_zero (native_int_to_nat i))
              t u)
            SmtTerm.None)
        cases native_and
            (native_and (native_streq s (native_string_lit "@Tuple"))
              (native_streq s2 (native_string_lit "@Tuple")))
            (native_zleq 0 i) <;> try trivial
        simpa [native_ite] using
          smtTermClosedIn_eo_to_smt_updater
            (sel := SmtTerm.DtSel (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl d)
              native_nat_zero (native_int_to_nat i))
            ht hu

theorem smtTermClosedIn_eo_to_smt_tuple_update
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update x) y) z)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt y))
      (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
  exact smtTermClosedIn_eo_to_smt_tuple_update_smt
    (__smtx_typeof (__eo_to_smt y)) hx hy hz

theorem smtTermClosedIn_eo_to_smt_tuple_prepend_rec
    {vars : List SmtVarKey} {dd : SmtDatatypeDecl} {d : SmtDatatype} {tail acc : SmtTerm}
    (hTail : SmtTermClosedIn vars tail)
    (hAcc : SmtTermClosedIn vars acc) :
  ∀ n,
    SmtTermClosedIn vars (__eo_to_smt_tuple_prepend_rec dd d tail n acc) :=
by
  intro n
  induction n generalizing acc with
  | zero =>
      exact hAcc
  | succ n ih =>
      exact ⟨ih hAcc, ⟨trivial, hTail⟩⟩

theorem smtTermClosedIn_eo_to_smt_tuple_prepend_of_type
    {vars : List SmtVarKey} (T hT : SmtType) {h tail : SmtTerm}
    (hHead : SmtTermClosedIn vars h)
    (hTail : SmtTermClosedIn vars tail) :
  SmtTermClosedIn vars (__eo_to_smt_tuple_prepend_of_type T h hT tail) :=
by
  cases T <;> try trivial
  case Datatype s dd =>
    cases dd <;> try trivial
    case cons s2 d dd2 =>
      cases d <;> try trivial
      case sum c rest =>
        cases rest <;> try trivial
        cases dd2 <;> try trivial
        change SmtTermClosedIn vars
          (native_ite
            (native_and
              (native_and (native_streq s (native_string_lit "@Tuple"))
                (native_streq s2 (native_string_lit "@Tuple")))
              (__smtx_type_wf
                (SmtType.Datatype (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                      SmtDatatype.null)))))
            (__eo_to_smt_tuple_prepend_rec
              (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null))
              (SmtDatatype.sum c SmtDatatype.null)
              tail (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
                native_nat_zero)
              (SmtTerm.Apply
                (SmtTerm.DtCons (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                      SmtDatatype.null))
                  native_nat_zero)
                h))
            SmtTerm.None)
        cases native_and
            (native_and (native_streq s (native_string_lit "@Tuple"))
              (native_streq s2 (native_string_lit "@Tuple")))
            (__smtx_type_wf
              (SmtType.Datatype (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl
                  (SmtDatatype.sum (SmtDatatypeCons.cons hT c)
                    SmtDatatype.null)))) <;> try trivial
        exact smtTermClosedIn_eo_to_smt_tuple_prepend_rec
          (tail := tail)
          (acc := SmtTerm.Apply
            (SmtTerm.DtCons (native_string_lit "@Tuple")
              (__eo_to_smt_tuple_decl
                (SmtDatatype.sum (SmtDatatypeCons.cons hT c) SmtDatatype.null))
              native_nat_zero)
            h)
          hTail (by exact ⟨trivial, hHead⟩)
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)

theorem smtTermClosedIn_eo_to_smt_tuple_prepend
    {vars : List SmtVarKey} {h tail : SmtTerm} (hT : SmtType)
    (hHead : SmtTermClosedIn vars h)
    (hTail : SmtTermClosedIn vars tail) :
  SmtTermClosedIn vars (__eo_to_smt_tuple_prepend h hT tail) :=
by
  exact smtTermClosedIn_eo_to_smt_tuple_prepend_of_type
    (__smtx_typeof tail) hT hHead hTail

theorem smtTermClosedIn_eo_to_smt_tuple
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)) :=
by
  change SmtTermClosedIn vars
    (__eo_to_smt_tuple_prepend (__eo_to_smt x)
      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y))
  exact smtTermClosedIn_eo_to_smt_tuple_prepend
    (__smtx_typeof (__eo_to_smt x)) hx hy

theorem smtTermClosedIn_eo_to_smt_and
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_or
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_imp
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_xor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_eq
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_plus
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_neg
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_mult
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_lt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_leq
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_gt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_geq
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_div
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_mod
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_divisible
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_div_total
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_mod_total
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_select
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_concat
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvand
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvnand
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvnor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvxor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvxnor
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvcomp
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvadd
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvmul
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvudiv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvurem
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsub
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsdiv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsrem
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsmod
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvult
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvule
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvugt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvuge
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvslt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsle
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsgt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsge
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvshl
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvlshr
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvashr
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvuaddo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsaddo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvumulo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsmulo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvusubo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvssubo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvsdivo
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_bvultbv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y)) :=
by
  exact ⟨⟨hx, hy⟩, trivial, trivial⟩

theorem smtTermClosedIn_eo_to_smt_bvsltbv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y)) :=
by
  exact ⟨⟨hx, hy⟩, trivial, trivial⟩

theorem smtTermClosedIn_eo_to_smt_from_bools
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)) :=
by
  exact ⟨hy, hx, trivial, trivial⟩

theorem smtTermClosedIn_eo_to_smt_str_concat
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_contains
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_at
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_prefixof
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_suffixof
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_lt
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_leq
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_re_range
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_re_concat
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_re_inter
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_re_union
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_re_diff
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_str_in_re
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_seq_nth
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_union
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_inter
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_minus
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_member
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_subset
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using :
    ∀ {xs : Term} {base : SmtTerm} {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnvPerm env vars ->
        (∀ {t env' : Term} {vars' : List SmtVarKey},
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t)) ->
          __eo_is_closed_rec xs env = Term.Boolean true ->
            SmtTermClosedIn vars base ->
              SmtTermClosedIn vars (__eo_to_smt_set_insert xs base)
  | Term.__eo_List_nil, base, env, vars, hEnv, hRec, hClosed, hBase =>
      by trivial
  | Term.Apply f tail, base, env, vars, hEnv, hRec, hClosed, hBase =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case _at__at_TypedList_nil =>
            cases hTy :
                native_Teq (__smtx_typeof base)
                  (SmtType.Set (__eo_to_smt_type tail))
            · simp [__eo_to_smt_set_insert, hTy, native_ite]
              change True
              trivial
            · simpa [__eo_to_smt_set_insert, hTy, native_ite] using hBase
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              change SmtTermClosedIn vars
                (SmtTerm.set_union
                  (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail base))
              exact
                ⟨hRec hEnv hCases.1,
                  smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using
                    hEnv hRec hCases.2 hBase⟩
  | Term.UOp _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.UOp1 _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.UOp2 _ _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.UOp3 _ _ _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.__eo_List, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.__eo_List_cons, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Bool, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Boolean _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Numeral _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Rational _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.String _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Binary _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Type, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Stuck, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.FunType, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.Var _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.DatatypeType _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.DatatypeTypeRef _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.DtcAppType _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.DtCons _ _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.DtSel _ _ _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.USort _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial
  | Term.UConst _ _, base, env, vars, hEnv, hRec, hClosed, hBase => by trivial

theorem smtTermClosedIn_eo_to_smt_distinct_pairs_rec_of_closed_rec_using :
    ∀ {xs : Term} {s : SmtTerm} {env : Term} {vars : List SmtVarKey},
      SmtTermClosedIn vars s ->
        EoSmtVarEnvPerm env vars ->
          (∀ {t env' : Term} {vars' : List SmtVarKey},
            EoSmtVarEnvPerm env' vars' ->
              __eo_is_closed_rec t env' = Term.Boolean true ->
                SmtTermClosedIn vars' (__eo_to_smt t)) ->
            __eo_is_closed_rec xs env = Term.Boolean true ->
              SmtTermClosedIn vars (__eo_to_smt_distinct_pairs s xs)
  | Term.Apply f tail, s, env, vars, hs, hEnv, hRec, hClosed =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                  (__eo_to_smt_distinct_pairs s tail))
              exact
                ⟨⟨hs, hRec hEnv hCases.1⟩,
                  smtTermClosedIn_eo_to_smt_distinct_pairs_rec_of_closed_rec_using
                    hs hEnv hRec hCases.2⟩
  | Term.UOp _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.UOp1 _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.UOp2 _ _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.UOp3 _ _ _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List_nil, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List_cons, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Bool, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Boolean _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Numeral _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Rational _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.String _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Binary _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Type, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Stuck, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.FunType, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.Var _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.DatatypeType _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.DatatypeTypeRef _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.DtcAppType _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.DtCons _ _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.DtSel _ _ _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.USort _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial
  | Term.UConst _ _, s, env, vars, hs, hEnv, hRec, hClosed => by trivial

theorem smtTermClosedIn_eo_to_smt_distinct_rec_of_closed_rec_using :
    ∀ {xs env : Term} {vars : List SmtVarKey},
      EoSmtVarEnvPerm env vars ->
        (∀ {t env' : Term} {vars' : List SmtVarKey},
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t)) ->
          __eo_is_closed_rec xs env = Term.Boolean true ->
            SmtTermClosedIn vars (__eo_to_smt_distinct xs)
  | Term.Apply f tail, env, vars, hEnv, hRec, hClosed =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              have hHead := hRec hEnv hCases.1
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                  (__eo_to_smt_distinct tail))
              exact
                ⟨smtTermClosedIn_eo_to_smt_distinct_pairs_rec_of_closed_rec_using
                    hHead hEnv hRec hCases.2,
                  smtTermClosedIn_eo_to_smt_distinct_rec_of_closed_rec_using
                    hEnv hRec hCases.2⟩
  | Term.UOp _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.UOp1 _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.UOp2 _ _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.UOp3 _ _ _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List_nil, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.__eo_List_cons, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Bool, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Boolean _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Numeral _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Rational _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.String _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Binary _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Type, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Stuck, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.FunType, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.Var _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.DatatypeType _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.DatatypeTypeRef _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.DtcAppType _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.DtCons _ _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.DtSel _ _ _ _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.USort _, env, vars, hEnv, hRec, hClosed => by trivial
  | Term.UConst _ _, env, vars, hEnv, hRec, hClosed => by trivial

theorem smtTermClosedIn_eo_to_smt_set_insert_rec_below
    (root : Term)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t)) :
    ∀ {xs : Term} {base : SmtTerm} {env : Term} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        EoSmtVarEnvPerm env vars ->
          __eo_is_closed_rec xs env = Term.Boolean true ->
            SmtTermClosedIn vars base ->
              SmtTermClosedIn vars (__eo_to_smt_set_insert xs base)
  | Term.__eo_List_nil, base, env, vars, hLt, hEnv, hClosed, hBase =>
      by trivial
  | Term.Apply f tail, base, env, vars, hLt, hEnv, hClosed, hBase =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case _at__at_TypedList_nil =>
            cases hTy :
                native_Teq (__smtx_typeof base)
                  (SmtType.Set (__eo_to_smt_type tail))
            · simp [__eo_to_smt_set_insert, hTy, native_ite]
              change True
              trivial
            · simpa [__eo_to_smt_set_insert, hTy, native_ite] using hBase
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              change SmtTermClosedIn vars
                (SmtTerm.set_union
                  (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail base))
              exact
                ⟨hRec hHeadLt hEnv hCases.1,
                  smtTermClosedIn_eo_to_smt_set_insert_rec_below root hRec
                    hTailLt hEnv hCases.2 hBase⟩
  | Term.UOp _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.UOp1 _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.UOp2 _ _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.UOp3 _ _ _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.__eo_List, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.__eo_List_cons, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Bool, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Boolean _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Numeral _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Rational _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.String _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Binary _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Type, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Stuck, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.FunType, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.Var _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.DatatypeType _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.DatatypeTypeRef _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.DtcAppType _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.DtCons _ _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.DtSel _ _ _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.USort _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial
  | Term.UConst _ _, base, env, vars, hLt, hEnv, hClosed, hBase => by trivial

theorem smtTermClosedIn_eo_to_smt_distinct_pairs_rec_below
    (root : Term)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t)) :
    ∀ {xs : Term} {s : SmtTerm} {env : Term} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        SmtTermClosedIn vars s ->
          EoSmtVarEnvPerm env vars ->
            __eo_is_closed_rec xs env = Term.Boolean true ->
              SmtTermClosedIn vars (__eo_to_smt_distinct_pairs s xs)
  | Term.Apply f tail, s, env, vars, hLt, hs, hEnv, hClosed =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                  (__eo_to_smt_distinct_pairs s tail))
              exact
                ⟨⟨hs, hRec hHeadLt hEnv hCases.1⟩,
                  smtTermClosedIn_eo_to_smt_distinct_pairs_rec_below root hRec
                    hTailLt hs hEnv hCases.2⟩
  | Term.UOp _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.UOp1 _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.UOp2 _ _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.UOp3 _ _ _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.__eo_List, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.__eo_List_nil, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.__eo_List_cons, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Bool, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Boolean _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Numeral _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Rational _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.String _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Binary _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Type, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Stuck, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.FunType, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.Var _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.DatatypeType _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.DatatypeTypeRef _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.DtcAppType _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.DtCons _ _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.DtSel _ _ _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.USort _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial
  | Term.UConst _ _, s, env, vars, hLt, hs, hEnv, hClosed => by trivial

theorem smtTermClosedIn_eo_to_smt_distinct_rec_below
    (root : Term)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t)) :
    ∀ {xs env : Term} {vars : List SmtVarKey},
      sizeOf xs < sizeOf root ->
        EoSmtVarEnvPerm env vars ->
          __eo_is_closed_rec xs env = Term.Boolean true ->
            SmtTermClosedIn vars (__eo_to_smt_distinct xs)
  | Term.Apply f tail, env, vars, hLt, hEnv, hClosed =>
      by
        cases f <;> try trivial
        case UOp op =>
          cases op <;> trivial
        case Apply g head =>
          cases g <;> try trivial
          case UOp op =>
            cases op <;> try trivial
            case _at__at_TypedList_cons =>
              have hCases :=
                eo_is_closed_rec_binary_uop_eq_true_cases
                  (op := UserOp._at__at_TypedList_cons)
                  (by decide) (by decide) hEnv hClosed
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              have hHead := hRec hHeadLt hEnv hCases.1
              change SmtTermClosedIn vars
                (SmtTerm.and
                  (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                  (__eo_to_smt_distinct tail))
              exact
                ⟨smtTermClosedIn_eo_to_smt_distinct_pairs_rec_below root hRec
                    hTailLt hHead hEnv hCases.2,
                  smtTermClosedIn_eo_to_smt_distinct_rec_below root hRec
                    hTailLt hEnv hCases.2⟩
  | Term.UOp _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.UOp1 _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.UOp2 _ _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.UOp3 _ _ _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.__eo_List, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.__eo_List_nil, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.__eo_List_cons, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Bool, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Boolean _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Numeral _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Rational _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.String _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Binary _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Type, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Stuck, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.FunType, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.Var _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.DatatypeType _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.DatatypeTypeRef _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.DtcAppType _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.DtCons _ _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.DtSel _ _ _ _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.USort _, env, vars, hLt, hEnv, hClosed => by trivial
  | Term.UConst _ _, env, vars, hLt, hEnv, hClosed => by trivial

theorem smtTermClosedIn_eo_to_smt_qdiv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_qdiv_total
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_ite
    {vars : List SmtVarKey} {c x y : Term}
    (hc : SmtTermClosedIn vars (__eo_to_smt c))
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :=
by
  exact ⟨hc, hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_store
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_bvite
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z)) :=
by
  exact ⟨⟨hx, trivial⟩, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_substr
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_replace
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_indexof
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_update
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_replace_all
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_replace_re
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_replace_re_all
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_str_indexof_re
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_not_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  exact smtTermClosedIn_eo_to_smt_not
    (hRec hEnv
      (eo_is_closed_rec_apply_uop_arg_eq_true hEnv hClosed))

theorem smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
    {f x env : Term} {vars : List SmtVarKey}
    (hSmt :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecF :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec f env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt f))
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.Apply f x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply f x)) :=
by
  have hCases :=
    eo_is_closed_rec_apply_eq_true_cases_of_not_quantifier
      hNotForall hNotExists hEnv hClosed
  rw [hSmt]
  exact ⟨hRecF hEnv hCases.1, hRecX hEnv hCases.2⟩

theorem smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp op) x)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  exact hBuilder
    (hRec hEnv (eo_is_closed_rec_apply_uop_arg_eq_true hEnv hClosed))

theorem smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  have hCases :=
    eo_is_closed_rec_binary_uop_eq_true_cases
      hNotForall hNotExists hEnv hClosed
  exact hBuilder (hRecX hEnv hCases.1) (hRecY hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt z) ->
            SmtTermClosedIn vars
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)) :=
by
  have hCases :=
    eo_is_closed_rec_ternary_uop_eq_true_cases
      hNotForall hNotExists hEnv hClosed
  exact hBuilder
    (hRecX hEnv hCases.1)
    (hRecY hEnv hCases.2.1)
    (hRecZ hEnv hCases.2.2)

theorem smtTermClosedIn_eo_to_smt_quaternary_uop_of_closed_rec_using
    {op : UserOp} {w x y z env : Term} {vars : List SmtVarKey}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt w) ->
        SmtTermClosedIn vars (__eo_to_smt x) ->
          SmtTermClosedIn vars (__eo_to_smt y) ->
            SmtTermClosedIn vars (__eo_to_smt z) ->
              SmtTermClosedIn vars
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.Apply (Term.UOp op) w) x) y) z)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecW :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec w env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt w))
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) x) y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) x) y) z)) :=
by
  have hCases :=
    eo_is_closed_rec_quaternary_uop_eq_true_cases
      hNotForall hNotExists hEnv hClosed
  exact hBuilder
    (hRecW hEnv hCases.1)
    (hRecX hEnv hCases.2.1)
    (hRecY hEnv hCases.2.2.1)
    (hRecZ hEnv hCases.2.2.2)

theorem smtTermClosedIn_eo_to_smt_ite_of_closed_rec_using
    {c x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecC :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec c env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt c))
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
    (op := UserOp.ite) (by decide) (by decide)
    (fun hc hx hy => smtTermClosedIn_eo_to_smt_ite hc hx hy)
    hEnv hRecC hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_uop1_of_closed_rec_using
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 op x)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 op x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 op x)) :=
by
  exact hBuilder
    (hRec hEnv (eo_is_closed_rec_uop1_eq_true hEnv hClosed))

theorem smtTermClosedIn_eo_to_smt_uop2_of_closed_rec_using
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt (Term.UOp2 op x y)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp2 op x y)) :=
by
  have hCases := eo_is_closed_rec_uop2_eq_true_cases hEnv hClosed
  exact hBuilder (hRecX hEnv hCases.1) (hRecY hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_uop3_of_closed_rec_using
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt z) ->
            SmtTermClosedIn vars (__eo_to_smt (Term.UOp3 op x y z)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp3 op x y z)) :=
by
  have hCases := eo_is_closed_rec_uop3_eq_true_cases hEnv hClosed
  exact hBuilder
    (hRecX hEnv hCases.1)
    (hRecY hEnv hCases.2.1)
    (hRecZ hEnv hCases.2.2)

theorem smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    {op : UserOp1} {x y env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 op x) y)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 op x) y)) :=
by
  have hCases := eo_is_closed_rec_apply_uop1_eq_true_cases hEnv hClosed
  exact hBuilder (hRecX hEnv hCases.1) (hRecY hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_apply_uop2_of_closed_rec_using
    {op : UserOp2} {x y z env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt z) ->
            SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp2 op x y) z)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op x y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp2 op x y) z)) :=
by
  have hCases := eo_is_closed_rec_apply_uop2_eq_true_cases hEnv hClosed
  exact hBuilder
    (hRecX hEnv hCases.1)
    (hRecY hEnv hCases.2.1)
    (hRecZ hEnv hCases.2.2)

theorem smtTermClosedIn_eo_to_smt_apply_apply_uop1_of_closed_rec_using
    {op : UserOp1} {x y z env : Term} {vars : List SmtVarKey}
    (hBuilder :
      SmtTermClosedIn vars (__eo_to_smt x) ->
        SmtTermClosedIn vars (__eo_to_smt y) ->
          SmtTermClosedIn vars (__eo_to_smt z) ->
            SmtTermClosedIn vars
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp1 op x) y) z)))
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op x) y) z)) :=
by
  have hCases :=
    eo_is_closed_rec_apply_apply_uop1_eq_true_cases hEnv hClosed
  exact hBuilder
    (hRecX hEnv hCases.1)
    (hRecY hEnv hCases.2.1)
    (hRecZ hEnv hCases.2.2)

theorem smtTermClosedIn_eo_to_smt_int_to_bv
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_repeat
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_zero_extend
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_sign_extend
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_rotate_left
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_rotate_right
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_at_bit
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit x) y)) :=
by
  exact ⟨⟨hx, hx, hy⟩, trivial⟩

theorem smtTermClosedIn_eo_to_smt_re_exp
    {vars : List SmtVarKey} {x y : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp x) y)) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_eo_to_smt_extract
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract x y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_re_loop
    {vars : List SmtVarKey} {x y z : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x))
    (hy : SmtTermClosedIn vars (__eo_to_smt y))
    (hz : SmtTermClosedIn vars (__eo_to_smt z)) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop x y) z)) :=
by
  exact ⟨hx, hy, hz⟩

theorem smtTermClosedIn_eo_to_smt_purify
    {vars : List SmtVarKey} {x : Term}
    (hx : SmtTermClosedIn vars (__eo_to_smt x)) :
  SmtTermClosedIn vars (__eo_to_smt (Term._at_purify x)) :=
by
  exact hx

theorem smtTermClosedIn_eo_to_smt_purify_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term._at_purify x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term._at_purify x)) :=
by
  exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
    (op := UserOp._at_purify)
    (fun hx => smtTermClosedIn_eo_to_smt_purify hx)
    hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_bvsize_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_bvsize) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) :=
by
  exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
    (op := UserOp._at_bvsize)
    (fun _ => smtTermClosedIn_eo_to_smt_bvsize vars x)
    hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_seq_empty_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 UserOp1.seq_empty x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 UserOp1.seq_empty x)) :=
by
  exact smtTermClosedIn_eo_to_smt_uop1_of_closed_rec_using
    (op := UserOp1.seq_empty)
    (fun _ => smtTermClosedIn_eo_to_smt_seq_empty vars x)
    hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_set_empty_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 UserOp1.set_empty x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 UserOp1.set_empty x)) :=
by
  exact smtTermClosedIn_eo_to_smt_uop1_of_closed_rec_using
    (op := UserOp1.set_empty)
    (fun _ => smtTermClosedIn_eo_to_smt_set_empty vars x)
    hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_set_insert_of_closed_rec_using
    {xs x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)) :=
by
  have hCases :=
    eo_is_closed_rec_binary_uop_eq_true_cases
      (op := UserOp.set_insert) (by decide) (by decide)
      hEnv hClosed
  cases xs
  case Apply f arg =>
    cases f
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        exact smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using
          hEnv hRec hCases.1 (hRec hEnv hCases.2)
      all_goals
        exact smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using
          hEnv hRec hCases.1 (hRec hEnv hCases.2)
    all_goals
      exact smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using
        hEnv hRec hCases.1 (hRec hEnv hCases.2)
  all_goals
    exact smtTermClosedIn_eo_to_smt_set_insert_rec_of_closed_rec_using
      hEnv hRec hCases.1 (hRec hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_distinct_of_closed_rec_using
    {xs env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.distinct) xs) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) :=
by
  have hXs :=
    eo_is_closed_rec_apply_uop_arg_eq_true
      (op := UserOp.distinct) hEnv hClosed
  change SmtTermClosedIn vars
    (native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs))
  cases native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None <;>
    try trivial
  simpa [native_ite] using
    smtTermClosedIn_eo_to_smt_distinct_rec_of_closed_rec_using
      hEnv hRec hXs

theorem smtTermClosedIn_eo_to_smt_int_to_bv_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.int_to_bv x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.int_to_bv)
    (fun hx hy => smtTermClosedIn_eo_to_smt_int_to_bv hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_repeat_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.repeat x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.repeat)
    (fun hx hy => smtTermClosedIn_eo_to_smt_repeat hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_zero_extend_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.zero_extend x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.zero_extend)
    (fun hx hy => smtTermClosedIn_eo_to_smt_zero_extend hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_sign_extend_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.sign_extend x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.sign_extend)
    (fun hx hy => smtTermClosedIn_eo_to_smt_sign_extend hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_rotate_left_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_left x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.rotate_left)
    (fun hx hy => smtTermClosedIn_eo_to_smt_rotate_left hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_rotate_right_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_right x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.rotate_right)
    (fun hx hy => smtTermClosedIn_eo_to_smt_rotate_right hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_at_bit_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1._at_bit x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1._at_bit)
    (fun hx hy => smtTermClosedIn_eo_to_smt_at_bit hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_re_exp_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.re_exp x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.re_exp)
    (fun hx hy => smtTermClosedIn_eo_to_smt_re_exp hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_is_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.is x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.is)
    (fun hx hy => smtTermClosedIn_eo_to_smt_is hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_tuple_select_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.tuple_select x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop1_of_closed_rec_using
    (op := UserOp1.tuple_select)
    (fun hx hy => smtTermClosedIn_eo_to_smt_tuple_select hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_update_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update x) y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update x) y) z)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_apply_uop1_of_closed_rec_using
    (op := UserOp1.update)
    (fun hx hy hz => smtTermClosedIn_eo_to_smt_update hx hy hz)
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_tuple_update_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update x) y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update x) y) z)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_apply_uop1_of_closed_rec_using
    (op := UserOp1.tuple_update)
    (fun hx hy hz => smtTermClosedIn_eo_to_smt_tuple_update hx hy hz)
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_extract_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.extract x y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract x y) z)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop2_of_closed_rec_using
    (op := UserOp2.extract)
    (fun hx hy hz => smtTermClosedIn_eo_to_smt_extract hx hy hz)
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_re_loop_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.re_loop x y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop x y) z)) :=
by
  exact smtTermClosedIn_eo_to_smt_apply_uop2_of_closed_rec_using
    (op := UserOp2.re_loop)
    (fun hx hy hz => smtTermClosedIn_eo_to_smt_re_loop hx hy hz)
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_and_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.and) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_and hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_or_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.or) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_or hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_imp_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.imp) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_imp hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_xor_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.xor) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_xor hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_eq_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.eq) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_eq hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_from_bools_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_from_bools) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_from_bools hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_tuple_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp.tuple) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_tuple hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_array_deq_diff_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term._at_array_deq_diff x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_array_deq_diff x y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_array_deq_diff) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_array_deq_diff hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_at_bv_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv y) x)) :=
by
  exact smtTermClosedIn_eo_to_smt_int_to_bv_of_closed_rec_using
    hEnv hRecY hRecX hClosed

theorem smtTermClosedIn_eo_to_smt_sets_deq_diff_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term._at_sets_deq_diff x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_sets_deq_diff x y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_sets_deq_diff) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_sets_deq_diff hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_strings_deq_diff_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec (Term._at_strings_deq_diff x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_strings_deq_diff x y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_strings_deq_diff) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_strings_deq_diff hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_strings_stoi_result_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term._at_strings_stoi_result x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term._at_strings_stoi_result x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_strings_stoi_result) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_strings_stoi_result hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_strings_stoi_non_digit_of_closed_rec_using
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term._at_strings_stoi_non_digit x)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term._at_strings_stoi_non_digit x)) :=
by
  exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
    (op := UserOp._at_strings_stoi_non_digit)
    (fun hx => smtTermClosedIn_eo_to_smt_strings_stoi_non_digit hx)
    hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_strings_itos_result_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term._at_strings_itos_result x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term._at_strings_itos_result x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_strings_itos_result) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_strings_itos_result hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_strings_num_occur_of_closed_rec_using
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)) :=
by
  exact smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
    (op := UserOp._at_strings_num_occur) (by decide) (by decide)
    (fun hx hy => smtTermClosedIn_eo_to_smt_strings_num_occur hx hy)
    hEnv hRecX hRecY hClosed

theorem smtTermClosedIn_eo_to_smt_witness_string_length_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec (Term.UOp3 UserOp3._at_witness_string_length x y z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.UOp3 UserOp3._at_witness_string_length x y z)) :=
by
  exact smtTermClosedIn_eo_to_smt_uop3_of_closed_rec_using
    (op := UserOp3._at_witness_string_length)
    (fun _ hy _ => smtTermClosedIn_eo_to_smt_witness_string_length hy)
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_re_unfold_pos_component_of_closed_rec_using
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hRecY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y))
    (hRecZ :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec z env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt z))
    (hClosed :
      __eo_is_closed_rec
        (Term._at_re_unfold_pos_component x y z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term._at_re_unfold_pos_component x y z)) :=
by
  exact smtTermClosedIn_eo_to_smt_uop3_of_closed_rec_using
    (op := UserOp3._at_re_unfold_pos_component)
    (fun hx hy hz => by
      change SmtTermClosedIn vars
        (native_ite (__eo_to_smt_nat_is_valid z)
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
            (__eo_to_smt y) (__eo_to_smt_nat z))
          SmtTerm.None)
      cases __eo_to_smt_nat_is_valid z <;> try trivial
      exact smtTermClosedIn_eo_to_smt_re_unfold_pos_component
        hx hy (__eo_to_smt_nat z))
    hEnv hRecX hRecY hRecZ hClosed

theorem smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall_of_closed_rec_using
    {xs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRecForall :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
            env' = Term.Boolean true ->
            SmtTermClosedIn vars'
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)))
    (hRecIdx :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec idx env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt idx))
    (hClosed :
      __eo_is_closed_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) idx)) :=
by
  exact smtTermClosedIn_eo_to_smt_uop2_of_closed_rec_using
    (op := UserOp2._at_quantifiers_skolemize)
    (fun hForall _ =>
      smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall hForall)
    hEnv hRecForall hRecIdx hClosed

theorem smtTermClosedIn_eo_to_smt_uop1_any_of_closed_rec_using
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x))
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 op x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 op x)) :=
by
  cases op <;> try trivial
  case seq_empty =>
    exact smtTermClosedIn_eo_to_smt_seq_empty_of_closed_rec_using
      hEnv hRec hClosed
  case set_empty =>
    exact smtTermClosedIn_eo_to_smt_set_empty_of_closed_rec_using
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_uop2_any_of_closed_rec_using
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp2 op x y)) :=
by
  cases op <;> try trivial
  case _at_const =>
    cases hValid : __eo_to_smt_nat_is_valid x
    · rw [TranslationProofs.eo_to_smt_at_const_of_invalid hValid]
      trivial
    · rw [TranslationProofs.eo_to_smt_at_const_of_valid hValid]
      trivial
  case _at_quantifiers_skolemize =>
    cases x <;> try trivial
    case Apply f body =>
      cases f <;> try trivial
      case Apply g xs =>
        cases g <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case «forall» =>
            exact
              smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall_of_closed_rec_using
                hEnv
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                hClosed

theorem smtTermClosedIn_eo_to_smt_uop3_any_of_closed_rec_using
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp3 op x y z)) :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact smtTermClosedIn_eo_to_smt_re_unfold_pos_component_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_witness_string_length =>
    exact smtTermClosedIn_eo_to_smt_witness_string_length_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed

theorem smtTermClosedIn_eo_to_smt_apply_uop_any_of_closed_rec_using
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  cases op
  case not =>
    exact smtTermClosedIn_eo_to_smt_not_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case distinct =>
    exact smtTermClosedIn_eo_to_smt_distinct_of_closed_rec_using
      hEnv hRec hClosed
  case _at_purify =>
    exact smtTermClosedIn_eo_to_smt_purify_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case to_real =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.to_real)
      (fun hx => smtTermClosedIn_eo_to_smt_to_real hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_to_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case is_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.is_int)
      (fun hx => smtTermClosedIn_eo_to_smt_is_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case abs =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.abs)
      (fun hx => smtTermClosedIn_eo_to_smt_abs hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case __eoo_neg_2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.__eoo_neg_2)
      (fun hx => smtTermClosedIn_eo_to_smt_uneg hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case int_pow2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_pow2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_pow2 hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case int_log2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_log2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_log2 hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case int_ispow2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_ispow2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_ispow2 hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_int_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_int_div_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_int_div_by_zero hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_mod_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_mod_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_mod_by_zero hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_bvsize =>
    exact smtTermClosedIn_eo_to_smt_bvsize_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvnot =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvnot)
      (fun hx => smtTermClosedIn_eo_to_smt_bvnot hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvneg =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvneg)
      (fun hx => smtTermClosedIn_eo_to_smt_bvneg hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvnego =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvnego)
      (fun hx => smtTermClosedIn_eo_to_smt_bvnego hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvredand =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvredand)
      (fun hx => smtTermClosedIn_eo_to_smt_bvredand hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvredor =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvredor)
      (fun hx => smtTermClosedIn_eo_to_smt_bvredor hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_len =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_len)
      (fun hx => smtTermClosedIn_eo_to_smt_str_len hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_rev =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_rev)
      (fun hx => smtTermClosedIn_eo_to_smt_str_rev hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_to_lower =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_lower)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_lower hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_to_upper =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_upper)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_upper hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_to_code =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_code)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_code hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_from_code =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_from_code)
      (fun hx => smtTermClosedIn_eo_to_smt_str_from_code hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_is_digit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_is_digit)
      (fun hx => smtTermClosedIn_eo_to_smt_str_is_digit hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_stoi_non_digit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_strings_stoi_non_digit)
      (fun hx => smtTermClosedIn_eo_to_smt_strings_stoi_non_digit hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_from_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_from_int)
      (fun hx => smtTermClosedIn_eo_to_smt_str_from_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_to_re =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_re)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_re hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_mult =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_mult)
      (fun hx => smtTermClosedIn_eo_to_smt_re_mult hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_plus =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_plus)
      (fun hx => smtTermClosedIn_eo_to_smt_re_plus hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_opt =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_opt)
      (fun hx => smtTermClosedIn_eo_to_smt_re_opt hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_comp =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_comp)
      (fun hx => smtTermClosedIn_eo_to_smt_re_comp hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case seq_unit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.seq_unit)
      (fun hx => smtTermClosedIn_eo_to_smt_seq_unit hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case set_singleton =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_singleton)
      (fun hx => smtTermClosedIn_eo_to_smt_set_singleton hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case set_choose =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_choose)
      (fun hx => smtTermClosedIn_eo_to_smt_set_choose hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case set_is_empty =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_is_empty)
      (fun hx => smtTermClosedIn_eo_to_smt_set_is_empty hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case set_is_singleton =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_is_singleton)
      (fun hx => smtTermClosedIn_eo_to_smt_set_is_singleton hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_div_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_qdiv_by_zero hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case ubv_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.ubv_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_ubv_to_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case sbv_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.sbv_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_sbv_to_int hx)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_uop1_any_of_closed_rec_using
    {op : UserOp1} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 op x) y)) :=
by
  cases op
  case «repeat» =>
    exact smtTermClosedIn_eo_to_smt_repeat_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case zero_extend =>
    exact smtTermClosedIn_eo_to_smt_zero_extend_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case sign_extend =>
    exact smtTermClosedIn_eo_to_smt_sign_extend_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case rotate_left =>
    exact smtTermClosedIn_eo_to_smt_rotate_left_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case rotate_right =>
    exact smtTermClosedIn_eo_to_smt_rotate_right_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_bit =>
    exact smtTermClosedIn_eo_to_smt_at_bit_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_exp =>
    exact smtTermClosedIn_eo_to_smt_re_exp_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case «is» =>
    exact smtTermClosedIn_eo_to_smt_is_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case tuple_select =>
    exact smtTermClosedIn_eo_to_smt_tuple_select_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case int_to_bv =>
    exact smtTermClosedIn_eo_to_smt_int_to_bv_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_uop2_any_of_closed_rec_using
    {op : UserOp2} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op x y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp2 op x y) z)) :=
by
  cases op
  case extract =>
    exact smtTermClosedIn_eo_to_smt_extract_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case re_loop =>
    exact smtTermClosedIn_eo_to_smt_re_loop_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_apply_uop1_any_of_closed_rec_using
    {op : UserOp1} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op x) y) z)) :=
by
  cases op
  case update =>
    exact smtTermClosedIn_eo_to_smt_update_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case tuple_update =>
    exact smtTermClosedIn_eo_to_smt_tuple_update_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_apply_apply_uop_any_of_closed_rec_using
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)) :=
by
  cases op
  case ite =>
    exact smtTermClosedIn_eo_to_smt_ite_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case store =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.store) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_store hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case bvite =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.bvite) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_bvite hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_substr =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_substr) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_substr hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_replace =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_indexof =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_indexof) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_indexof hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_update =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_update) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_update hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_replace_all =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_all) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_all hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_replace_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_re) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_replace_re_all =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_re_all) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_re_all hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_indexof_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_indexof_re) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_indexof_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_occur_index =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp._at_strings_occur_index) (by decide) (by decide)
      (fun hx hy hz =>
        smtTermClosedIn_eo_to_smt_strings_occur_index hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_occur_index_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp._at_strings_occur_index_re) (by decide) (by decide)
      (fun hx hy hz =>
        smtTermClosedIn_eo_to_smt_strings_occur_index_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_not_binary_uop_of_closed_rec_using
    {f x env : Term} {vars : List SmtVarKey}
    (hNotBinary :
      ∀ op y, f ≠ Term.Apply (Term.UOp op) y)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply f x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply f x)) :=
by
  cases f
  case UOp op =>
    exact smtTermClosedIn_eo_to_smt_apply_uop_any_of_closed_rec_using
      hEnv hRec hClosed
  case UOp1 op a =>
    exact smtTermClosedIn_eo_to_smt_apply_uop1_any_of_closed_rec_using
      hEnv hRec hClosed
  case UOp2 op a b =>
    exact smtTermClosedIn_eo_to_smt_apply_uop2_any_of_closed_rec_using
      hEnv hRec hClosed
  case Apply g y =>
    cases g
    case UOp op =>
      exfalso
      exact hNotBinary op y rfl
    case UOp1 op a =>
      exact smtTermClosedIn_eo_to_smt_apply_apply_uop1_any_of_closed_rec_using
        hEnv hRec hClosed
    case Apply h z =>
      cases h
      case UOp op =>
        exact smtTermClosedIn_eo_to_smt_apply_apply_apply_uop_any_of_closed_rec_using
          hEnv hRec hClosed
      case Apply k w =>
        cases k
        case UOp op =>
          cases op
          case _at_strings_replace_all_result =>
            exact
              smtTermClosedIn_eo_to_smt_quaternary_uop_of_closed_rec_using
                (op := UserOp._at_strings_replace_all_result)
                (by decide) (by decide)
                (fun hw hz hy hx =>
                  smtTermClosedIn_eo_to_smt_strings_replace_all_result
                    hw hz hy hx)
                hEnv
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                hClosed
          case _at_strings_replace_re_all_result =>
            exact
              smtTermClosedIn_eo_to_smt_quaternary_uop_of_closed_rec_using
                (op := UserOp._at_strings_replace_re_all_result)
                (by decide) (by decide)
                (fun hw hz hy hx =>
                  smtTermClosedIn_eo_to_smt_strings_replace_re_all_result
                    hw hz hy hx)
                hEnv
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hEnv' hClosed')
                hClosed
          all_goals
            exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
              (by rfl)
              (fun vs hEq => hNotBinary UserOp.forall vs hEq)
              (fun vs hEq => hNotBinary UserOp.exists vs hEq)
              hEnv
              (fun hEnv' hClosed' => hRec hEnv' hClosed')
              (fun hEnv' hClosed' => hRec hEnv' hClosed')
              hClosed
        all_goals
          exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
            (by rfl)
            (fun vs hEq => hNotBinary UserOp.forall vs hEq)
            (fun vs hEq => hNotBinary UserOp.exists vs hEq)
            hEnv
            (fun hEnv' hClosed' => hRec hEnv' hClosed')
            (fun hEnv' hClosed' => hRec hEnv' hClosed')
            hClosed
      all_goals
        exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
          (by rfl)
          (fun vs hEq => hNotBinary UserOp.forall vs hEq)
          (fun vs hEq => hNotBinary UserOp.exists vs hEq)
          hEnv
          (fun hEnv' hClosed' => hRec hEnv' hClosed')
          (fun hEnv' hClosed' => hRec hEnv' hClosed')
          hClosed
    all_goals
      exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
        (by rfl)
        (fun vs hEq => hNotBinary UserOp.forall vs hEq)
        (fun vs hEq => hNotBinary UserOp.exists vs hEq)
        hEnv
        (fun hEnv' hClosed' => hRec hEnv' hClosed')
        (fun hEnv' hClosed' => hRec hEnv' hClosed')
        hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs hEq => hNotBinary UserOp.forall vs hEq)
      (fun vs hEq => hNotBinary UserOp.exists vs hEq)
      hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_of_eo_is_closed_rec_perm_non_apply
    {t env : Term} {vars : List SmtVarKey}
    (hNotApply : ∀ f x, t ≠ Term.Apply f x)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed : __eo_is_closed_rec t env = Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt t) :=
by
  cases t
  case UOp op =>
    exact smtTermClosedIn_eo_to_smt_uop vars op
  case UOp1 op x =>
    exact smtTermClosedIn_eo_to_smt_uop1_any_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case UOp2 op x y =>
    exact smtTermClosedIn_eo_to_smt_uop2_any_of_closed_rec_using
      hEnv hRec hClosed
  case UOp3 op x y z =>
    exact smtTermClosedIn_eo_to_smt_uop3_any_of_closed_rec_using
      hEnv hRec hClosed
  case Boolean b =>
    exact smtTermClosedIn_eo_to_smt_boolean vars b
  case Numeral n =>
    exact smtTermClosedIn_eo_to_smt_numeral vars n
  case Rational r =>
    exact smtTermClosedIn_eo_to_smt_rational vars r
  case String s =>
    exact smtTermClosedIn_eo_to_smt_string vars s
  case Binary w n =>
    exact smtTermClosedIn_eo_to_smt_binary vars w n
  case Apply f x =>
    exfalso
    exact hNotApply f x rfl
  case Var name T =>
    exact smtTermClosedIn_eo_to_smt_var_of_closed_rec_perm
      hEnv hClosed
  case DtCons s d i =>
    exact smtTermClosedIn_eo_to_smt_dtcons vars s d i
  case DtSel s d i j =>
    exact smtTermClosedIn_eo_to_smt_dtsel vars s d i j
  case UConst i T =>
    exact smtTermClosedIn_eo_to_smt_uconst vars i T
  all_goals
    trivial

theorem smtTermClosedIn_eo_to_smt_exists_cons_term
    {vars : List SmtVarKey} {s : native_String} {T vs body : Term}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs (__eo_to_smt body))) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.exists)
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) vs))
        body)) :=
by
  change
    SmtTermClosedIn vars
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) vs)
        (__eo_to_smt body))
  exact smtTermClosedIn_eo_to_smt_exists_cons hBody

theorem smtTermClosedIn_eo_to_smt_exists_nil_term
    {vars : List SmtVarKey} {body : Term} :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.exists) Term.__eo_List_nil)
        body)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_exists_term_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {body : Term},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body) ->
          SmtTermClosedIn vars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body))
  | _, _, _, _, EoSmtVarEnv.nil, hBody =>
      by
        trivial
  | _, _, _, _, EoSmtVarEnv.cons (s := s) (T := T) hTail, hBody =>
      by
        exact smtTermClosedIn_eo_to_smt_exists_cons_term
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env hTail (by
            simpa [List.reverse_cons, List.append_assoc] using hBody))

theorem smtTermClosedIn_eo_to_smt_exists_term_of_env_or_none
    {vs body : Term} {vars : List SmtVarKey}
    (hBody :
      ∀ {binderVars : List SmtVarKey},
        EoSmtVarEnv vs binderVars ->
          SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body)) :=
by
  cases vs
  all_goals
    first
    | exact smtTermClosedIn_eo_to_smt_exists_of_env_or_none
        (vars := vars) (F := __eo_to_smt body) hBody
    | trivial

theorem smtTermClosedIn_eo_to_smt_forall_nil
    {vars : List SmtVarKey} {body : Term} :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.forall) Term.__eo_List_nil)
        body)) :=
by
  trivial

theorem smtTermClosedIn_eo_to_smt_forall_cons_term
    {vars : List SmtVarKey} {s : native_String} {T vs body : Term}
    (hBody :
      SmtTermClosedIn ((s, __eo_to_smt_type T) :: vars)
        (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body)))) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.forall)
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) vs))
        body)) :=
by
  change
    SmtTermClosedIn vars
      (SmtTerm.not
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) vs)
          (SmtTerm.not (__eo_to_smt body))))
  exact smtTermClosedIn_eo_to_smt_exists_cons hBody

theorem smtTermClosedIn_eo_to_smt_forall_term_of_rev_env :
    ∀ {vs : Term} {binderVars vars : List SmtVarKey} {body : Term},
      EoSmtVarEnv vs binderVars ->
        SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body) ->
          SmtTermClosedIn vars
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body))
  | _, _, _, _, EoSmtVarEnv.nil, hBody =>
      by
        trivial
  | _, _, _, body, EoSmtVarEnv.cons (s := s) (T := T) hTail, hBody =>
      by
        exact smtTermClosedIn_eo_to_smt_forall_cons_term
          (s := s) (T := T)
          (smtTermClosedIn_eo_to_smt_exists_of_rev_env
            (F := SmtTerm.not (__eo_to_smt body)) hTail (by
              change SmtTermClosedIn _ (__eo_to_smt body)
              simpa [List.reverse_cons, List.append_assoc] using hBody))

theorem smtTermClosedIn_eo_to_smt_forall_term_of_env_or_none
    {vs body : Term} {vars : List SmtVarKey}
    (hBody :
      ∀ {binderVars : List SmtVarKey},
        EoSmtVarEnv vs binderVars ->
          SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body)) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)) :=
by
  cases vs
  all_goals
    first
    | exact smtTermClosedIn_eo_to_smt_exists_of_env_or_none
        (vars := vars) (F := SmtTerm.not (__eo_to_smt body))
        (by
          intro binderVars hVs
          change SmtTermClosedIn (binderVars.reverse ++ vars) (__eo_to_smt body)
          exact hBody hVs)
    | trivial

theorem smtTermClosedIn_eo_to_smt_exists_of_closed_rec_using
    {vs body env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec body env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt body))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) body)) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact smtTermClosedIn_eo_to_smt_exists_term_of_env_or_none
        (by
          intro binderVars hVs
          exact hRec
            (EoSmtVarEnvPerm.concat_rev hVs
              ⟨_, EoSmtVarEnv.nil, hEquiv⟩)
            (by simpa [__eo_is_closed_rec] using hClosed))
  | cons hTail =>
      exact smtTermClosedIn_eo_to_smt_exists_term_of_env_or_none
        (by
          intro binderVars hVs
          exact hRec
            (EoSmtVarEnvPerm.concat_rev hVs
              ⟨_, EoSmtVarEnv.cons hTail, hEquiv⟩)
            (by simpa [__eo_is_closed_rec] using hClosed))

theorem smtTermClosedIn_eo_to_smt_forall_of_closed_rec_using
    {vs body env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec body env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt body))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  cases hExact with
  | nil =>
      exact smtTermClosedIn_eo_to_smt_forall_term_of_env_or_none
        (by
          intro binderVars hVs
          exact hRec
            (EoSmtVarEnvPerm.concat_rev hVs
              ⟨_, EoSmtVarEnv.nil, hEquiv⟩)
            (by simpa [__eo_is_closed_rec] using hClosed))
  | cons hTail =>
      exact smtTermClosedIn_eo_to_smt_forall_term_of_env_or_none
        (by
          intro binderVars hVs
          exact hRec
            (EoSmtVarEnvPerm.concat_rev hVs
              ⟨_, EoSmtVarEnv.cons hTail, hEquiv⟩)
            (by simpa [__eo_is_closed_rec] using hClosed))

theorem smtTermClosedIn_eo_to_smt_apply_apply_uop_any_of_closed_rec_using
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec t env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  let binary
      (hNotForall : op ≠ UserOp.forall)
      (hNotExists : op ≠ UserOp.exists)
      (hBuilder :
        SmtTermClosedIn vars (__eo_to_smt x) ->
          SmtTermClosedIn vars (__eo_to_smt y) ->
            SmtTermClosedIn vars
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp op) x) y))) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
    smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
      (op := op) hNotForall hNotExists hBuilder hEnv
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed
  cases op
  case «or» =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_or hx hy)
  case «and» =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_and hx hy)
  case imp =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_imp hx hy)
  case xor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_xor hx hy)
  case eq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_eq hx hy)
  case plus =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_plus hx hy)
  case neg =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_neg hx hy)
  case mult =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mult hx hy)
  case lt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_lt hx hy)
  case leq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_leq hx hy)
  case gt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_gt hx hy)
  case geq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_geq hx hy)
  case div =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_div hx hy)
  case mod =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mod hx hy)
  case divisible =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_divisible hx hy)
  case div_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_div_total hx hy)
  case mod_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mod_total hx hy)
  case select =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_select hx hy)
  case concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_concat hx hy)
  case bvand =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvand hx hy)
  case bvor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvor hx hy)
  case bvnand =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvnand hx hy)
  case bvnor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvnor hx hy)
  case bvxor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvxor hx hy)
  case bvxnor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvxnor hx hy)
  case bvcomp =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvcomp hx hy)
  case bvadd =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvadd hx hy)
  case bvmul =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvmul hx hy)
  case bvudiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvudiv hx hy)
  case bvurem =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvurem hx hy)
  case bvsub =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsub hx hy)
  case bvsdiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsdiv hx hy)
  case bvsrem =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsrem hx hy)
  case bvsmod =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsmod hx hy)
  case bvult =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvult hx hy)
  case bvule =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvule hx hy)
  case bvugt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvugt hx hy)
  case bvuge =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvuge hx hy)
  case bvslt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvslt hx hy)
  case bvsle =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsle hx hy)
  case bvsgt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsgt hx hy)
  case bvsge =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsge hx hy)
  case bvshl =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvshl hx hy)
  case bvlshr =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvlshr hx hy)
  case bvashr =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvashr hx hy)
  case bvuaddo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvuaddo hx hy)
  case bvsaddo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsaddo hx hy)
  case bvumulo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvumulo hx hy)
  case bvsmulo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsmulo hx hy)
  case bvusubo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvusubo hx hy)
  case bvssubo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvssubo hx hy)
  case bvsdivo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsdivo hx hy)
  case bvultbv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvultbv hx hy)
  case bvsltbv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsltbv hx hy)
  case _at_from_bools =>
    exact smtTermClosedIn_eo_to_smt_from_bools_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case str_concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_concat hx hy)
  case str_contains =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_contains hx hy)
  case str_at =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_at hx hy)
  case str_prefixof =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_prefixof hx hy)
  case str_suffixof =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_suffixof hx hy)
  case str_lt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_lt hx hy)
  case str_leq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_leq hx hy)
  case re_range =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_range hx hy)
  case re_concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_concat hx hy)
  case re_inter =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_inter hx hy)
  case re_union =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_union hx hy)
  case re_diff =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_diff hx hy)
  case str_in_re =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_in_re hx hy)
  case seq_nth =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_seq_nth hx hy)
  case _at_strings_num_occur =>
    exact smtTermClosedIn_eo_to_smt_strings_num_occur_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_num_occur_re =>
    exact binary (by decide) (by decide)
      (fun hx hy =>
        smtTermClosedIn_eo_to_smt_strings_num_occur_re hx hy)
  case _at_array_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_array_deq_diff_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_strings_deq_diff_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_stoi_result =>
    exact smtTermClosedIn_eo_to_smt_strings_stoi_result_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_strings_itos_result =>
    exact smtTermClosedIn_eo_to_smt_strings_itos_result_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case _at_sets_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_sets_deq_diff_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case tuple =>
    exact smtTermClosedIn_eo_to_smt_tuple_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case set_union =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_union hx hy)
  case set_inter =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_inter hx hy)
  case set_minus =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_minus hx hy)
  case set_member =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_member hx hy)
  case set_subset =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_subset hx hy)
  case set_insert =>
    exact smtTermClosedIn_eo_to_smt_set_insert_of_closed_rec_using
      hEnv hRec hClosed
  case qdiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_qdiv hx hy)
  case qdiv_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_qdiv_total hx hy)
  case «forall» =>
    exact smtTermClosedIn_eo_to_smt_forall_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  case «exists» =>
    exact smtTermClosedIn_eo_to_smt_exists_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
      (by rfl)
      (fun vs hEq => by cases hEq)
      (fun vs hEq => by cases hEq)
      hEnv
      (fun hEnv' hClosed' =>
        smtTermClosedIn_eo_to_smt_apply_uop_any_of_closed_rec_using
          hEnv' (fun hEnv'' hClosed'' => hRec hEnv'' hClosed'')
          hClosed')
      (fun hEnv' hClosed' => hRec hEnv' hClosed')
      hClosed

theorem smtTermClosedIn_eo_to_smt_apply_generic_below
    {f x env : Term} {vars : List SmtVarKey}
    (hSmt :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply f x) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply f x) env = Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply f x)) :=
by
  have hFLt : sizeOf f < sizeOf (Term.Apply f x) := by
    simp
    omega
  have hXLt : sizeOf x < sizeOf (Term.Apply f x) := by
    simp
    omega
  exact smtTermClosedIn_eo_to_smt_apply_generic_of_closed_rec_using
    hSmt hNotForall hNotExists hEnv
    (fun hEnv' hClosed' => hRec hFLt hEnv' hClosed')
    (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
    hClosed

theorem smtTermClosedIn_eo_to_smt_uop1_any_below
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.UOp1 op x) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.UOp1 op x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp1 op x)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.UOp1 op x) := by
    simp
    omega
  cases op <;> try trivial
  case seq_empty =>
    exact smtTermClosedIn_eo_to_smt_seq_empty_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed') hClosed
  case set_empty =>
    exact smtTermClosedIn_eo_to_smt_set_empty_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed') hClosed

theorem smtTermClosedIn_eo_to_smt_uop2_any_below
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.UOp2 op x y) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp2 op x y)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.UOp2 op x y) := by
    simp
    omega
  have hYLt : sizeOf y < sizeOf (Term.UOp2 op x y) := by
    simp
    omega
  cases op <;> try trivial
  case _at_const =>
    cases hValid : __eo_to_smt_nat_is_valid x
    · rw [TranslationProofs.eo_to_smt_at_const_of_invalid hValid]
      trivial
    · rw [TranslationProofs.eo_to_smt_at_const_of_valid hValid]
      trivial
  case _at_quantifiers_skolemize =>
    cases x <;> try trivial
    case Apply f body =>
      cases f <;> try trivial
      case Apply g xs =>
        cases g <;> try trivial
        case UOp op =>
          cases op <;> try trivial
          case «forall» =>
            exact
              smtTermClosedIn_eo_to_smt_quantifiers_skolemize_forall_of_closed_rec_using
                hEnv
                (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
                (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
                hClosed

theorem smtTermClosedIn_eo_to_smt_uop3_any_below
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.UOp3 op x y z) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.UOp3 op x y z)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.UOp3 op x y z) := by
    simp
    omega
  have hYLt : sizeOf y < sizeOf (Term.UOp3 op x y z) := by
    simp
    omega
  have hZLt : sizeOf z < sizeOf (Term.UOp3 op x y z) := by
    simp
    omega
  cases op
  case _at_re_unfold_pos_component =>
    exact smtTermClosedIn_eo_to_smt_re_unfold_pos_component_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case _at_witness_string_length =>
    exact smtTermClosedIn_eo_to_smt_witness_string_length_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed

theorem smtTermClosedIn_eo_to_smt_distinct_below
    {xs env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.UOp UserOp.distinct) xs) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.distinct) xs) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) :=
by
  have hXsLt :
      sizeOf xs < sizeOf (Term.Apply (Term.UOp UserOp.distinct) xs) := by
    simp
  have hXs :=
    eo_is_closed_rec_apply_uop_arg_eq_true
      (op := UserOp.distinct) hEnv hClosed
  change SmtTermClosedIn vars
    (native_ite
      (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs))
  cases native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None <;>
    try trivial
  simpa [native_ite] using
    smtTermClosedIn_eo_to_smt_distinct_rec_below
      (Term.Apply (Term.UOp UserOp.distinct) xs) hRec
      hXsLt hEnv hXs

theorem smtTermClosedIn_eo_to_smt_apply_uop_any_below
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.UOp op) x) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.Apply (Term.UOp op) x) := by
    simp
    omega
  let recX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x) :=
    fun hEnv' hClosed' => hRec hXLt hEnv' hClosed'
  cases op
  case not =>
    exact smtTermClosedIn_eo_to_smt_not_of_closed_rec_using
      hEnv recX hClosed
  case distinct =>
    exact smtTermClosedIn_eo_to_smt_distinct_below hEnv hRec hClosed
  case _at_purify =>
    exact smtTermClosedIn_eo_to_smt_purify_of_closed_rec_using
      hEnv recX hClosed
  case to_real =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.to_real)
      (fun hx => smtTermClosedIn_eo_to_smt_to_real hx)
      hEnv recX hClosed
  case to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_to_int hx)
      hEnv recX hClosed
  case is_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.is_int)
      (fun hx => smtTermClosedIn_eo_to_smt_is_int hx)
      hEnv recX hClosed
  case abs =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.abs)
      (fun hx => smtTermClosedIn_eo_to_smt_abs hx)
      hEnv recX hClosed
  case __eoo_neg_2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.__eoo_neg_2)
      (fun hx => smtTermClosedIn_eo_to_smt_uneg hx)
      hEnv recX hClosed
  case int_pow2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_pow2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_pow2 hx)
      hEnv recX hClosed
  case int_log2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_log2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_log2 hx)
      hEnv recX hClosed
  case int_ispow2 =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.int_ispow2)
      (fun hx => smtTermClosedIn_eo_to_smt_int_ispow2 hx)
      hEnv recX hClosed
  case _at_int_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_int_div_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_int_div_by_zero hx)
      hEnv recX hClosed
  case _at_mod_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_mod_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_mod_by_zero hx)
      hEnv recX hClosed
  case _at_bvsize =>
    exact smtTermClosedIn_eo_to_smt_bvsize_of_closed_rec_using
      hEnv recX hClosed
  case bvnot =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvnot)
      (fun hx => smtTermClosedIn_eo_to_smt_bvnot hx)
      hEnv recX hClosed
  case bvneg =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvneg)
      (fun hx => smtTermClosedIn_eo_to_smt_bvneg hx)
      hEnv recX hClosed
  case bvnego =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvnego)
      (fun hx => smtTermClosedIn_eo_to_smt_bvnego hx)
      hEnv recX hClosed
  case bvredand =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvredand)
      (fun hx => smtTermClosedIn_eo_to_smt_bvredand hx)
      hEnv recX hClosed
  case bvredor =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.bvredor)
      (fun hx => smtTermClosedIn_eo_to_smt_bvredor hx)
      hEnv recX hClosed
  case str_len =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_len)
      (fun hx => smtTermClosedIn_eo_to_smt_str_len hx)
      hEnv recX hClosed
  case str_rev =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_rev)
      (fun hx => smtTermClosedIn_eo_to_smt_str_rev hx)
      hEnv recX hClosed
  case str_to_lower =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_lower)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_lower hx)
      hEnv recX hClosed
  case str_to_upper =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_upper)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_upper hx)
      hEnv recX hClosed
  case str_to_code =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_code)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_code hx)
      hEnv recX hClosed
  case str_from_code =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_from_code)
      (fun hx => smtTermClosedIn_eo_to_smt_str_from_code hx)
      hEnv recX hClosed
  case str_is_digit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_is_digit)
      (fun hx => smtTermClosedIn_eo_to_smt_str_is_digit hx)
      hEnv recX hClosed
  case str_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_int hx)
      hEnv recX hClosed
  case _at_strings_stoi_non_digit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_strings_stoi_non_digit)
      (fun hx => smtTermClosedIn_eo_to_smt_strings_stoi_non_digit hx)
      hEnv recX hClosed
  case str_from_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_from_int)
      (fun hx => smtTermClosedIn_eo_to_smt_str_from_int hx)
      hEnv recX hClosed
  case str_to_re =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.str_to_re)
      (fun hx => smtTermClosedIn_eo_to_smt_str_to_re hx)
      hEnv recX hClosed
  case re_mult =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_mult)
      (fun hx => smtTermClosedIn_eo_to_smt_re_mult hx)
      hEnv recX hClosed
  case re_plus =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_plus)
      (fun hx => smtTermClosedIn_eo_to_smt_re_plus hx)
      hEnv recX hClosed
  case re_opt =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_opt)
      (fun hx => smtTermClosedIn_eo_to_smt_re_opt hx)
      hEnv recX hClosed
  case re_comp =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.re_comp)
      (fun hx => smtTermClosedIn_eo_to_smt_re_comp hx)
      hEnv recX hClosed
  case seq_unit =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.seq_unit)
      (fun hx => smtTermClosedIn_eo_to_smt_seq_unit hx)
      hEnv recX hClosed
  case set_singleton =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_singleton)
      (fun hx => smtTermClosedIn_eo_to_smt_set_singleton hx)
      hEnv recX hClosed
  case set_choose =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_choose)
      (fun hx => smtTermClosedIn_eo_to_smt_set_choose hx)
      hEnv recX hClosed
  case set_is_empty =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_is_empty)
      (fun hx => smtTermClosedIn_eo_to_smt_set_is_empty hx)
      hEnv recX hClosed
  case set_is_singleton =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.set_is_singleton)
      (fun hx => smtTermClosedIn_eo_to_smt_set_is_singleton hx)
      hEnv recX hClosed
  case _at_div_by_zero =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp._at_div_by_zero)
      (fun hx => smtTermClosedIn_eo_to_smt_qdiv_by_zero hx)
      hEnv recX hClosed
  case ubv_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.ubv_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_ubv_to_int hx)
      hEnv recX hClosed
  case sbv_to_int =>
    exact smtTermClosedIn_eo_to_smt_unary_uop_of_closed_rec_using
      (op := UserOp.sbv_to_int)
      (fun hx => smtTermClosedIn_eo_to_smt_sbv_to_int hx)
      hEnv recX hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_apply_uop1_any_below
    {op : UserOp1} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.UOp1 op x) y) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp1 op x) y)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.Apply (Term.UOp1 op x) y) := by
    simp; omega
  have hYLt : sizeOf y < sizeOf (Term.Apply (Term.UOp1 op x) y) := by
    simp; omega
  cases op
  case «repeat» =>
    exact smtTermClosedIn_eo_to_smt_repeat_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case zero_extend =>
    exact smtTermClosedIn_eo_to_smt_zero_extend_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case sign_extend =>
    exact smtTermClosedIn_eo_to_smt_sign_extend_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case rotate_left =>
    exact smtTermClosedIn_eo_to_smt_rotate_left_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case rotate_right =>
    exact smtTermClosedIn_eo_to_smt_rotate_right_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case _at_bit =>
    exact smtTermClosedIn_eo_to_smt_at_bit_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case re_exp =>
    exact smtTermClosedIn_eo_to_smt_re_exp_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case «is» =>
    exact smtTermClosedIn_eo_to_smt_is_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case tuple_select =>
    exact smtTermClosedIn_eo_to_smt_tuple_select_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  case int_to_bv =>
    exact smtTermClosedIn_eo_to_smt_int_to_bv_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_apply_uop2_any_below
    {op : UserOp2} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.UOp2 op x y) z) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op x y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply (Term.UOp2 op x y) z)) :=
by
  have hXLt : sizeOf x < sizeOf (Term.Apply (Term.UOp2 op x y) z) := by
    simp; omega
  have hYLt : sizeOf y < sizeOf (Term.Apply (Term.UOp2 op x y) z) := by
    simp; omega
  have hZLt : sizeOf z < sizeOf (Term.Apply (Term.UOp2 op x y) z) := by
    simp; omega
  cases op
  case extract =>
    exact smtTermClosedIn_eo_to_smt_extract_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case re_loop =>
    exact smtTermClosedIn_eo_to_smt_re_loop_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_apply_apply_uop1_any_below
    {op : UserOp1} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op x) y) z)) :=
by
  have hXLt :
      sizeOf x <
        sizeOf (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) := by
    simp; omega
  have hYLt :
      sizeOf y <
        sizeOf (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) := by
    simp; omega
  have hZLt :
      sizeOf z <
        sizeOf (Term.Apply (Term.Apply (Term.UOp1 op x) y) z) := by
    simp; omega
  cases op
  case update =>
    exact smtTermClosedIn_eo_to_smt_update_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case tuple_update =>
    exact smtTermClosedIn_eo_to_smt_tuple_update_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_apply_apply_apply_uop_any_below
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t <
          sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env = Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)) :=
by
  have hXLt :
      sizeOf x <
        sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) := by
    simp; omega
  have hYLt :
      sizeOf y <
        sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) := by
    simp; omega
  have hZLt :
      sizeOf z <
        sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) := by
    simp; omega
  cases op
  case ite =>
    exact smtTermClosedIn_eo_to_smt_ite_of_closed_rec_using
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case store =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.store) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_store hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case bvite =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.bvite) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_bvite hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_substr =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_substr) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_substr hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_replace =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_indexof =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_indexof) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_indexof hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_update =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_update) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_update hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_replace_all =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_all) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_all hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_replace_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_re) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_replace_re_all =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_replace_re_all) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_replace_re_all hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case str_indexof_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp.str_indexof_re) (by decide) (by decide)
      (fun hx hy hz => smtTermClosedIn_eo_to_smt_str_indexof_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case _at_strings_occur_index =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp._at_strings_occur_index) (by decide) (by decide)
      (fun hx hy hz =>
        smtTermClosedIn_eo_to_smt_strings_occur_index hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  case _at_strings_occur_index_re =>
    exact smtTermClosedIn_eo_to_smt_ternary_uop_of_closed_rec_using
      (op := UserOp._at_strings_occur_index_re) (by decide) (by decide)
      (fun hx hy hz =>
        smtTermClosedIn_eo_to_smt_strings_occur_index_re hx hy hz)
      hEnv (fun hEnv' hClosed' => hRec hXLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hYLt hEnv' hClosed')
      (fun hEnv' hClosed' => hRec hZLt hEnv' hClosed') hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs h => by cases h)
      (fun vs h => by cases h)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_set_insert_below
    {xs x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t <
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)) :=
by
  have hXsLt :
      sizeOf xs <
        sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) := by
    simp; omega
  have hXLt :
      sizeOf x <
        sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) := by
    simp; omega
  have hCases :=
    eo_is_closed_rec_binary_uop_eq_true_cases
      (op := UserOp.set_insert) (by decide) (by decide)
      hEnv hClosed
  cases xs
  case Apply f arg =>
    cases f
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        exact smtTermClosedIn_eo_to_smt_set_insert_rec_below
          _ hRec
          hXsLt hEnv hCases.1
          (hRec hXLt hEnv hCases.2)
      all_goals
        exact smtTermClosedIn_eo_to_smt_set_insert_rec_below
          _ hRec
          hXsLt hEnv hCases.1
          (hRec hXLt hEnv hCases.2)
    all_goals
      exact smtTermClosedIn_eo_to_smt_set_insert_rec_below
        _ hRec
        hXsLt hEnv hCases.1
        (hRec hXLt hEnv hCases.2)
  all_goals
    exact smtTermClosedIn_eo_to_smt_set_insert_rec_below
      _ hRec
      hXsLt hEnv hCases.1
      (hRec hXLt hEnv hCases.2)

theorem smtTermClosedIn_eo_to_smt_apply_apply_uop_any_below
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean true) :
  SmtTermClosedIn vars
    (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  have hXLt :
      sizeOf x < sizeOf (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simp; omega
  have hYLt :
      sizeOf y < sizeOf (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simp; omega
  let recX :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec x env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt x) :=
    fun hEnv' hClosed' => hRec hXLt hEnv' hClosed'
  let recY :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnvPerm env' vars' ->
          __eo_is_closed_rec y env' = Term.Boolean true ->
            SmtTermClosedIn vars' (__eo_to_smt y) :=
    fun hEnv' hClosed' => hRec hYLt hEnv' hClosed'
  let binary
      (hNotForall : op ≠ UserOp.forall)
      (hNotExists : op ≠ UserOp.exists)
      (hBuilder :
        SmtTermClosedIn vars (__eo_to_smt x) ->
          SmtTermClosedIn vars (__eo_to_smt y) ->
            SmtTermClosedIn vars
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp op) x) y))) :
    SmtTermClosedIn vars
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
    smtTermClosedIn_eo_to_smt_binary_uop_of_closed_rec_using
      (op := op) hNotForall hNotExists hBuilder hEnv
      recX recY hClosed
  cases op
  case «or» =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_or hx hy)
  case «and» =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_and hx hy)
  case imp =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_imp hx hy)
  case xor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_xor hx hy)
  case eq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_eq hx hy)
  case plus =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_plus hx hy)
  case neg =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_neg hx hy)
  case mult =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mult hx hy)
  case lt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_lt hx hy)
  case leq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_leq hx hy)
  case gt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_gt hx hy)
  case geq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_geq hx hy)
  case div =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_div hx hy)
  case mod =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mod hx hy)
  case divisible =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_divisible hx hy)
  case div_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_div_total hx hy)
  case mod_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_mod_total hx hy)
  case select =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_select hx hy)
  case concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_concat hx hy)
  case bvand =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvand hx hy)
  case bvor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvor hx hy)
  case bvnand =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvnand hx hy)
  case bvnor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvnor hx hy)
  case bvxor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvxor hx hy)
  case bvxnor =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvxnor hx hy)
  case bvcomp =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvcomp hx hy)
  case bvadd =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvadd hx hy)
  case bvmul =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvmul hx hy)
  case bvudiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvudiv hx hy)
  case bvurem =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvurem hx hy)
  case bvsub =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsub hx hy)
  case bvsdiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsdiv hx hy)
  case bvsrem =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsrem hx hy)
  case bvsmod =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsmod hx hy)
  case bvult =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvult hx hy)
  case bvule =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvule hx hy)
  case bvugt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvugt hx hy)
  case bvuge =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvuge hx hy)
  case bvslt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvslt hx hy)
  case bvsle =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsle hx hy)
  case bvsgt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsgt hx hy)
  case bvsge =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsge hx hy)
  case bvshl =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvshl hx hy)
  case bvlshr =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvlshr hx hy)
  case bvashr =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvashr hx hy)
  case bvuaddo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvuaddo hx hy)
  case bvsaddo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsaddo hx hy)
  case bvumulo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvumulo hx hy)
  case bvsmulo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsmulo hx hy)
  case bvusubo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvusubo hx hy)
  case bvssubo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvssubo hx hy)
  case bvsdivo =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsdivo hx hy)
  case bvultbv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvultbv hx hy)
  case bvsltbv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_bvsltbv hx hy)
  case _at_from_bools =>
    exact smtTermClosedIn_eo_to_smt_from_bools_of_closed_rec_using
      hEnv recX recY hClosed
  case str_concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_concat hx hy)
  case str_contains =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_contains hx hy)
  case str_at =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_at hx hy)
  case str_prefixof =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_prefixof hx hy)
  case str_suffixof =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_suffixof hx hy)
  case str_lt =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_lt hx hy)
  case str_leq =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_leq hx hy)
  case re_range =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_range hx hy)
  case re_concat =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_concat hx hy)
  case re_inter =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_inter hx hy)
  case re_union =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_union hx hy)
  case re_diff =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_re_diff hx hy)
  case str_in_re =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_str_in_re hx hy)
  case seq_nth =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_seq_nth hx hy)
  case _at_strings_num_occur =>
    exact smtTermClosedIn_eo_to_smt_strings_num_occur_of_closed_rec_using
      hEnv recX recY hClosed
  case _at_strings_num_occur_re =>
    exact binary (by decide) (by decide)
      (fun hx hy =>
        smtTermClosedIn_eo_to_smt_strings_num_occur_re hx hy)
  case _at_array_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_array_deq_diff_of_closed_rec_using
      hEnv recX recY hClosed
  case _at_strings_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_strings_deq_diff_of_closed_rec_using
      hEnv recX recY hClosed
  case _at_strings_stoi_result =>
    exact smtTermClosedIn_eo_to_smt_strings_stoi_result_of_closed_rec_using
      hEnv recX recY hClosed
  case _at_strings_itos_result =>
    exact smtTermClosedIn_eo_to_smt_strings_itos_result_of_closed_rec_using
      hEnv recX recY hClosed
  case _at_sets_deq_diff =>
    exact smtTermClosedIn_eo_to_smt_sets_deq_diff_of_closed_rec_using
      hEnv recX recY hClosed
  case tuple =>
    exact smtTermClosedIn_eo_to_smt_tuple_of_closed_rec_using
      hEnv recX recY hClosed
  case set_union =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_union hx hy)
  case set_inter =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_inter hx hy)
  case set_minus =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_minus hx hy)
  case set_member =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_member hx hy)
  case set_subset =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_set_subset hx hy)
  case set_insert =>
    exact smtTermClosedIn_eo_to_smt_set_insert_below
      hEnv hRec hClosed
  case qdiv =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_qdiv hx hy)
  case qdiv_total =>
    exact binary (by decide) (by decide)
      (fun hx hy => smtTermClosedIn_eo_to_smt_qdiv_total hx hy)
  case «forall» =>
    exact smtTermClosedIn_eo_to_smt_forall_of_closed_rec_using
      hEnv recY hClosed
  case «exists» =>
    exact smtTermClosedIn_eo_to_smt_exists_of_closed_rec_using
      hEnv recY hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs hEq => by cases hEq)
      (fun vs hEq => by cases hEq)
      hEnv hRec hClosed

theorem smtTermClosedIn_eo_to_smt_apply_not_binary_uop_below
    {f x env : Term} {vars : List SmtVarKey}
    (hNotBinary :
      ∀ op y, f ≠ Term.Apply (Term.UOp op) y)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hRec :
      ∀ {t env' : Term} {vars' : List SmtVarKey},
        sizeOf t < sizeOf (Term.Apply f x) ->
          EoSmtVarEnvPerm env' vars' ->
            __eo_is_closed_rec t env' = Term.Boolean true ->
              SmtTermClosedIn vars' (__eo_to_smt t))
    (hClosed :
      __eo_is_closed_rec (Term.Apply f x) env =
        Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt (Term.Apply f x)) :=
by
  cases f
  case UOp op =>
    exact smtTermClosedIn_eo_to_smt_apply_uop_any_below
      hEnv hRec hClosed
  case UOp1 op a =>
    exact smtTermClosedIn_eo_to_smt_apply_uop1_any_below
      hEnv hRec hClosed
  case UOp2 op a b =>
    exact smtTermClosedIn_eo_to_smt_apply_uop2_any_below
      hEnv hRec hClosed
  case Apply g y =>
    cases g
    case UOp op =>
      exfalso
      exact hNotBinary op y rfl
    case UOp1 op a =>
      exact smtTermClosedIn_eo_to_smt_apply_apply_uop1_any_below
        hEnv hRec hClosed
    case Apply h z =>
      cases h
      case UOp op =>
        exact smtTermClosedIn_eo_to_smt_apply_apply_apply_uop_any_below
          hEnv hRec hClosed
      case Apply k w =>
        cases k
        case UOp op =>
          cases op
          case _at_strings_replace_all_result =>
            exact
              smtTermClosedIn_eo_to_smt_quaternary_uop_of_closed_rec_using
                (op := UserOp._at_strings_replace_all_result)
                (by decide) (by decide)
                (fun hw hz hy hx =>
                  smtTermClosedIn_eo_to_smt_strings_replace_all_result
                    hw hz hy hx)
                hEnv
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                hClosed
          case _at_strings_replace_re_all_result =>
            exact
              smtTermClosedIn_eo_to_smt_quaternary_uop_of_closed_rec_using
                (op := UserOp._at_strings_replace_re_all_result)
                (by decide) (by decide)
                (fun hw hz hy hx =>
                  smtTermClosedIn_eo_to_smt_strings_replace_re_all_result
                    hw hz hy hx)
                hEnv
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                (fun hEnv' hClosed' =>
                  hRec (by simp; omega) hEnv' hClosed')
                hClosed
          all_goals
            exact smtTermClosedIn_eo_to_smt_apply_generic_below
              (by rfl)
              (fun vs hEq => hNotBinary UserOp.forall vs hEq)
              (fun vs hEq => hNotBinary UserOp.exists vs hEq)
              hEnv hRec hClosed
        all_goals
          exact smtTermClosedIn_eo_to_smt_apply_generic_below
            (by rfl)
            (fun vs hEq => hNotBinary UserOp.forall vs hEq)
            (fun vs hEq => hNotBinary UserOp.exists vs hEq)
            hEnv hRec hClosed
      all_goals
        exact smtTermClosedIn_eo_to_smt_apply_generic_below
          (by rfl)
          (fun vs hEq => hNotBinary UserOp.forall vs hEq)
          (fun vs hEq => hNotBinary UserOp.exists vs hEq)
          hEnv hRec hClosed
    all_goals
      exact smtTermClosedIn_eo_to_smt_apply_generic_below
        (by rfl)
        (fun vs hEq => hNotBinary UserOp.forall vs hEq)
        (fun vs hEq => hNotBinary UserOp.exists vs hEq)
        hEnv hRec hClosed
  all_goals
    exact smtTermClosedIn_eo_to_smt_apply_generic_below
      (by rfl)
      (fun vs hEq => hNotBinary UserOp.forall vs hEq)
      (fun vs hEq => hNotBinary UserOp.exists vs hEq)
      hEnv hRec hClosed

theorem smtTermClosedIn_smt_apply
    {vars : List SmtVarKey} {f x : SmtTerm}
    (hf : SmtTermClosedIn vars f)
    (hx : SmtTermClosedIn vars x) :
  SmtTermClosedIn vars (SmtTerm.Apply f x) :=
by
  exact ⟨hf, hx⟩

theorem smtTermClosedIn_smt_not
    {vars : List SmtVarKey} {x : SmtTerm}
    (hx : SmtTermClosedIn vars x) :
  SmtTermClosedIn vars (SmtTerm.not x) :=
by
  exact hx

theorem smtTermClosedIn_smt_and
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.and x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_or
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.or x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_eq
    {vars : List SmtVarKey} {x y : SmtTerm}
    (hx : SmtTermClosedIn vars x)
    (hy : SmtTermClosedIn vars y) :
  SmtTermClosedIn vars (SmtTerm.eq x y) :=
by
  exact ⟨hx, hy⟩

theorem smtTermClosedIn_smt_exists
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.exists s T body) :=
by
  exact hBody

theorem smtTermClosedIn_smt_forall
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.forall s T body) :=
by
  exact hBody

theorem smtTermClosedIn_smt_choice
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : SmtTermClosedIn ((s, T) :: vars) body) :
  SmtTermClosedIn vars (SmtTerm.choice s T body) :=
by
  exact hBody

theorem smtTermClosedIn_smt_bind
    {vars : List SmtVarKey} {s : native_String} {T : SmtType}
    {x1 x2 : SmtTerm}
    (hx1 : SmtTermClosedIn vars x1)
    (hx2 : SmtTermClosedIn ((s, T) :: vars) x2) :
  SmtTermClosedIn vars (SmtTerm.bind s T x1 x2) :=
by
  exact ⟨hx1, hx2⟩

theorem smtx_model_eval_var_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType}
    (hAgree : model_agrees_on_env vars M N)
    (hClosed : SmtTermClosedIn vars (SmtTerm.Var s T)) :
  __smtx_model_eval M (SmtTerm.Var s T) =
    __smtx_model_eval N (SmtTerm.Var s T) :=
by
  simp [__smtx_model_eval, native_model_var_lookup_eq_of_env hAgree hClosed]

theorem smtx_model_eval_uconst_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType}
    (hAgree : model_agrees_on_env vars M N) :
  __smtx_model_eval M (SmtTerm.UConst s T) =
    __smtx_model_eval N (SmtTerm.UConst s T) :=
by
  simp [__smtx_model_eval, native_model_lookup_eq_of_env hAgree]

theorem smtx_model_eval_apply_eq_of_env
    {vars : List SmtVarKey} {M N : SmtModel} {f x : SmtTerm}
    (hAgree : model_agrees_on_env vars M N)
    (hf :
      __smtx_model_eval M f = __smtx_model_eval N f)
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x) :
  __smtx_model_eval M (SmtTerm.Apply f x) =
    __smtx_model_eval N (SmtTerm.Apply f x) :=
by
  cases f <;>
    first
    | -- `DtSel`/`DtTester` heads (and any head with no `M`/`N` dependence):
      -- close via the globals bridge lemmas; `done` forces fallthrough otherwise.
      (simp only [__smtx_model_eval]
       simp [hx,
         smtx_model_eval_dt_sel_eq_of_globals hAgree.globals,
         smtx_model_eval_apply_eq_of_globals hAgree.globals]
       done)
    | -- General application head: rewrite the head value via `hf` before the
      -- globals lemmas can partially rewrite its subterms, then bridge `M`/`N`.
      (simp only [__smtx_model_eval] at hf ⊢
       rw [hf, hx]
       exact smtx_model_eval_apply_eq_of_globals hAgree.globals _ _)

theorem smtx_model_eval_not_eq_of_eval_eq
    {M N : SmtModel} {x : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x) :
  __smtx_model_eval M (SmtTerm.not x) =
    __smtx_model_eval N (SmtTerm.not x) :=
by
  simp [__smtx_model_eval, hx]

theorem smtx_model_eval_and_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.and x y) =
    __smtx_model_eval N (SmtTerm.and x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_or_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.or x y) =
    __smtx_model_eval N (SmtTerm.or x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_imp_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.imp x y) =
    __smtx_model_eval N (SmtTerm.imp x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_xor_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.xor x y) =
    __smtx_model_eval N (SmtTerm.xor x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_eq_eq_of_eval_eq
    {M N : SmtModel} {x y : SmtTerm}
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.eq x y) =
    __smtx_model_eval N (SmtTerm.eq x y) :=
by
  simp [__smtx_model_eval, hx, hy]

theorem smtx_model_eval_exists_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  __smtx_model_eval M (SmtTerm.exists s T body) =
    __smtx_model_eval N (SmtTerm.exists s T body) :=
by
  simp [__smtx_model_eval, native_eval_texists_eq_of_body_eval_eq hBody]

theorem smtx_model_eval_forall_eq_of_body_eval_eq
    {M N : SmtModel} {s : native_String} {T : SmtType}
    {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
  __smtx_model_eval M (SmtTerm.forall s T body) =
    __smtx_model_eval N (SmtTerm.forall s T body) :=
by
  simp [__smtx_model_eval, native_eval_tforall_eq_of_body_eval_eq hBody]

/-- A formula remains true when only SMT variable assignments are changed. -/
def StableInAnyVarModel (M : SmtModel) (P : Term) : Prop :=
  ∀ N, model_wf N -> model_agrees_on_globals M N ->
    eo_interprets N P true

/-- A formula remains true under variable-model changes whenever it is true. -/
def StableWhenTrueInAnyVarModel (P : Term) : Prop :=
  ∀ M, model_wf M -> eo_interprets M P true ->
    StableInAnyVarModel M P

theorem smt_interprets_of_model_eval_eq
    {M N : SmtModel} {t : SmtTerm} {b : Bool}
    (hEval : __smtx_model_eval M t = __smtx_model_eval N t) :
  smt_interprets M t b ->
    smt_interprets N t b :=
by
  intro h
  cases h with
  | intro_true hTy hTrue =>
      exact smt_interprets.intro_true N t hTy (by
        simpa [← hEval] using hTrue)
  | intro_false hTy hFalse =>
      exact smt_interprets.intro_false N t hTy (by
        simpa [← hEval] using hFalse)

theorem eo_interprets_of_smt_model_eval_eq
    {M N : SmtModel} {P : Term} {b : Bool}
    (hEval :
      __smtx_model_eval M (__eo_to_smt P) =
        __smtx_model_eval N (__eo_to_smt P)) :
  eo_interprets M P b ->
    eo_interprets N P b :=
by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  exact smt_interprets_of_model_eval_eq hEval

theorem stableWhenTrueInAnyVarModel_of_smt_model_eval_eq
    (P : Term)
    (hEval : ∀ M N : SmtModel,
      model_agrees_on_globals M N ->
        __smtx_model_eval M (__eo_to_smt P) =
          __smtx_model_eval N (__eo_to_smt P)) :
  StableWhenTrueInAnyVarModel P :=
by
  intro M _ hTrue N _ hAgree
  exact eo_interprets_of_smt_model_eval_eq (hEval M N hAgree) hTrue


/--
Remaining translation invariant for closed EO formulas.

Executable EO closedness should imply closedness of the translated SMT term in
the empty SMT-variable environment.
-/
theorem smtTermClosedIn_of_eo_is_closed_rec_perm_lt
    (n : Nat) {t env : Term} {vars : List SmtVarKey}
    (hLt : sizeOf t < n)
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed : __eo_is_closed_rec t env = Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt t) :=
by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u env' : Term} {vars' : List SmtVarKey},
            sizeOf u < sizeOf t ->
              EoSmtVarEnvPerm env' vars' ->
                __eo_is_closed_rec u env' = Term.Boolean true ->
                  SmtTermClosedIn vars' (__eo_to_smt u) :=
        fun {u env'} {vars'} hULt hEnv' hClosed' =>
          smtTermClosedIn_of_eo_is_closed_rec_perm_lt
            n (t := u) (env := env') (vars := vars')
            (by omega) hEnv' hClosed'
      cases t
      case UOp op =>
        exact smtTermClosedIn_eo_to_smt_uop vars op
      case UOp1 op x =>
        exact smtTermClosedIn_eo_to_smt_uop1_any_below
          hEnv hRec hClosed
      case UOp2 op x y =>
        exact smtTermClosedIn_eo_to_smt_uop2_any_below
          hEnv hRec hClosed
      case UOp3 op x y z =>
        exact smtTermClosedIn_eo_to_smt_uop3_any_below
          hEnv hRec hClosed
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            exact smtTermClosedIn_eo_to_smt_apply_apply_uop_any_below
              hEnv hRec hClosed
          all_goals
            exact smtTermClosedIn_eo_to_smt_apply_not_binary_uop_below
              (by intro op y h; cases h)
              hEnv hRec hClosed
        all_goals
          exact smtTermClosedIn_eo_to_smt_apply_not_binary_uop_below
            (by intro op y h; cases h)
            hEnv hRec hClosed
      case Boolean b =>
        exact smtTermClosedIn_eo_to_smt_boolean vars b
      case Numeral n =>
        exact smtTermClosedIn_eo_to_smt_numeral vars n
      case Rational r =>
        exact smtTermClosedIn_eo_to_smt_rational vars r
      case String s =>
        exact smtTermClosedIn_eo_to_smt_string vars s
      case Binary w n =>
        exact smtTermClosedIn_eo_to_smt_binary vars w n
      case Var name T =>
        exact smtTermClosedIn_eo_to_smt_var_of_closed_rec_perm
          hEnv hClosed
      case DtCons s d i =>
        exact smtTermClosedIn_eo_to_smt_dtcons vars s d i
      case DtSel s d i j =>
        exact smtTermClosedIn_eo_to_smt_dtsel vars s d i j
      case UConst i T =>
        exact smtTermClosedIn_eo_to_smt_uconst vars i T
      all_goals
        trivial
termination_by n
decreasing_by
  all_goals omega

theorem smtTermClosedIn_of_eo_is_closed_rec_perm
    {t env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnvPerm env vars)
    (hClosed : __eo_is_closed_rec t env = Term.Boolean true) :
  SmtTermClosedIn vars (__eo_to_smt t) :=
by
  exact smtTermClosedIn_of_eo_is_closed_rec_perm_lt
    (sizeOf t + 1) (by omega) hEnv hClosed

theorem smtTermClosedIn_of_eo_is_closed
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true) :
  SmtTermClosedIn [] (__eo_to_smt P) :=
by
  exact smtTermClosedIn_of_eo_is_closed_rec_perm
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil)
    (eo_is_closed_eq_true_rec_nil hClosed)

/--
Remaining structural SMT evaluator invariant.

If two models agree on all globals and on the currently bound SMT variables,
then every SMT term closed in that environment evaluates identically in them.
-/
theorem smt_model_eval_eq_of_closedIn_lt
    (n : Nat) {t : SmtTerm} {vars : List SmtVarKey} {M N : SmtModel}
    (hLt : sizeOf t < n)
    (hClosed : SmtTermClosedIn vars t)
    (hAgree : model_agrees_on_env vars M N) :
  __smtx_model_eval M t = __smtx_model_eval N t :=
by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u : SmtTerm} {vars' : List SmtVarKey} {M' N' : SmtModel},
            sizeOf u < sizeOf t ->
              SmtTermClosedIn vars' u ->
                model_agrees_on_env vars' M' N' ->
                  __smtx_model_eval M' u = __smtx_model_eval N' u :=
        fun {u vars' M' N'} hULt hClosed' hAgree' =>
          smt_model_eval_eq_of_closedIn_lt
            n (t := u) (vars := vars') (M := M') (N := N')
            (by omega) hClosed' hAgree'
      let hEval :
          ∀ {u : SmtTerm} {vars' : List SmtVarKey} {M' N' : SmtModel},
              SmtTermClosedIn vars' u ->
                model_agrees_on_env vars' M' N' ->
                  sizeOf u < sizeOf t ->
                    __smtx_model_eval M' u = __smtx_model_eval N' u :=
        fun {u vars' M' N'} hClosed' hAgree' hULt =>
          hRec hULt hClosed' hAgree'
      let hEvalSame :
          ∀ u : SmtTerm,
              SmtTermClosedIn vars u ->
                sizeOf u < sizeOf t ->
                  __smtx_model_eval M u = __smtx_model_eval N u :=
        fun u hClosed' hULt =>
          hRec hULt hClosed' hAgree
      cases t <;> simp [SmtTermClosedIn] at hClosed ⊢
      case Var s T =>
        exact smtx_model_eval_var_eq_of_env hAgree hClosed
      case UConst s T =>
        exact smtx_model_eval_uconst_eq_of_env hAgree
      case Apply f x =>
        exact smtx_model_eval_apply_eq_of_env hAgree
          (hRec (by simp; omega) hClosed.1 hAgree)
          (hRec (by simp; omega) hClosed.2 hAgree)
      case «exists» s T body =>
        exact smtx_model_eval_exists_eq_of_body_eval_eq
          (fun v =>
            hRec (by simp; omega) hClosed
              (model_agrees_on_env_push_same hAgree))
      case «forall» s T body =>
        exact smtx_model_eval_forall_eq_of_body_eval_eq
          (fun v =>
            hRec (by simp; omega) hClosed
              (model_agrees_on_env_push_same hAgree))
      case choice s T body =>
        rw [smtx_model_eval_choice_eq M s T body,
          smtx_model_eval_choice_eq N s T body]
        exact native_eval_tchoice_eq_of_body_eval_eq
          (fun v =>
            hRec (by simp; omega) hClosed
              (model_agrees_on_env_push_same hAgree))
      case bind s T x1 x2 =>
        rw [smtx_model_eval_bind_eq M s T x1 x2,
          smtx_model_eval_bind_eq N s T x1 x2]
        have hx1 : __smtx_model_eval M x1 = __smtx_model_eval N x1 :=
          hRec (by simp; omega) hClosed.1 hAgree
        rw [hx1]
        exact hRec (by simp; omega) hClosed.2
          (model_agrees_on_env_push_same hAgree)
      case not x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case _at_purify x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case to_real x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case to_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case is_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case abs x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case uneg x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case int_pow2 x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case int_log2 x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case bvnot x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case bvneg x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case bvnego x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_len x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_rev x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_to_lower x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_to_upper x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_to_code x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_from_code x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_is_digit x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_to_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_from_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case str_to_re x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case re_mult x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case re_plus x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case re_opt x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case re_comp x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case seq_unit x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case set_singleton x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case ubv_to_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      case sbv_to_int x =>
        simp [__smtx_model_eval,
          hRec (by simp) hClosed hAgree]
      all_goals try
        simp [__smtx_model_eval, hAgree.globals.1,
          smtx_model_eval_apply_eq_of_globals hAgree.globals,
          smtx_seq_nth_eq_of_globals hAgree.globals]
      all_goals try
        rw [hEvalSame _ hClosed.1 (by simp; omega),
          hEvalSame _ hClosed.2 (by simp; omega)]
      all_goals try
        rw [hEvalSame _ hClosed.1 (by simp; omega),
          hEvalSame _ hClosed.2.1 (by simp; omega),
          hEvalSame _ hClosed.2.2 (by simp; omega)]
      all_goals try
        simp [hAgree.globals.1, hAgree.globals.2,
          smtx_model_eval_apply_eq_of_globals hAgree.globals,
          smtx_seq_nth_eq_of_globals hAgree.globals,
          smtx_model_eval_dt_sel_eq_of_globals hAgree.globals]
termination_by n
decreasing_by
  all_goals omega

theorem smt_model_eval_eq_of_closedIn
    (t : SmtTerm) (vars : List SmtVarKey) (M N : SmtModel)
    (hClosed : SmtTermClosedIn vars t)
    (hAgree : model_agrees_on_env vars M N) :
  __smtx_model_eval M t = __smtx_model_eval N t :=
by
  exact smt_model_eval_eq_of_closedIn_lt
    (sizeOf t + 1) (by omega) hClosed hAgree

theorem smt_model_eval_eq_of_eo_closed_in_empty_env
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true)
    (M N : SmtModel) (hAgree : model_agrees_on_env [] M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_closedIn (__eo_to_smt P) [] M N
    (smtTermClosedIn_of_eo_is_closed P hClosed) hAgree

theorem smt_model_eval_eq_of_eo_smt_closed
    {P : Term} {M N : SmtModel}
    (hClosed : SmtTermClosedIn [] (__eo_to_smt P))
    (hAgree : model_agrees_on_globals M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_closedIn (__eo_to_smt P) [] M N hClosed
    (model_agrees_on_env_nil_of_globals hAgree)

/-- Closed EO formula evaluation is insensitive to variable-model changes. -/
theorem smt_model_eval_eq_of_eo_closed
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true)
    (M N : SmtModel) (hAgree : model_agrees_on_globals M N) :
  __smtx_model_eval M (__eo_to_smt P) =
    __smtx_model_eval N (__eo_to_smt P) :=
by
  exact smt_model_eval_eq_of_eo_closed_in_empty_env P hClosed M N
    (model_agrees_on_env_nil_of_globals hAgree)

/--
Closed EO formulas are stable under changes to SMT variable assignments.

This is now derived from `smt_model_eval_eq_of_eo_closed`; the remaining proof
work is the evaluator invariant, not the high-level checker stability property.
-/
theorem stableWhenTrueInAnyVarModel_of_closed
    (P : Term) (hClosed : __eo_is_closed P = Term.Boolean true) :
  StableWhenTrueInAnyVarModel P :=
by
  exact stableWhenTrueInAnyVarModel_of_smt_model_eval_eq P
    (fun M N hAgree => smt_model_eval_eq_of_eo_closed P hClosed M N hAgree)
