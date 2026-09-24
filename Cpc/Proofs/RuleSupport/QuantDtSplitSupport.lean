module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.RuleSupport.DtConsEqSupport
import all Cpc.Proofs.RuleSupport.DtConsEqSupport
public import Cpc.Proofs.RuleSupport.QdsCtor
import all Cpc.Proofs.RuleSupport.QdsCtor
public import Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
import all Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
public import Cpc.Proofs.TypePreservation
import all Cpc.Proofs.TypePreservation

public section

open Eo
open SmtEval
open Smtm

/-!
Support lemmas for the rule `quant_dt_split`:

* list-view spine decomposition of SMT values and the reconstruction form of
  datatype exhaustiveness (`datatype_value_spine`);
* the two-sided truth characterization of a translated universal quantifier
  (`forall_encoding_true_iff`);
* syntactic reification of the guard (`ConjRel`/`SplitRel`) with extraction
  from a successful run (`conjRel_of_guard_true`, `splitRel_of_guard_true`).
-/

namespace QuantDtSplitRule

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open InstantiateRule

/-- Application spine, accumulator style: `vsmMkSpine h [a, b] = Apply (Apply h a) b`. -/
def vsmMkSpine (head : SmtValue) : List SmtValue -> SmtValue
  | [] => head
  | a :: args => vsmMkSpine (SmtValue.Apply head a) args

/-- The arguments of a value's application spine, outermost last. -/
def vsmArgs : SmtValue -> List SmtValue
  | SmtValue.Apply f a => vsmArgs f ++ [a]
  | _ => []

@[simp] private theorem vsmMkSpine_nil (h : SmtValue) : vsmMkSpine h [] = h := rfl

@[simp] private theorem vsmMkSpine_cons (h a : SmtValue) (args : List SmtValue) :
    vsmMkSpine h (a :: args) = vsmMkSpine (SmtValue.Apply h a) args := rfl

theorem vsmMkSpine_append_singleton (args : List SmtValue) :
    ∀ (h a : SmtValue), vsmMkSpine h (args ++ [a]) = SmtValue.Apply (vsmMkSpine h args) a := by
  induction args with
  | nil => intro h a; rfl
  | cons b args ih =>
      intro h a
      rw [List.cons_append, vsmMkSpine_cons, vsmMkSpine_cons, ih]

theorem vsmArgs_vsmMkSpine : ∀ (head : SmtValue) (args : List SmtValue),
    vsmArgs (vsmMkSpine head args) = vsmArgs head ++ args := by
  intro head args
  induction args generalizing head with
  | nil => simp
  | cons a args ih =>
      rw [vsmMkSpine_cons, ih]
      simp [vsmArgs, List.append_assoc]

/-- Every value is the spine of its head applied to its arguments. -/
theorem vsm_spine_decomposition :
    ∀ v : SmtValue, v = vsmMkSpine (__smtx_apply_head_value v) (vsmArgs v)
  | SmtValue.Apply f a => by
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl,
        show __smtx_apply_head_value (SmtValue.Apply f a) = __smtx_apply_head_value f from rfl,
        vsmMkSpine_append_singleton]
      exact congrArg (SmtValue.Apply · a) (vsm_spine_decomposition f)
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

theorem vsmArgs_length : ∀ v : SmtValue, (vsmArgs v).length = vsm_num_apply_args v
  | SmtValue.Apply f a => by
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl,
        show vsm_num_apply_args (SmtValue.Apply f a) = Nat.succ (vsm_num_apply_args f) from rfl,
        List.length_append, vsmArgs_length f]
      simp
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ _ _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

/-- The index-based accessor reads the list view. -/
theorem vsm_apply_arg_nth_eq_getElem :
    ∀ (v : SmtValue) (j : Nat), j < (vsmArgs v).length ->
      __smtx_apply_arg_nth_value v j (vsm_num_apply_args v) = (vsmArgs v)[j]!
  | SmtValue.Apply f a => by
      intro j hj
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl] at hj ⊢
      rw [show vsm_num_apply_args (SmtValue.Apply f a) = Nat.succ (vsm_num_apply_args f) from rfl,
        show __smtx_apply_arg_nth_value (SmtValue.Apply f a) j (Nat.succ (vsm_num_apply_args f)) =
          native_ite (native_nateq j (vsm_num_apply_args f)) a
            (__smtx_apply_arg_nth_value f j (vsm_num_apply_args f)) from rfl]
      by_cases hEq : j = vsm_num_apply_args f
      · have hbeq : native_nateq j (vsm_num_apply_args f) = true := by
          simp [native_nateq, hEq]
        rw [hbeq]
        have hj' : j = (vsmArgs f).length := by rw [vsmArgs_length f]; exact hEq
        subst hj'
        have : (vsmArgs f ++ [a])[(vsmArgs f).length]! = a := by simp
        rw [this]
        rfl
      · have hbeq : native_nateq j (vsm_num_apply_args f) = false := by
          simp [native_nateq, hEq]
        rw [hbeq]
        have hjf : j < (vsmArgs f).length := by
          rw [List.length_append] at hj
          rw [vsmArgs_length f]
          rw [vsmArgs_length f] at hj
          simp at hj
          omega
        have : (vsmArgs f ++ [a])[j]! = (vsmArgs f)[j]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left hjf]
        rw [this, ← vsm_apply_arg_nth_eq_getElem f j hjf]
        rfl
  | SmtValue.NotValue => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Boolean _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Numeral _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Rational _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Binary _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Map _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Fun _ _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Set _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Seq _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.Char _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.UValue _ _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.RegLan _ => by intro j hj; simp [vsmArgs] at hj
  | SmtValue.DtCons _ _ _ => by intro j hj; simp [vsmArgs] at hj

/-- Canonicity of a spine gives canonicity of head and all arguments. -/
theorem vsm_canonical_spine :
    ∀ v : SmtValue,
      __smtx_value_canonical v = true ->
      __smtx_value_canonical (__smtx_apply_head_value v) = true ∧
        ∀ a ∈ vsmArgs v, __smtx_value_canonical a = true
  | SmtValue.Apply f a => by
      intro hCanon
      rw [show __smtx_value_canonical (SmtValue.Apply f a) =
        native_and (__smtx_value_canonical f) (__smtx_value_canonical a) from rfl]
        at hCanon
      have hf : __smtx_value_canonical f = true := by
        cases hcf : __smtx_value_canonical f
        · rw [hcf] at hCanon; cases hCanon
        · rfl
      have ha : __smtx_value_canonical a = true := by
        rw [hf] at hCanon
        cases hca : __smtx_value_canonical a
        · rw [hca] at hCanon; cases hCanon
        · rfl
      obtain ⟨hHead, hArgs⟩ := vsm_canonical_spine f hf
      refine ⟨hHead, ?_⟩
      intro b hb
      rw [show vsmArgs (SmtValue.Apply f a) = vsmArgs f ++ [a] from rfl] at hb
      rcases List.mem_append.1 hb with hbf | hba
      · exact hArgs b hbf
      · rw [List.mem_singleton.1 hba]; exact ha
  | SmtValue.NotValue => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Boolean _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Numeral _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Rational _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Binary _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Map _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Fun _ _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Set _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Seq _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.Char _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.UValue _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.RegLan _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩
  | SmtValue.DtCons _ _ _ => fun h => ⟨h, by intro a ha; simp [vsmArgs] at ha⟩

/-- Canonicity of a spine from canonicity of head and arguments (converse). -/
theorem vsm_canonical_of_spine (args : List SmtValue) :
    ∀ head : SmtValue,
      __smtx_value_canonical head = true ->
      (∀ a ∈ args, __smtx_value_canonical a = true) ->
      __smtx_value_canonical (vsmMkSpine head args) = true := by
  induction args with
  | nil => intro head hHead _; simpa using hHead
  | cons a args ih =>
      intro head hHead hArgs
      rw [vsmMkSpine_cons]
      refine ih (SmtValue.Apply head a) ?_ ?_
      · rw [show __smtx_value_canonical (SmtValue.Apply head a) =
          native_and (__smtx_value_canonical head) (__smtx_value_canonical a) from rfl,
          hHead, hArgs a (List.mem_cons_self ..)]
        rfl
      · intro b hb
        exact hArgs b (List.mem_cons_of_mem a hb)

theorem vsmMkSpine_dtcons_type_aux
    (s : native_String) (d0 : SmtDatatypeDecl) (d : SmtDatatype)
    (i : native_Nat)
    (total : Nat)
    (hTotal : total ≤ __smtx_dt_num_sels d i)
    (hRetWf : ∀ j, j < total ->
      __smtx_type_wf (__smtx_ret_typeof_sel_rec d i j) = true) :
    ∀ (args : List SmtValue) (head : SmtValue) (n : Nat),
      __smtx_typeof_value head =
          dt_cons_applied_type_rec s d0 d i n ->
      n + args.length ≤ total ->
      (∀ j, j < args.length ->
        __smtx_typeof_value args[j]! =
          __smtx_ret_typeof_sel_rec d i (n + j)) ->
      __smtx_typeof_value (vsmMkSpine head args) =
        dt_cons_applied_type_rec s d0 d i (n + args.length) := by
  intro args
  induction args with
  | nil =>
      intro head n hHead hBound hTypes
      simpa [vsmMkSpine] using hHead
  | cons a args ih =>
      intro head n hHead hBound hTypes
      simp only [List.length_cons] at hBound
      have hnLt : n < __smtx_dt_num_sels d i := by
        omega
      have hStep := dt_cons_applied_type_rec_step s d0 d i n hnLt
      have hATy : __smtx_typeof_value a =
          __smtx_ret_typeof_sel_rec d i n := by
        simpa using hTypes 0 (by simp)
      have hRetNN : __smtx_ret_typeof_sel_rec d i n ≠ SmtType.None := by
        intro hNone
        have hBad := hRetWf n (by omega)
        rw [hNone] at hBad
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hBad
      have hApplyTy : __smtx_typeof_value (SmtValue.Apply head a) =
          dt_cons_applied_type_rec s d0 d i (Nat.succ n) := by
        change __smtx_typeof_apply_value
          (__smtx_typeof_value head) (__smtx_typeof_value a) = _
        rw [hHead, hStep, hATy]
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
          hRetNN, native_ite, native_Teq]
      rw [vsmMkSpine_cons]
      have hRec := ih (SmtValue.Apply head a) (Nat.succ n) hApplyTy
        (by omega) (by
          intro j hj
          have hTy := hTypes (Nat.succ j)
            (by simpa using Nat.succ_lt_succ hj)
          simpa [Nat.succ_add, Nat.add_assoc] using hTy)
      change __smtx_typeof_value
          (vsmMkSpine (SmtValue.Apply head a) args) =
        dt_cons_applied_type_rec s d0 d i (n + Nat.succ args.length)
      rw [show n + Nat.succ args.length = Nat.succ n + args.length by omega]
      exact hRec

theorem vsmMkSpine_dtcons_type
    (s : native_String) (d0 : SmtDatatypeDecl) (d : SmtDatatype)
    (i : native_Nat)
    (args : List SmtValue)
    (hRoot : __smtx_typeof_value (SmtValue.DtCons s d0 i) =
      dt_cons_applied_type_rec s d0 d i 0)
    (hBound : args.length ≤ __smtx_dt_num_sels d i)
    (hRetWf : ∀ j, j < __smtx_dt_num_sels d i ->
      __smtx_type_wf (__smtx_ret_typeof_sel_rec d i j) = true)
    (hTypes : ∀ j, j < args.length ->
      __smtx_typeof_value args[j]! =
        __smtx_ret_typeof_sel_rec d i j) :
    __smtx_typeof_value
        (vsmMkSpine (SmtValue.DtCons s d0 i) args) =
      dt_cons_applied_type_rec s d0 d i args.length := by
  simpa using
    (vsmMkSpine_dtcons_type_aux s d0 d i
      (__smtx_dt_num_sels d i) (Nat.le_refl _) hRetWf args
      (SmtValue.DtCons s d0 i) 0 hRoot (by simpa using hBound)
      (by simpa using hTypes))

theorem list_take_succ_eq_append_getElem! :
    ∀ (xs : List SmtValue) (k : Nat), k < xs.length ->
      xs.take (Nat.succ k) = xs.take k ++ [xs[k]!]
  | [], k, hk => by simp at hk
  | x :: xs, 0, hk => by simp
  | x :: xs, Nat.succ k, hk => by
      have hk' : k < xs.length := by simpa using hk
      simp [List.take_succ_cons,
        list_take_succ_eq_append_getElem! xs k hk']

theorem tuplePrependValueRec_vsmMkSpine_prefix
    (tailD : SmtDatatype) (root : SmtValue) (args : List SmtValue)
    (hRootArgs : vsmArgs root = [])
    (hLen : args.length =
      __smtx_dt_num_sels tailD native_nat_zero) :
    ∀ (k : Nat) (acc : SmtValue), k ≤ args.length ->
      tuplePrependValueRec tailD (vsmMkSpine root args) k acc =
        vsmMkSpine acc (args.take k) := by
  intro k
  induction k with
  | zero =>
      intro acc hk
      simp [tuplePrependValueRec]
  | succ k ih =>
      intro acc hk
      have hkLt : k < args.length := Nat.lt_of_succ_le hk
      have hView : vsmArgs (vsmMkSpine root args) = args := by
        rw [vsmArgs_vsmMkSpine]
        rw [hRootArgs]
        rfl
      have hCount : vsm_num_apply_args (vsmMkSpine root args) = args.length := by
        rw [← vsmArgs_length, hView]
      have hArg := vsm_apply_arg_nth_eq_getElem
        (vsmMkSpine root args) k (by simpa [hView] using hkLt)
      rw [hCount, hView] at hArg
      simp only [tuplePrependValueRec]
      rw [ih acc (Nat.le_of_succ_le hk)]
      rw [← hLen]
      rw [hArg, list_take_succ_eq_append_getElem! args k hkLt,
        vsmMkSpine_append_singleton]

theorem tuplePrependValueRec_vsmMkSpine
    (tailD : SmtDatatype) (root : SmtValue) (args : List SmtValue)
    (acc : SmtValue)
    (hRootArgs : vsmArgs root = [])
    (hLen : args.length =
      __smtx_dt_num_sels tailD native_nat_zero) :
    tuplePrependValueRec tailD (vsmMkSpine root args)
        (__smtx_dt_num_sels tailD native_nat_zero) acc =
      vsmMkSpine acc args := by
  rw [← hLen]
  simpa using tuplePrependValueRec_vsmMkSpine_prefix
    tailD root args hRootArgs hLen args.length acc (Nat.le_refl _)

/--
Reconstruction form of datatype exhaustiveness: every value of a datatype sort
is a constructor spine with in-range index, correct arity, and arguments typed
by the (substituted) selector types.
-/
theorem datatype_value_spine
    {v : SmtValue} {s : native_String} {d : SmtDatatypeDecl}
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ (i : Nat) (args : List SmtValue),
      v = vsmMkSpine (SmtValue.DtCons s d i) args ∧
      i < smtDatatypeNumCtors (__smtx_dd_lookup s d) ∧
      args.length =
        __smtx_dt_num_sels
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i ∧
      (∀ j : Nat, j < args.length ->
        __smtx_typeof_value args[j]! =
          __smtx_ret_typeof_sel_rec
            (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i j) := by
  obtain ⟨i, hHead⟩ := datatype_value_head_of_type hTy
  refine ⟨i, vsmArgs v, ?_, ?_, ?_, ?_⟩
  · have := vsm_spine_decomposition v
    rwa [hHead] at this
  · exact datatype_head_index_lt hHead hTy
  · rw [vsmArgs_length]
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  · intro j hj
    have hjn : j < vsm_num_apply_args v := by rwa [vsmArgs_length] at hj
    have hNone : __smtx_typeof_value v ≠ SmtType.None := by
      rw [hTy]; intro h; cases h
    have := apply_arg_nth_type_of_non_none hHead hNone hjn
    rw [vsm_apply_arg_nth_eq_getElem v j hj] at this
    exact this

/-! ## Truth characterization of translated universals -/


theorem smtx_model_eval_not_unfold (M : SmtModel) (t : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not t) =
      __smtx_model_eval_not (__smtx_model_eval M t) := by
  simp only [__smtx_model_eval]

/-- Introduction direction: body true under every instantiation makes the
    encoded forall true. -/
theorem forall_encoding_true_of_all_inst
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf : ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    ∀ M : SmtModel, model_wf M ->
    (∀ N, ForallInstantiationModel M xs N ->
      __smtx_model_eval N body = SmtValue.Boolean true) ->
    __smtx_model_eval M (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
      SmtValue.Boolean true := by
  classical
  induction hEnv with
  | nil =>
      intro M _hM h
      have hBody : __smtx_model_eval M body = SmtValue.Boolean true :=
        h M (ForallInstantiationModel.nil M)
      rw [show __eo_to_smt_exists Term.__eo_List_nil (SmtTerm.not body) =
        SmtTerm.not body from rfl]
      rw [smtx_model_eval_not_unfold, smtx_model_eval_not_unfold, hBody]
      rfl
  | cons hTail ih =>
      rename_i s T env tailVars
      intro M hM h
      rw [show __eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env) (SmtTerm.not body) =
        SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists env (SmtTerm.not body)) from rfl]
      have hHeadWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf s T (List.Mem.head _)
      have hnP : ¬ (∃ v : SmtValue,
          __smtx_typeof_value v = __eo_to_smt_type T ∧
            __smtx_value_canonical v = true ∧
              __smtx_model_eval
                (native_model_push M s (__eo_to_smt_type T) v)
                (__eo_to_smt_exists env (SmtTerm.not body)) =
                SmtValue.Boolean true) := by
        rintro ⟨v, hvT, hvC, hvE⟩
        have hPushTotal :
            model_wf (native_model_push M s (__eo_to_smt_type T) v) :=
          model_total_typed_push hM s (__eo_to_smt_type T) v hHeadWf hvT
            (by simpa [value_canonical] using hvC)
        have hInner :
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
              (SmtTerm.not (__eo_to_smt_exists env (SmtTerm.not body))) =
              SmtValue.Boolean true := by
          refine ih
            (by
              intro s' T' hMem
              exact hWf s' T' (List.Mem.tail _ hMem))
            (native_model_push M s (__eo_to_smt_type T) v) hPushTotal ?_
          intro N hInst
          exact h N (ForallInstantiationModel.cons hHeadWf hvT hvC hInst)
        rw [smtx_model_eval_not_unfold] at hInner
        have hFalse :
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
              (__eo_to_smt_exists env (SmtTerm.not body)) =
              SmtValue.Boolean false :=
          (smtx_model_eval_not_true_iff _).1 hInner
        rw [hFalse] at hvE
        exact absurd hvE (by decide)
      have hExFalse :
          __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env (SmtTerm.not body))) =
            SmtValue.Boolean false := by
        show (if _ : (∃ v : SmtValue,
            __smtx_typeof_value v = __eo_to_smt_type T ∧
              __smtx_value_canonical v = true ∧
                __smtx_model_eval
                  (native_model_push M s (__eo_to_smt_type T) v)
                  (__eo_to_smt_exists env (SmtTerm.not body)) =
                  SmtValue.Boolean true)
          then SmtValue.Boolean true else SmtValue.Boolean false) =
          SmtValue.Boolean false
        rw [dif_neg hnP]
      rw [smtx_model_eval_not_unfold, hExFalse]
      rfl

/-- Two-sided characterization of the truth of an encoded universal. -/
theorem forall_encoding_true_iff
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf : ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (M : SmtModel) (hM : model_wf M) :
    __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true ↔
      ∀ N, ForallInstantiationModel M xs N ->
        __smtx_model_eval N body = SmtValue.Boolean true := by
  constructor
  · intro hEval N hInst
    exact forall_instantiation_body_true hInst hM hBodyTy hEval
  · exact forall_encoding_true_of_all_inst hEnv hWf hBodyTy M hM

/-! ## Guard reification -/

/-- `cons` cell of an EO list. -/
abbrev eoCons (a l : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons a) l

/-- EO `forall` with binder list `vs` and body `B`. -/
abbrev mkForall (vs B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) B

/-- EO `and` application. -/
abbrev mkAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

/-- Singleton-list substitution of `x` by `t` in `F` as used by the guard. -/
abbrev substOne (x t F : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) F
    (eoCons x Term.__eo_List_nil) (eoCons t Term.__eo_List_nil)
    Term.__eo_List_nil

/-! ### Eliminators for the EO control primitives -/

theorem eo_requires_boolean_true_elim {a b c : Term}
    (h : __eo_requires a b c = Term.Boolean true) :
    a = b ∧ a ≠ Term.Stuck ∧ c = Term.Boolean true := by
  rw [__eo_requires] at h
  by_cases hab : native_teq a b = true
  · rw [hab] at h
    simp only [native_ite, if_true] at h
    by_cases hStuck : native_teq a Term.Stuck = true
    · rw [hStuck] at h
      simp [native_not] at h
    · have : native_teq a Term.Stuck = false := by
        cases hv : native_teq a Term.Stuck
        · rfl
        · exact absurd hv hStuck
      rw [this] at h
      simp only [native_not, Bool.not_false, native_ite, if_true] at h
      refine ⟨by simpa [native_teq] using hab, ?_, h⟩
      intro hEq
      rw [hEq] at this
      simp [native_teq] at this
  · have : native_teq a b = false := by
      cases hv : native_teq a b
      · rfl
      · exact absurd hv hab
    rw [this] at h
    simp only [native_ite, if_false] at h
    cases h

theorem eo_ite_boolean_true_elim {c t e : Term}
    (h : __eo_ite c t e = Term.Boolean true) :
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  rw [__eo_ite] at h
  by_cases hc : native_teq c (Term.Boolean true) = true
  · left
    refine ⟨by simpa [native_teq] using hc, ?_⟩
    rw [hc] at h
    exact h
  · have hcf : native_teq c (Term.Boolean true) = false := by
      cases hv : native_teq c (Term.Boolean true)
      · rfl
      · exact absurd hv hc
    rw [hcf] at h
    simp only [native_ite, if_false] at h
    by_cases hc2 : native_teq c (Term.Boolean false) = true
    · right
      refine ⟨by simpa [native_teq] using hc2, ?_⟩
      rw [hc2] at h
      exact h
    · have hc2f : native_teq c (Term.Boolean false) = false := by
        cases hv : native_teq c (Term.Boolean false)
        · rfl
        · exact absurd hv hc2
      rw [hc2f] at h
      simp at h

theorem eo_eq_boolean_true_elim {a b : Term}
    (h : __eo_eq a b = Term.Boolean true) : a = b := by
  fun_cases __eo_eq a b <;> simp_all [__eo_eq, native_teq]

/-! ### The reified guard relations -/

/--
Reified successful run of `__is_quant_dt_split_conj x c ys F g`.

Constructors mirror the arms of the (fixed) guard:
- `peel`: consume a retained binder present in both `ys` and the conjunct's
  binder list (no later shadowing).
- `absorb`: `ys` exhausted; absorb the conjunct's next binder as a constructor
  argument (no later shadowing, not free in `F`).
- `unwrap`: the single conjunct binder list is exhausted; finish at its body.
- `final`: the remaining conjunct is exactly the substituted body.
-/
inductive ConjRel (x F : Term) : Term -> Term -> Term -> Type where
  | peel {c y ys zs G : Term} :
      __eo_list_find Term.__eo_List_cons zs y = Term.Numeral (-1 : native_Int) ->
      ConjRel x F c ys (mkForall zs G) ->
      ConjRel x F c (eoCons y ys) (mkForall (eoCons y zs) G)
  | absorb {c y zs G : Term} :
      __eo_list_find Term.__eo_List_cons zs y = Term.Numeral (-1 : native_Int) ->
      __contains_atomic_term_list_free_rec F (eoCons y Term.__eo_List_nil)
        Term.__eo_List_nil = Term.Boolean false ->
      ConjRel x F (Term.Apply c y) Term.__eo_List_nil (mkForall zs G) ->
      ConjRel x F c Term.__eo_List_nil (mkForall (eoCons y zs) G)
  | unwrap {c G : Term} :
      __eo_typeof c = __eo_typeof x ->
      substOne x c F = G ->
      ConjRel x F c Term.__eo_List_nil (mkForall Term.__eo_List_nil G)
  | final {cx g : Term} :
      __eo_typeof cx = __eo_typeof x ->
      (∀ B : Term, g ≠ mkForall Term.__eo_List_nil B) ->
      substOne x cx F = g ->
      ConjRel x F cx Term.__eo_List_nil g

/-- Reified successful run of `__is_quant_dt_split x cs ys F G`. -/
inductive SplitRel (x ys F : Term) : Term -> Term -> Type where
  | single {c g : Term} :
      ConjRel x F c ys g ->
      SplitRel x ys F (eoCons c Term.__eo_List_nil) g
  | nil_true :
      SplitRel x ys F Term.__eo_List_nil (Term.Boolean true)
  | step {c cs g G : Term} :
      ConjRel x F c ys g ->
      SplitRel x ys F cs G ->
      SplitRel x ys F (eoCons c cs) (mkAnd g G)

/-- Concrete values used to instantiate the constructor-field quantifiers of
an accepted conjunct. Retained binders are handled separately by
`ForallInstantiationModel`. -/
def CtorInst (x F : Term) {c ys g : Term}
    (rel : ConjRel x F c ys g) (M : SmtModel) (v : SmtValue) : Prop :=
  (match rel with
  | ConjRel.peel _ tail => CtorInst x F tail M v
  | @ConjRel.absorb _ _ _ y _ _ _ _ tail =>
      ∃ (s : native_String) (T : Term) (u : SmtValue),
        y = Term.Var (Term.String s) T ∧
        __smtx_typeof_value u = __eo_to_smt_type T ∧
        __smtx_value_canonical u = true ∧
        CtorInst x F tail
          (native_model_push M s (__eo_to_smt_type T) u) v
  | @ConjRel.unwrap _ _ c _ _ _ =>
      __smtx_model_eval M (__eo_to_smt c) = v
  | @ConjRel.final _ _ cx _ _ _ _ =>
      __smtx_model_eval M (__eo_to_smt cx) = v : Prop)

/-- Left-associated EO application spine. -/
def eoTermSpine : Term -> List Term -> Term
  | c, [] => c
  | c, a :: args => eoTermSpine (Term.Apply c a) args

theorem eoTermSpine_size_lt_of_nonempty (c a : Term) :
    ∀ args : List Term, sizeOf c < sizeOf (eoTermSpine c (a :: args)) := by
  intro args
  induction args generalizing c a with
  | nil => simp [eoTermSpine]; omega
  | cons b args ih =>
      have h₁ : sizeOf c < sizeOf (Term.Apply c a) := by simp; omega
      have h₂ := ih (Term.Apply c a) b
      simpa [eoTermSpine] using Nat.lt_trans h₁ h₂

theorem eoTermSpine_eq_head_implies_nil {c : Term} {args : List Term}
    (h : eoTermSpine c args = c) : args = [] := by
  cases args with
  | nil => rfl
  | cons a args =>
      have hLt := eoTermSpine_size_lt_of_nonempty c a args
      rw [h] at hLt
      omega

inductive DtEoSpine : Term -> native_String -> DatatypeDecl -> Nat -> Prop where
  | root (s : native_String) (d : DatatypeDecl) (i : Nat) :
      DtEoSpine (Term.DtCons s d i) s d i
  | app {c : Term} {s : native_String} {d : DatatypeDecl} {i : Nat}
      (a : Term) : DtEoSpine c s d i -> DtEoSpine (Term.Apply c a) s d i

theorem dtEoSpine_apply_translation
    {c : Term} {s : native_String} {d : DatatypeDecl} {i : Nat}
    (hSpine : DtEoSpine c s d i) (a : Term) :
    __eo_to_smt (Term.Apply c a) =
      SmtTerm.Apply (__eo_to_smt c) (__eo_to_smt a) := by
  induction hSpine generalizing a with
  | root => rfl
  | app a' hSpine ih =>
      cases hSpine with
      | root => rfl
      | app a'' hSpine' =>
          cases hSpine' with
          | root => rfl
          | app a''' hSpine'' => cases hSpine'' <;> rfl

theorem dtEoSpine_spine_translation
    {c : Term} {s : native_String} {d : DatatypeDecl} {i : Nat}
    (hSpine : DtEoSpine c s d i) (args : List Term) :
    __eo_to_smt (eoTermSpine c args) =
      List.foldl (fun f a => SmtTerm.Apply f (__eo_to_smt a))
        (__eo_to_smt c) args := by
  induction args generalizing c with
  | nil => rfl
  | cons a args ih =>
      rw [show eoTermSpine c (a :: args) =
        eoTermSpine (Term.Apply c a) args from rfl]
      rw [ih (DtEoSpine.app a hSpine), dtEoSpine_apply_translation hSpine]
      rfl

theorem dtEoSpine_translation_head
    {c : Term} {s : native_String} {d : DatatypeDecl} {i : Nat}
    (hSpine : DtEoSpine c s d i)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false) :
    qdsSmtApplyHead (__eo_to_smt c) =
      SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i := by
  induction hSpine with
  | root => simp [qdsSmtApplyHead, hReserved, native_ite]
  | app a hSpine ih =>
      rw [dtEoSpine_apply_translation hSpine]
      simpa [qdsSmtApplyHead] using ih hReserved

/-- Constructor arguments absorbed while following one accepted conjunct. -/
def conjAbsorbed {x F c ys g : Term}
    (rel : ConjRel x F c ys g) : List Term :=
  match rel with
  | ConjRel.peel _ tail => conjAbsorbed tail
  | @ConjRel.absorb _ _ _ y _ _ _ _ tail => y :: conjAbsorbed tail
  | ConjRel.unwrap _ _ => []
  | ConjRel.final _ _ _ => []

/-- Fully applied constructor at the final node of a conjunct relation. -/
def conjFinal {x F c ys g : Term}
    (rel : ConjRel x F c ys g) : Term :=
  match rel with
  | ConjRel.peel _ tail => conjFinal tail
  | ConjRel.absorb _ _ tail => conjFinal tail
  | @ConjRel.unwrap _ _ c _ _ _ => c
  | @ConjRel.final _ _ cx _ _ _ _ => cx

/-- A Lean list occurring as an initial segment of an EO list. -/
inductive EoListPrefix : List Term → Term → Prop where
  | nil (zs : Term) : EoListPrefix [] zs
  | cons {ys : List Term} {zs y : Term} :
      EoListPrefix ys zs → EoListPrefix (y :: ys) (eoCons y zs)

private theorem conjAbsorbed_prefix_aux {x F c ys g : Term}
    (rel : ConjRel x F c ys g) :
    ∀ {zs G : Term}, ys = Term.__eo_List_nil -> g = mkForall zs G ->
      EoListPrefix (conjAbsorbed rel) zs := by
  induction rel with
  | peel hFind tail ih =>
      intro zs G hys hg
      simp [eoCons] at hys
  | @absorb c y zs G hFind hFree tail ih =>
      intro zs' G' hys hg
      cases hg
      exact EoListPrefix.cons (ih rfl rfl)
  | unwrap hTy hSubst =>
      intro zs G hys hg
      exact EoListPrefix.nil _
  | final hTy hNotForall hSubst =>
      intro zs G hys hg
      exact EoListPrefix.nil _

theorem conjAbsorbed_prefix_of_forall
    {x F c zs G : Term}
    (rel : ConjRel x F c Term.__eo_List_nil (mkForall zs G)) :
    EoListPrefix (conjAbsorbed rel) zs :=
  conjAbsorbed_prefix_aux rel rfl rfl

theorem EoListPrefix.not_mem_of_var_env_not_mem
    {ys : List Term} {zs : Term} {vars : List EoVarKey}
    (hPrefix : EoListPrefix ys zs) (hEnv : EoVarEnv zs vars)
    {s : native_String} {T : Term} (hNotMem : (s, T) ∉ vars) :
    Term.Var (Term.String s) T ∉ ys := by
  induction hPrefix generalizing vars with
  | nil => simp
  | @cons ys zs y hPrefix ih =>
      cases hEnv with
      | cons hTail =>
          simp only [List.mem_cons, not_or]
          constructor
          · intro hEq
            injection hEq with hName hTy
            injection hName with hs
            subst hs
            subst hTy
            exact hNotMem (List.Mem.head _)
          · exact ih hTail (fun hMem => hNotMem (List.Mem.tail _ hMem))

theorem EoListPrefix.var_shape_of_mem_env
    {ys : List Term} {zs : Term} {vars : List EoVarKey}
    (hPrefix : EoListPrefix ys zs) (hEnv : EoVarEnv zs vars)
    {y : Term} (hMem : y ∈ ys) :
    ∃ s T, y = Term.Var (Term.String s) T := by
  induction hPrefix generalizing vars with
  | nil => simp at hMem
  | @cons ys zs z hPrefix ih =>
      cases hEnv with
      | @cons s T env vars hTail =>
          cases hMem with
          | head => exact ⟨s, T, rfl⟩
          | tail _ hMem => exact ih hTail hMem

theorem conjFinal_eq_spine {x F c ys g : Term}
    (rel : ConjRel x F c ys g) :
    conjFinal rel = eoTermSpine c (conjAbsorbed rel) := by
  induction rel with
  | peel hFind tail ih => simpa [conjFinal, conjAbsorbed] using ih
  | absorb hFind hFree tail ih =>
      simpa [conjFinal, conjAbsorbed, eoTermSpine] using ih
  | unwrap hTy hSubst => simp [conjFinal, conjAbsorbed, eoTermSpine]
  | final hTy hNotForall hSubst => simp [conjFinal, conjAbsorbed, eoTermSpine]

theorem conjFinal_typeof {x F c ys g : Term}
    (rel : ConjRel x F c ys g) :
    __eo_typeof (conjFinal rel) = __eo_typeof x := by
  induction rel with
  | peel hFind tail ih => exact ih
  | absorb hFind hFree tail ih => exact ih
  | unwrap hTy hSubst => simpa [conjFinal] using hTy
  | final hTy hNotForall hSubst => simpa [conjFinal] using hTy

theorem ctorInst_of_no_absorbed
    {x F c ys g : Term} (rel : ConjRel x F c ys g) :
    ∀ (M : SmtModel) (v : SmtValue),
      conjAbsorbed rel = [] ->
      __smtx_model_eval M (__eo_to_smt (conjFinal rel)) = v ->
      CtorInst x F rel M v := by
  induction rel with
  | peel hFind tail ih =>
      intro M v hAbs hEval
      exact ih M v hAbs hEval
  | absorb hFind hFree tail ih =>
      intro M v hAbs hEval
      simp [conjAbsorbed] at hAbs
  | unwrap hTy hSubst =>
      intro M v hAbs hEval
      simpa [CtorInst, conjFinal] using hEval
  | final hTy hNotForall hSubst =>
      intro M v hAbs hEval
      simpa [CtorInst, conjFinal] using hEval

theorem ctorInst_of_one_absorbed
    {x F c ys g : Term} (rel : ConjRel x F c ys g) :
    ∀ (M : SmtModel) (v : SmtValue) (s : native_String) (T : Term)
      (u : SmtValue),
      conjAbsorbed rel = [Term.Var (Term.String s) T] ->
      __smtx_typeof_value u = __eo_to_smt_type T ->
      __smtx_value_canonical u = true ->
      __smtx_model_eval
          (native_model_push M s (__eo_to_smt_type T) u)
          (__eo_to_smt (conjFinal rel)) = v ->
      CtorInst x F rel M v := by
  induction rel with
  | peel hFind tail ih =>
      intro M v s T u hAbs huTy huCanon hEval
      exact ih M v s T u hAbs huTy huCanon hEval
  | @absorb c y zs G hFind hFree tail ih =>
      intro M v s T u hAbs huTy huCanon hEval
      have hHead : y = Term.Var (Term.String s) T := by
        simpa [conjAbsorbed] using congrArg List.head? hAbs
      have hTailAbs : conjAbsorbed tail = [] := by
        simpa [conjAbsorbed] using congrArg List.tail hAbs
      subst y
      refine ⟨s, T, u, rfl, huTy, huCanon, ?_⟩
      exact ctorInst_of_no_absorbed tail
        (native_model_push M s (__eo_to_smt_type T) u) v hTailAbs
        (by simpa [conjFinal] using hEval)
  | unwrap hTy hSubst =>
      intro M v s T u hAbs huTy huCanon hEval
      simp [conjAbsorbed] at hAbs
  | final hTy hNotForall hSubst =>
      intro M v s T u hAbs huTy huCanon hEval
      simp [conjAbsorbed] at hAbs

theorem ctorInst_of_two_absorbed
    {x F c ys g : Term} (rel : ConjRel x F c ys g) :
    ∀ (M : SmtModel) (v : SmtValue)
      (s₁ : native_String) (T₁ : Term) (u₁ : SmtValue)
      (s₂ : native_String) (T₂ : Term) (u₂ : SmtValue),
      conjAbsorbed rel =
        [Term.Var (Term.String s₁) T₁, Term.Var (Term.String s₂) T₂] ->
      __smtx_typeof_value u₁ = __eo_to_smt_type T₁ ->
      __smtx_value_canonical u₁ = true ->
      __smtx_typeof_value u₂ = __eo_to_smt_type T₂ ->
      __smtx_value_canonical u₂ = true ->
      __smtx_model_eval
          (native_model_push
            (native_model_push M s₁ (__eo_to_smt_type T₁) u₁)
            s₂ (__eo_to_smt_type T₂) u₂)
          (__eo_to_smt (conjFinal rel)) = v ->
      CtorInst x F rel M v := by
  induction rel with
  | peel hFind tail ih =>
      intro M v s₁ T₁ u₁ s₂ T₂ u₂ hAbs hU₁Ty hU₁Canon hU₂Ty hU₂Canon hEval
      exact ih M v s₁ T₁ u₁ s₂ T₂ u₂ hAbs hU₁Ty hU₁Canon hU₂Ty hU₂Canon hEval
  | @absorb c y zs G hFind hFree tail ih =>
      intro M v s₁ T₁ u₁ s₂ T₂ u₂ hAbs hU₁Ty hU₁Canon hU₂Ty hU₂Canon hEval
      have hHead : y = Term.Var (Term.String s₁) T₁ := by
        simpa [conjAbsorbed] using congrArg List.head? hAbs
      have hTailAbs : conjAbsorbed tail =
          [Term.Var (Term.String s₂) T₂] := by
        simpa [conjAbsorbed] using congrArg List.tail hAbs
      subst y
      refine ⟨s₁, T₁, u₁, rfl, hU₁Ty, hU₁Canon, ?_⟩
      exact ctorInst_of_one_absorbed tail
        (native_model_push M s₁ (__eo_to_smt_type T₁) u₁) v
        s₂ T₂ u₂ hTailAbs hU₂Ty hU₂Canon
        (by simpa [conjFinal] using hEval)
  | unwrap hTy hSubst =>
      intro M v s₁ T₁ u₁ s₂ T₂ u₂ hAbs hU₁Ty hU₁Canon hU₂Ty hU₂Canon hEval
      simp [conjAbsorbed] at hAbs
  | final hTy hNotForall hSubst =>
      intro M v s₁ T₁ u₁ s₂ T₂ u₂ hAbs hU₁Ty hU₁Canon hU₂Ty hU₂Canon hEval
      simp [conjAbsorbed] at hAbs

def eoTermArgs : Term -> List Term
  | Term.Apply f a => eoTermArgs f ++ [a]
  | _ => []

theorem eoTermArgs_eoTermSpine : ∀ (head : Term) (args : List Term),
    eoTermArgs (eoTermSpine head args) = eoTermArgs head ++ args := by
  intro head args
  induction args generalizing head with
  | nil => simp [eoTermSpine]
  | cons a args ih =>
      rw [show eoTermSpine head (a :: args) =
        eoTermSpine (Term.Apply head a) args from rfl, ih]
      simp [eoTermArgs, List.append_assoc]

theorem eo_to_smt_spine_dtcons
    (s : native_String) (d : DatatypeDecl) (i : Nat) (args : List Term)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false) :
    __eo_to_smt (eoTermSpine (Term.DtCons s d i) args) =
      List.foldl (fun f a => SmtTerm.Apply f (__eo_to_smt a))
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) args := by
  rw [dtEoSpine_spine_translation (DtEoSpine.root s d i)]
  simp [hReserved, native_ite]

/-! ### Extraction from a successful guard run -/

private theorem conjRel_extract_aux (x F : Term) :
    ∀ n : Nat, ∀ c ys g : Term, sizeOf g < n ->
      (__eo_l_1___is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
        Nonempty (ConjRel x F c ys g)) ∧
      (__is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
        Nonempty (ConjRel x F c ys g)) := by
  intro n
  induction n with
  | zero => intro c ys g hsz; omega
  | succ n ih =>
      intro c ys g hsz
      have hl1 : __eo_l_1___is_quant_dt_split_conj x c ys F g = Term.Boolean true ->
          Nonempty (ConjRel x F c ys g) := by
        intro h
        fun_cases __eo_l_1___is_quant_dt_split_conj x c ys F g
        case case1 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case2 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case3 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        case case4 => simp [__eo_l_1___is_quant_dt_split_conj] at h
        -- absorb arm
        case case5 =>
          rename_i y zs G _ _ _
          simp only [__eo_l_1___is_quant_dt_split_conj] at h
          obtain ⟨hFind, _, hRest⟩ := eo_requires_boolean_true_elim h
          obtain ⟨hFree, _, hRec⟩ := eo_requires_boolean_true_elim hRest
          have hSize : sizeOf (mkForall zs G) < n := by
            simp only [mkForall, eoCons] at hsz ⊢
            simp +arith at hsz ⊢
            omega
          obtain ⟨tail⟩ :=
            (ih (Term.Apply c y) Term.__eo_List_nil (mkForall zs G) hSize).2 hRec
          exact ⟨ConjRel.absorb hFind hFree tail⟩
        -- terminal empty-prefix arm
        case case6 =>
          rename_i G _ _ _
          simp only [__eo_l_1___is_quant_dt_split_conj] at h
          obtain ⟨hType, _, hEq⟩ := eo_requires_boolean_true_elim h
          exact ⟨ConjRel.unwrap hType (eo_eq_boolean_true_elim hEq)⟩
        -- final arm
        case case7 =>
          rename_i hxStuck hcStuck hFStuck hgStuck hCons hNil
          have hred : __eo_l_1___is_quant_dt_split_conj x c Term.__eo_List_nil F g =
              __eo_requires (__eo_typeof c) (__eo_typeof x)
                (__eo_eq (substOne x c F) g) := by
            simp_all [__eo_l_1___is_quant_dt_split_conj, substOne]
          rw [hred] at h
          obtain ⟨hType, _, hEq⟩ := eo_requires_boolean_true_elim h
          exact ⟨ConjRel.final hType (by
            intro B hForall
            exact hNil B hForall) (eo_eq_boolean_true_elim hEq)⟩
        case case8 =>
          simp [__eo_l_1___is_quant_dt_split_conj] at h
      refine ⟨hl1, ?_⟩
      intro h
      fun_cases __is_quant_dt_split_conj x c ys F g
      case case1 => simp [__is_quant_dt_split_conj] at h
      case case2 => simp [__is_quant_dt_split_conj] at h
      case case3 => simp [__is_quant_dt_split_conj] at h
      case case4 => simp [__is_quant_dt_split_conj] at h
      case case5 => simp [__is_quant_dt_split_conj] at h
      -- the peel/ite arm
      case case6 =>
        rename_i y ys' y2 zs G _ _ _
        simp only [__is_quant_dt_split_conj] at h
        rcases eo_ite_boolean_true_elim h with ⟨hEq, hThen⟩ | ⟨_, hElse⟩
        · have hy : y = y2 := eo_eq_boolean_true_elim hEq
          subst hy
          obtain ⟨hFind, _, hRec⟩ := eo_requires_boolean_true_elim hThen
          have hSize : sizeOf (mkForall zs G) < n := by
            simp only [mkForall, eoCons] at hsz ⊢
            simp +arith at hsz ⊢
            omega
          obtain ⟨tail⟩ := (ih c ys' (mkForall zs G) hSize).2 hRec
          exact ⟨ConjRel.peel hFind tail⟩
        · exact hl1 hElse
      -- the fallback arm
      case case7 =>
        have hred : __is_quant_dt_split_conj x c ys F g =
            __eo_l_1___is_quant_dt_split_conj x c ys F g := by
          simp_all [__is_quant_dt_split_conj]
        rw [hred] at h
        exact hl1 h

theorem conjRel_of_guard_true (x F c ys g : Term)
    (h : __is_quant_dt_split_conj x c ys F g = Term.Boolean true) :
    Nonempty (ConjRel x F c ys g) :=
  (conjRel_extract_aux x F (sizeOf g + 1) c ys g (by omega)).2 h

theorem splitRel_of_guard_true (x ys F : Term) :
    ∀ (cs G : Term),
      __is_quant_dt_split x cs ys F G = Term.Boolean true ->
      Nonempty (SplitRel x ys F cs G) := by
  intro cs G h
  fun_cases __is_quant_dt_split x cs ys F G
  case case1 => simp [__is_quant_dt_split] at h
  case case2 => simp [__is_quant_dt_split] at h
  case case3 => simp [__is_quant_dt_split] at h
  case case4 => simp [__is_quant_dt_split] at h
  -- and-chain arm
  case case5 =>
    rename_i c' cs' g' G' _ _ _
    simp only [__is_quant_dt_split] at h
    obtain ⟨hConj, _, hRec⟩ := eo_requires_boolean_true_elim h
    obtain ⟨hConjRel⟩ := conjRel_of_guard_true x F c' ys g' hConj
    obtain ⟨hRestRel⟩ := splitRel_of_guard_true x ys F cs' G' hRec
    exact ⟨SplitRel.step hConjRel hRestRel⟩
  -- nil/true arm
  case case6 =>
    exact ⟨SplitRel.nil_true⟩
  -- singleton arm
  case case7 =>
    rename_i c' cs' _ _ _ _ _
    have hred : __is_quant_dt_split x (eoCons c' cs') ys F G =
        __eo_requires cs' Term.__eo_List_nil
          (__is_quant_dt_split_conj x c' ys F G) := by
      simp_all [__is_quant_dt_split]
    rw [hred] at h
    obtain ⟨hNil, _, hConj⟩ := eo_requires_boolean_true_elim h
    subst hNil
    obtain ⟨hConjRel⟩ := conjRel_of_guard_true x F c' ys G hConj
    exact ⟨SplitRel.single hConjRel⟩
  case case8 =>
    simp [__is_quant_dt_split] at h

end QuantDtSplitRule

namespace QuantDtSplitRule

open InstantiateRule

set_option maxHeartbeats 4000000

/-! ## Model push manipulation -/

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
  · rw [if_pos h2, if_neg (by rw [h2]; exact fun hc => h hc.symm), if_pos h2]
  · rw [if_neg h2]
    by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_neg h2]

theorem native_model_push_shadow
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w =
      native_model_push M s T w := by
  simp only [native_model_push]
  congr 1
  funext k
  by_cases hk : k = ({ isVar := true, name := s, ty := T } : SmtModelKey)
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, if_neg hk]

/-- Two pushes at the same key collapse regardless of the first value. -/
theorem native_model_push_shadow_of_key_eq
    (M : SmtModel) (s1 : native_String) (T1 : SmtType) (v : SmtValue)
    (s2 : native_String) (T2 : SmtType) (w : SmtValue)
    (h : ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
      { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v) s2 T2 w =
      native_model_push M s2 T2 w := by
  have hs : s1 = s2 := by cases h; rfl
  have hT : T1 = T2 := by cases h; rfl
  subst hs; subst hT
  exact native_model_push_shadow M s1 T1 v w

/-! ## Single-binder step characterization of the forall encoding -/

theorem forall_encoding_step_iff
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T : SmtType) (tail : SmtTerm)
    (hWf : __smtx_type_wf T = true)
    (hTailTy : __smtx_typeof tail = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.exists s T tail)) =
        SmtValue.Boolean true ↔
      ∀ v : SmtValue, __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M s T v) (SmtTerm.not tail) =
          SmtValue.Boolean true := by
  classical
  constructor
  · intro h v hvT hvC
    rw [smtx_model_eval_not_unfold] at h
    have hExFalse : __smtx_model_eval M (SmtTerm.exists s T tail) =
        SmtValue.Boolean false :=
      (InstantiateRule.smtx_model_eval_not_true_iff _).1 h
    have hNoSat : ¬ (∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
          __smtx_value_canonical w = true ∧
            __smtx_model_eval (native_model_push M s T w) tail =
              SmtValue.Boolean true) := by
      intro hSat
      have : __smtx_model_eval M (SmtTerm.exists s T tail) =
          SmtValue.Boolean true := by
        show (if _ : (∃ w : SmtValue,
            __smtx_typeof_value w = T ∧
              __smtx_value_canonical w = true ∧
                __smtx_model_eval (native_model_push M s T w) tail =
                  SmtValue.Boolean true)
          then SmtValue.Boolean true else SmtValue.Boolean false) =
          SmtValue.Boolean true
        rw [dif_pos hSat]
      rw [hExFalse] at this
      exact absurd this (by decide)
    have hPushTotal : model_wf (native_model_push M s T v) :=
      model_total_typed_push hM s T v hWf hvT
        (by simpa [value_canonical] using hvC)
    obtain ⟨b, hb⟩ :=
      smt_model_eval_bool_is_boolean (native_model_push M s T v) hPushTotal
        tail hTailTy
    cases b
    · rw [smtx_model_eval_not_unfold, hb]
      rfl
    · exact absurd ⟨v, hvT, hvC, hb⟩ hNoSat
  · intro h
    have hNoSat : ¬ (∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
          __smtx_value_canonical w = true ∧
            __smtx_model_eval (native_model_push M s T w) tail =
              SmtValue.Boolean true) := by
      rintro ⟨w, hwT, hwC, hwE⟩
      have := h w hwT hwC
      rw [smtx_model_eval_not_unfold, hwE] at this
      exact absurd this (by decide)
    have hExFalse : __smtx_model_eval M (SmtTerm.exists s T tail) =
        SmtValue.Boolean false := by
      show (if _ : (∃ w : SmtValue,
          __smtx_typeof_value w = T ∧
            __smtx_value_canonical w = true ∧
              __smtx_model_eval (native_model_push M s T w) tail =
                SmtValue.Boolean true)
        then SmtValue.Boolean true else SmtValue.Boolean false) =
        SmtValue.Boolean false
      rw [dif_neg hNoSat]
    rw [smtx_model_eval_not_unfold, hExFalse]
    rfl

/-! ## Pushing the split variable last -/

/--
Commutes a push of the split variable past an instantiation chain: if the body
is true in every instantiation of `ys` over the base extended with `x ↦ v`,
then it is true when `x ↦ v` is pushed after the chain instead.
-/
theorem inst_push_last_bridge
    (sx : native_String) (Tx : SmtType) (v : SmtValue) (body : SmtTerm)
    (hvT : __smtx_typeof_value v = Tx)
    (hvC : __smtx_value_canonical v = true) :
    ∀ {M N : SmtModel} {ys : Term},
      ForallInstantiationModel M ys N ->
      (∀ K, ForallInstantiationModel (native_model_push M sx Tx v) ys K ->
        __smtx_model_eval K body = SmtValue.Boolean true) ->
      __smtx_model_eval (native_model_push N sx Tx v) body =
        SmtValue.Boolean true := by
  intro M N ys hInst
  induction hInst with
  | nil M =>
      intro h
      exact h (native_model_push M sx Tx v)
        (ForallInstantiationModel.nil _)
  | cons hWf hwT hwC hTail ih =>
      rename_i M N s T env w
      intro h
      refine ih ?_
      intro K hK
      by_cases hKey :
          ({ isVar := true, name := s, ty := __eo_to_smt_type T } : SmtModelKey) =
            { isVar := true, name := sx, ty := Tx }
      · have hTeq : __eo_to_smt_type T = Tx := by cases hKey; rfl
        have hBase :
            native_model_push (native_model_push M s (__eo_to_smt_type T) w)
                sx Tx v =
              native_model_push M sx Tx v :=
          native_model_push_shadow_of_key_eq M s (__eo_to_smt_type T) w sx Tx v
            hKey
        rw [hBase] at hK
        have hBase2 :
            native_model_push (native_model_push M sx Tx v)
                s (__eo_to_smt_type T) v =
              native_model_push M sx Tx v := by
          refine native_model_push_shadow_of_key_eq M sx Tx v
            s (__eo_to_smt_type T) v ?_ |>.trans ?_
          · exact hKey.symm
          · cases hKey; rfl
        refine h K (ForallInstantiationModel.cons hWf (by rw [hTeq]; exact hvT)
          hvC ?_)
        rw [hBase2]
        exact hK
      · have hSwap :
            native_model_push (native_model_push M s (__eo_to_smt_type T) w)
                sx Tx v =
              native_model_push (native_model_push M sx Tx v)
                s (__eo_to_smt_type T) w :=
          native_model_push_comm M s (__eo_to_smt_type T) w sx Tx v hKey
        rw [hSwap] at hK
        exact h K (ForallInstantiationModel.cons hWf hwT hwC hK)

/-! ## Insensitivity to constructor-argument binders -/

/--
Pushing a value at a variable that has no free occurrence in `F` does not
change the evaluation of `F`.
-/
theorem eval_push_not_free_eq
    (K : SmtModel) (sw : native_String) (Tw : Term) (u : SmtValue) (F : Term)
    (hTrans : eoHasSmtTranslation F)
    (hNoFree :
      __contains_atomic_term_list_free_rec F
        (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
        Term.__eo_List_nil = Term.Boolean false) :
    __smtx_model_eval (native_model_push K sw (__eo_to_smt_type Tw) u)
        (__eo_to_smt F) =
      __smtx_model_eval K (__eo_to_smt F) := by
  refine smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (exceptVars := [(sw, Tw)]) (boundVars := [])
    (EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil))
    (EoVarEnvPerm.of_exact EoVarEnv.nil)
    hTrans hNoFree ?_
  refine ⟨?_, ?_⟩
  · exact
      ⟨fun s' T' =>
        ((model_agrees_on_globals_push K sw (__eo_to_smt_type Tw) u).1 s' T').symm,
       fun fid T U =>
        ((model_agrees_on_globals_push K sw (__eo_to_smt_type Tw) u).2 fid T U).symm⟩
  · intro s' T' hKey
    rcases hKey with hBound | hNotExcept
    · cases hBound
    · have hne : (s', T') ≠ (sw, __eo_to_smt_type Tw) := by
        intro hc
        exact hNotExcept (by
          rw [show ([(sw, Tw)].map EoVarKey.toSmt) = [(sw, __eo_to_smt_type Tw)] from rfl]
          rw [hc]
          exact List.mem_singleton.2 rfl)
      simp only [native_model_var_lookup, native_model_push]
      rw [if_neg (by
        intro hc
        apply hne
        injection hc with h1 h2 h3
        exact Prod.ext h2 h3)]

private theorem contains_atomic_term_list_free_rec_apply_false_intro
    {f a : Term} {sw : native_String} {Tw : Term}
    (hNotList : ∀ q x xs,
      f ≠ Term.Apply q (eoCons x xs))
    (hF : __contains_atomic_term_list_free_rec f
      (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
      Term.__eo_List_nil = Term.Boolean false)
    (hA : __contains_atomic_term_list_free_rec a
      (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
      Term.__eo_List_nil = Term.Boolean false) :
    __contains_atomic_term_list_free_rec (Term.Apply f a)
      (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
      Term.__eo_List_nil = Term.Boolean false := by
  have hEq :
      __contains_atomic_term_list_free_rec (Term.Apply f a)
          (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
          Term.__eo_List_nil =
        __eo_ite (__contains_atomic_term_list_free_rec f
            (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
            Term.__eo_List_nil)
          (Term.Boolean true)
          (__contains_atomic_term_list_free_rec a
            (eoCons (Term.Var (Term.String sw) Tw) Term.__eo_List_nil)
            Term.__eo_List_nil) := by
    cases f <;> try rfl
    rename_i q listArg
    cases listArg <;> try rfl
    rename_i listHead xs
    cases listHead <;> try rfl
    rename_i cons x
    cases cons <;> try rfl
    exact False.elim (hNotList q x xs rfl)
  rw [hEq, hF]
  simpa [__eo_ite, native_ite, native_teq] using hA

/-! ## The LHS with the split variable pushed last -/

/--
From the truth of the left-hand universal (split variable bound first), derive
the body's truth with the split variable pushed after any instantiation of the
retained binders.
-/
theorem lhs_gives_push_last
    (M : SmtModel)
    (sx : native_String) (xT ys F : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hLHS : ∀ N, ForallInstantiationModel M
      (eoCons (Term.Var (Term.String sx) xT) ys) N ->
      __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true) :
    ∀ N, ForallInstantiationModel M ys N ->
    ∀ v : SmtValue,
      __smtx_typeof_value v = __eo_to_smt_type xT ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval
          (native_model_push N sx (__eo_to_smt_type xT) v) (__eo_to_smt F) =
        SmtValue.Boolean true := by
  intro N hInst v hvT hvC
  refine inst_push_last_bridge sx (__eo_to_smt_type xT) v (__eo_to_smt F)
    hvT hvC hInst ?_
  intro K hK
  exact hLHS K (ForallInstantiationModel.cons hWfX hvT hvC hK)

/-- Rebase an instantiation performed after `x` was pushed into one where the
retained binders are instantiated first and the effective value of `x` is
pushed last. -/
theorem inst_rebase_push_last
    (sx : native_String) (Tx : SmtType) :
    ∀ {M N : SmtModel} {ys : Term} {v : SmtValue},
      __smtx_typeof_value v = Tx ->
      __smtx_value_canonical v = true ->
      ForallInstantiationModel (native_model_push M sx Tx v) ys N ->
      ∃ (N₀ : SmtModel) (w : SmtValue),
        ForallInstantiationModel M ys N₀ ∧
        __smtx_typeof_value w = Tx ∧
        __smtx_value_canonical w = true ∧
        N = native_model_push N₀ sx Tx w := by
  intro M N ys v hvTy hvCanon hInst
  have aux : ∀ {K N : SmtModel} {ys : Term},
      ForallInstantiationModel K ys N ->
      ∀ (M : SmtModel) (v : SmtValue),
        __smtx_typeof_value v = Tx ->
        __smtx_value_canonical v = true ->
        K = native_model_push M sx Tx v ->
        ∃ (N₀ : SmtModel) (w : SmtValue),
          ForallInstantiationModel M ys N₀ ∧
          __smtx_typeof_value w = Tx ∧
          __smtx_value_canonical w = true ∧
          N = native_model_push N₀ sx Tx w := by
    intro K N ys hKN
    induction hKN with
    | nil K =>
        intro M v hvTy hvCanon hK
        exact ⟨M, v, ForallInstantiationModel.nil M, hvTy, hvCanon, hK⟩
    | cons hWf huTy huCanon hTail ih =>
      rename_i K N sy Ty env u
      intro M v hvTy hvCanon hK
      by_cases hKey :
          ({ isVar := true, name := sy, ty := __eo_to_smt_type Ty } :
            SmtModelKey) = { isVar := true, name := sx, ty := Tx }
      · have hTx : __eo_to_smt_type Ty = Tx := by cases hKey; rfl
        have hStart :
            native_model_push
                K sy (__eo_to_smt_type Ty) u =
              native_model_push
                (native_model_push M sy (__eo_to_smt_type Ty) u) sx Tx u := by
          rw [hK]
          rw [native_model_push_shadow_of_key_eq M sx Tx v sy
              (__eo_to_smt_type Ty) u hKey.symm]
          have hSingle : native_model_push M sy (__eo_to_smt_type Ty) u =
              native_model_push M sx Tx u := by
            cases hKey
            rfl
          exact hSingle.trans (native_model_push_shadow_of_key_eq M sy
            (__eo_to_smt_type Ty) u sx Tx u hKey).symm
        obtain ⟨N₀, w, hN₀, hwTy, hwCanon, hN⟩ :=
          ih (native_model_push M sy (__eo_to_smt_type Ty) u) u
            (by simpa [hTx] using huTy) huCanon hStart
        exact ⟨N₀, w,
          ForallInstantiationModel.cons hWf huTy huCanon hN₀,
          hwTy, hwCanon, hN⟩
      · have hStart :
            native_model_push K sy (__eo_to_smt_type Ty) u =
              native_model_push
                (native_model_push M sy (__eo_to_smt_type Ty) u) sx Tx v := by
          rw [hK]
          exact native_model_push_comm M sx Tx v sy
            (__eo_to_smt_type Ty) u (by exact fun h => hKey h.symm)
        obtain ⟨N₀, w, hN₀, hwTy, hwCanon, hN⟩ :=
          ih (native_model_push M sy (__eo_to_smt_type Ty) u) v
            hvTy hvCanon hStart
        exact ⟨N₀, w,
          ForallInstantiationModel.cons hWf huTy huCanon hN₀,
          hwTy, hwCanon, hN⟩
  exact aux hInst M v hvTy hvCanon rfl

/-! ## One-layer forall encoding -/

/--
One-layer encoding of a conjunct: a top-level `forall` is encoded through
`__eo_to_smt_exists` with its body translated normally; anything else is
translated directly.  For a `forall` with a `cons` binder list this definitionally
agrees with `__eo_to_smt`; for the virtual `forall` with a nil binder list
(produced mid-recursion by the guard) it is `not (not body)` where the direct
translation would be `SmtTerm.None`.
-/
def gEnc : Term -> SmtTerm
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) B =>
      SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt B)))
  | t => __eo_to_smt t

private theorem gEnc_forall (vs B : Term) :
    gEnc (mkForall vs B) =
      SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt B))) := rfl

theorem gEnc_eq_eo_to_smt_of_not_nil_forall {G : Term}
    (hNot : ∀ B : Term, G ≠ mkForall Term.__eo_List_nil B) :
    gEnc G = __eo_to_smt G := by
  cases G with
  | Apply f B =>
      cases f with
      | Apply q vs =>
          cases q with
          | UOp op =>
              cases op
              case «forall» =>
                cases vs with
                | __eo_List_nil => exact False.elim (hNot B rfl)
                | _ => rfl
              all_goals rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- Typing inversion for a Bool-typed `exists`. -/
theorem smtx_typeof_exists_bool_inv
    {s : native_String} {T : SmtType} {tail : SmtTerm}
    (h : __smtx_typeof (SmtTerm.exists s T tail) = SmtType.Bool) :
    __smtx_typeof tail = SmtType.Bool ∧ __smtx_type_wf T = true := by
  rw [show __smtx_typeof (SmtTerm.exists s T tail) =
    native_ite (native_Teq (__smtx_typeof tail) SmtType.Bool)
      (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None from by
      simp only [__smtx_typeof]] at h
  by_cases ht : native_Teq (__smtx_typeof tail) SmtType.Bool = true
  · refine ⟨by simpa [native_Teq] using ht, ?_⟩
    rw [ht] at h
    simp only [native_ite, if_true] at h
    rw [__smtx_typeof_guard_wf] at h
    by_cases hw : __smtx_type_wf T = true
    · exact hw
    · exfalso
      have hwf : __smtx_type_wf T = false := by
        cases hv : __smtx_type_wf T
        · rfl
        · exact absurd hv hw
      rw [hwf] at h
      simp [native_ite] at h
  · exfalso
    have htf : native_Teq (__smtx_typeof tail) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof tail) SmtType.Bool
      · rfl
      · exact absurd hv ht
    rw [htf] at h
    simp [native_ite] at h

/-- Typing inversion for a Bool-typed `not`. -/
theorem smtx_typeof_not_bool_inv
    {t : SmtTerm} (h : __smtx_typeof (SmtTerm.not t) = SmtType.Bool) :
    __smtx_typeof t = SmtType.Bool := by
  rw [show __smtx_typeof (SmtTerm.not t) =
    native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool
      SmtType.None from by simp only [__smtx_typeof]] at h
  by_cases ht : native_Teq (__smtx_typeof t) SmtType.Bool = true
  · simpa [native_Teq] using ht
  · exfalso
    have htf : native_Teq (__smtx_typeof t) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof t) SmtType.Bool
      · rfl
      · exact absurd hv ht
    rw [htf] at h
    simp [native_ite] at h

/-- Typing introduction for `not`. -/
theorem smtx_typeof_not_bool_intro
    {t : SmtTerm} (h : __smtx_typeof t = SmtType.Bool) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  rw [show __smtx_typeof (SmtTerm.not t) =
    native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool
      SmtType.None from by simp only [__smtx_typeof]]
  rw [h]
  rfl

/-! ## Forward direction: per-conjunct induction -/

/-- A Bool-typed exists-list translation forces its head binder to be a
    string-named variable. -/
theorem exl_cons_bool_var_shape {y zs : Term} {body : SmtTerm}
    (h : __smtx_typeof (__eo_to_smt_exists (eoCons y zs) body) = SmtType.Bool) :
    ∃ (sy : native_String) (Ty : Term), y = Term.Var (Term.String sy) Ty := by
  cases y with
  | Var n T =>
      cases n with
      | String sy => exact ⟨sy, T, rfl⟩
      | _ =>
          exfalso
          rw [show __eo_to_smt_exists (eoCons _ zs) body = SmtTerm.None from rfl,
            show __smtx_typeof SmtTerm.None = SmtType.None from rfl] at h
          cases h
  | _ =>
      exfalso
      rw [show __eo_to_smt_exists (eoCons _ zs) body = SmtTerm.None from rfl,
        show __smtx_typeof SmtTerm.None = SmtType.None from rfl] at h
      cases h

theorem eoVarEnv_of_exists_bool {zs : Term} {body : SmtTerm}
    (hTy : __smtx_typeof (__eo_to_smt_exists zs body) = SmtType.Bool) :
    ∃ vars, EoVarEnv zs vars := by
  revert hTy
  fun_cases __eo_to_smt_exists zs body
  case case1 =>
    intro hTy
    exact ⟨[], EoVarEnv.nil⟩
  case case2 =>
    intro hTy
    have hTailTy := (smtx_typeof_exists_bool_inv hTy).1
    obtain ⟨vars, hEnv⟩ := eoVarEnv_of_exists_bool hTailTy
    exact ⟨_ :: vars, EoVarEnv.cons hEnv⟩
  case case3 =>
    intro hTy
    simp [__smtx_typeof] at hTy
termination_by sizeOf zs
decreasing_by subst zs; simp_wf; omega

theorem conjAbsorbed_nodup_of_typed {x F c ys g : Term}
    (rel : ConjRel x F c ys g)
    (hTy : __smtx_typeof (gEnc g) = SmtType.Bool) :
    (conjAbsorbed rel).Nodup := by
  induction rel with
  | @peel c y ys zs G hFind tail ih =>
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWf⟩ := smtx_typeof_exists_bool_inv hNotTy
      apply ih
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @absorb c y zs G hFind hFree tail ih =>
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWf⟩ := smtx_typeof_exists_bool_inv hNotTy
      obtain ⟨vars, hEnv⟩ := eoVarEnv_of_exists_bool hTailTy
      have hFindNeg : __eo_is_neg
          (__eo_list_find Term.__eo_List_cons zs
            (Term.Var (Term.String sy) Ty)) = Term.Boolean true := by
        rw [hFind]
        rfl
      have hKeyNotMem : (sy, Ty) ∉ vars :=
        EoVarEnvPerm.not_mem_of_find_neg_true
          (EoVarEnvPerm.of_exact hEnv) hFindNeg
      have hHeadNotMem : Term.Var (Term.String sy) Ty ∉
          conjAbsorbed tail :=
        (conjAbsorbed_prefix_of_forall tail).not_mem_of_var_env_not_mem
          hEnv hKeyNotMem
      simp only [conjAbsorbed, List.nodup_cons]
      refine ⟨hHeadNotMem, ih ?_⟩
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | unwrap hCxTy hSubst => simp [conjAbsorbed]
  | final hCxTy hNotForall hSubst => simp [conjAbsorbed]

theorem conj_absorbed_two_ne_of_typed
    {x F c ys g y₁ y₂ : Term} (rel : ConjRel x F c ys g)
    (hTy : __smtx_typeof (gEnc g) = SmtType.Bool)
    (hAbs : conjAbsorbed rel = [y₁, y₂]) : y₁ ≠ y₂ := by
  have hNodup := conjAbsorbed_nodup_of_typed rel hTy
  rw [hAbs] at hNodup
  simpa using hNodup

theorem tuple_absorbed_two_ne_of_typed
    {x F ys g : Term}
    (rel : ConjRel x F (Term.UOp UserOp.tuple) ys g)
    (hTy : __smtx_typeof (gEnc g) = SmtType.Bool)
    (s₁ s₂ : native_String) (T₁ T₂ : Term)
    (hAbs : conjAbsorbed rel =
      [Term.Var (Term.String s₁) T₁, Term.Var (Term.String s₂) T₂]) :
    Term.Var (Term.String s₁) T₁ ≠
      Term.Var (Term.String s₂) T₂ := by
  exact conj_absorbed_two_ne_of_typed rel hTy hAbs

/-- `gEnc` agrees with the direct translation on Bool-translatable terms. -/
theorem gEnc_eq_eo_to_smt_of_bool {G : Term}
    (hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool) :
    gEnc G = __eo_to_smt G := by
  cases G with
  | Apply f B =>
      cases f with
      | Apply q vs =>
          cases q with
          | UOp op =>
              cases op
              case «forall» =>
                cases vs with
                | __eo_List_nil =>
                    exfalso
                    rw [show __eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.forall)
                        Term.__eo_List_nil) B) = SmtTerm.None from rfl,
                      show __smtx_typeof SmtTerm.None = SmtType.None from rfl]
                      at hGTy
                    cases hGTy
                | _ => rfl
              all_goals rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

private theorem conj_final_forward_core
    (sx : native_String) (xT F c G : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F)
    (hCxType : __eo_typeof c = __eo_typeof (Term.Var (Term.String sx) xT))
    (hSubst : substOne (Term.Var (Term.String sx) xT) c F = G)
    (hSpine : CS c) (M₀ : SmtModel) (hM₀ : model_wf M₀)
    (hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool)
    (hH : ∀ N, ForallInstantiationModel M₀ Term.__eo_List_nil N →
      ∀ v : SmtValue,
        __smtx_typeof_value v = __eo_to_smt_type xT →
        __smtx_value_canonical v = true →
        __smtx_model_eval
            (native_model_push N sx (__eo_to_smt_type xT) v)
            (__eo_to_smt F) = SmtValue.Boolean true) :
    __smtx_model_eval M₀ (__eo_to_smt G) = SmtValue.Boolean true := by
  have hCxTrans : RuleProofs.eo_has_smt_translation c :=
    ctor_spine_translation hSpine hCxType hWfX
  have hCxTy : __smtx_typeof (__eo_to_smt c) = __eo_to_smt_type xT := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation c hCxTrans,
      hCxType]
    rfl
  obtain ⟨hEvalCxTy, hEvalCxCanon⟩ :=
    InstantiateRule.eo_to_smt_eval_typed_canonical M₀ hM₀ c hCxTrans
  have hActuals : SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes
      (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
      (eoCons c Term.__eo_List_nil) :=
    SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes.cons
      hWfX hCxTrans hCxTy
      (SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes.nil
        Term.__eo_List_nil)
  have hTs : EoListAllHaveSmtTranslation (eoCons c Term.__eo_List_nil) := by
    simpa [eoCons, EoListAllHaveSmtTranslation] using
      And.intro hCxTrans True.intro
  have hSubstTrans : RuleProofs.eo_has_smt_translation
      (substOne (Term.Var (Term.String sx) xT) c F) := by
    intro hNone
    rw [hSubst, hGTy] at hNone
    cases hNone
  have hEval := InstantiateRule.substitute_simul_eval M₀ hM₀ F
    (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
    (eoCons c Term.__eo_List_nil) hFTrans hTs hActuals hSubstTrans
  have hBody := hH M₀ (ForallInstantiationModel.nil M₀)
    (__smtx_model_eval M₀ (__eo_to_smt c))
    (by simpa [hCxTy] using hEvalCxTy)
    (by simpa [value_canonical] using hEvalCxCanon)
  calc
    __smtx_model_eval M₀ (__eo_to_smt G) =
        __smtx_model_eval M₀
          (__eo_to_smt (substOne (Term.Var (Term.String sx) xT) c F)) := by
            rw [hSubst]
    _ = __smtx_model_eval
          (InstantiateRule.pushSubstModel M₀
            (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
            (eoCons c Term.__eo_List_nil)) (__eo_to_smt F) := hEval
    _ = SmtValue.Boolean true := by
          simpa [eoCons, InstantiateRule.pushSubstModel] using hBody

/--
Core forward induction: a conjunct accepted by the guard is true whenever the
body `F` is true with the split variable pushed after any instantiation of the
remaining retained binders.

The `final` substitution node uses the substitution/evaluation bridge; the
binder walk (`peel`, `absorb`, `unwrap`) threads the corresponding model
instantiations.
-/
theorem conj_forward_aux
    (sx : native_String) (xT F : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F) :
    ∀ {c ysRem g : Term},
      ConjRel (Term.Var (Term.String sx) xT) F c ysRem g ->
      CS c ->
      ∀ M₀ : SmtModel, model_wf M₀ ->
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      (∀ N, ForallInstantiationModel M₀ ysRem N ->
        ∀ v : SmtValue,
          __smtx_typeof_value v = __eo_to_smt_type xT ->
          __smtx_value_canonical v = true ->
          __smtx_model_eval
              (native_model_push N sx (__eo_to_smt_type xT) v)
              (__eo_to_smt F) = SmtValue.Boolean true) ->
      __smtx_model_eval M₀ (gEnc g) = SmtValue.Boolean true := by
  intro c ysRem g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine M₀ hM₀ hTy hH
      rw [gEnc_forall] at hTy ⊢
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool :=
        smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists (eoCons (Term.Var (Term.String sy) Ty) zs)
          (SmtTerm.not (__eo_to_smt G)) =
        SmtTerm.exists sy (__eo_to_smt_type Ty)
          (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy ⊢
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      rw [forall_encoding_step_iff M₀ hM₀ sy (__eo_to_smt_type Ty) _ hWfY hTailTy]
      intro v hvT hvC
      have hStep := ih hSpine (native_model_push M₀ sy (__eo_to_smt_type Ty) v)
        (model_total_typed_push hM₀ sy (__eo_to_smt_type Ty) v hWfY hvT
          (by simpa [value_canonical] using hvC))
        (by rw [gEnc_forall]; exact smtx_typeof_not_bool_intro hTailTy)
        (by
          intro N hInst u huT huC
          exact hH N (ForallInstantiationModel.cons hWfY hvT hvC hInst) u huT huC)
      rw [gEnc_forall] at hStep
      exact hStep
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine M₀ hM₀ hTy hH
      rw [gEnc_forall] at hTy ⊢
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool :=
        smtx_typeof_not_bool_inv hTy
      obtain ⟨sw, Tw, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists (eoCons (Term.Var (Term.String sw) Tw) zs)
          (SmtTerm.not (__eo_to_smt G)) =
        SmtTerm.exists sw (__eo_to_smt_type Tw)
          (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy ⊢
      obtain ⟨hTailTy, hWfW⟩ := smtx_typeof_exists_bool_inv hNotTy
      rw [forall_encoding_step_iff M₀ hM₀ sw (__eo_to_smt_type Tw) _ hWfW hTailTy]
      intro u huT huC
      have hStep := ih (CS.apply hSpine hWfW)
        (native_model_push M₀ sw (__eo_to_smt_type Tw) u)
        (model_total_typed_push hM₀ sw (__eo_to_smt_type Tw) u hWfW huT
          (by simpa [value_canonical] using huC))
        (by rw [gEnc_forall]; exact smtx_typeof_not_bool_intro hTailTy)
        (by
          intro N hInst v hvT hvC
          cases hInst with
          | nil =>
              by_cases hKey :
                  ({ isVar := true, name := sw, ty := __eo_to_smt_type Tw } :
                    SmtModelKey) =
                  { isVar := true, name := sx, ty := __eo_to_smt_type xT }
              · rw [native_model_push_shadow_of_key_eq M₀ sw (__eo_to_smt_type Tw)
                  u sx (__eo_to_smt_type xT) v hKey]
                exact hH M₀ (ForallInstantiationModel.nil M₀) v hvT hvC
              · rw [native_model_push_comm M₀ sw (__eo_to_smt_type Tw) u
                  sx (__eo_to_smt_type xT) v hKey]
                rw [eval_push_not_free_eq _ sw Tw u F hFTrans hFree]
                exact hH M₀ (ForallInstantiationModel.nil M₀) v hvT hvC)
      rw [gEnc_forall] at hStep
      exact hStep
  | @unwrap c G hCxType hSubst =>
      intro hSpine M₀ hM₀ hTy hH
      rw [gEnc_forall] at hTy ⊢
      rw [show __eo_to_smt_exists Term.__eo_List_nil (SmtTerm.not (__eo_to_smt G)) =
        SmtTerm.not (__eo_to_smt G) from rfl] at hTy ⊢
      have hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool :=
        smtx_typeof_not_bool_inv (smtx_typeof_not_bool_inv hTy)
      have hInner := conj_final_forward_core sx xT F c G hWfX hFTrans
        hCxType hSubst hSpine M₀ hM₀ hGTy hH
      rw [smtx_model_eval_not_unfold, smtx_model_eval_not_unfold, hInner]
      rfl
  | @final cx g hCxType hNotNilForall hSubst =>
      intro hSpine M₀ hM₀ hTy hH
      have hEnc : gEnc g = __eo_to_smt g :=
        gEnc_eq_eo_to_smt_of_not_nil_forall hNotNilForall
      rw [hEnc] at hTy ⊢
      exact conj_final_forward_core sx xT F cx g hWfX hFTrans hCxType
        hSubst hSpine M₀ hM₀ hTy hH

private theorem conj_final_backward_core
    (sx : native_String) (xT F c G : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F)
    (hCxType : __eo_typeof c = __eo_typeof (Term.Var (Term.String sx) xT))
    (hSubst : substOne (Term.Var (Term.String sx) xT) c F = G)
    (hSpine : CS c) (M : SmtModel) (hM : model_wf M)
    (hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool)
    (hGTrue : __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true)
    (v : SmtValue) (hCI : __smtx_model_eval M (__eo_to_smt c) = v) :
    __smtx_model_eval
        (native_model_push M sx (__eo_to_smt_type xT) v)
        (__eo_to_smt F) = SmtValue.Boolean true := by
  have hCxTrans : RuleProofs.eo_has_smt_translation c :=
    ctor_spine_translation hSpine hCxType hWfX
  have hCxTy : __smtx_typeof (__eo_to_smt c) = __eo_to_smt_type xT := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation c hCxTrans,
      hCxType]
    rfl
  have hActuals :
      SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes
        (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
        (eoCons c Term.__eo_List_nil) :=
    SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes.cons
      hWfX hCxTrans hCxTy
      (SubstituteTranslatabilitySupport.SubstActualsHaveSmtTypes.nil
        Term.__eo_List_nil)
  have hTs : EoListAllHaveSmtTranslation (eoCons c Term.__eo_List_nil) := by
    simpa [eoCons, EoListAllHaveSmtTranslation] using
      And.intro hCxTrans True.intro
  have hSubstTrans : RuleProofs.eo_has_smt_translation
      (substOne (Term.Var (Term.String sx) xT) c F) := by
    intro hNone
    rw [hSubst, hGTy] at hNone
    cases hNone
  have hEval := InstantiateRule.substitute_simul_eval M hM F
    (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
    (eoCons c Term.__eo_List_nil) hFTrans hTs hActuals hSubstTrans
  have hBody : __smtx_model_eval
      (InstantiateRule.pushSubstModel M
        (eoCons (Term.Var (Term.String sx) xT) Term.__eo_List_nil)
      (eoCons c Term.__eo_List_nil)) (__eo_to_smt F) =
      SmtValue.Boolean true := by
    rw [← hEval]
    change __smtx_model_eval M
      (__eo_to_smt (substOne (Term.Var (Term.String sx) xT) c F)) =
      SmtValue.Boolean true
    rw [hSubst]
    exact hGTrue
  simpa [eoCons, InstantiateRule.pushSubstModel, hCI] using hBody

/-- Reverse semantic induction for one accepted conjunct. -/
theorem conj_backward_aux
    (sx : native_String) (xT F : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F) :
    ∀ {c ysRem g : Term}
      (rel : ConjRel (Term.Var (Term.String sx) xT) F c ysRem g),
      CS c ->
      ∀ M : SmtModel, model_wf M ->
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      __smtx_model_eval M (gEnc g) = SmtValue.Boolean true ->
      ∀ N, ForallInstantiationModel M ysRem N ->
      ∀ v, CtorInst (Term.Var (Term.String sx) xT) F rel N v ->
      __smtx_model_eval
          (native_model_push N sx (__eo_to_smt_type xT) v)
          (__eo_to_smt F) = SmtValue.Boolean true := by
  intro c ysRem g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine M hM hTy hTrue N hInst v hCI
      change CtorInst (Term.Var (Term.String sx) xT) F hTail N v at hCI
      rw [gEnc_forall] at hTy hTrue
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
            (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy hTrue
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      cases hInst with
      | cons hWfY' huTy huCanon hInstTail =>
          have hTailTrue :=
            (forall_encoding_step_iff M hM sy (__eo_to_smt_type Ty)
              (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G)))
              hWfY hTailTy).1 hTrue _ huTy huCanon
          refine ih hSpine
            (native_model_push M sy (__eo_to_smt_type Ty) _)
            (model_total_typed_push hM sy (__eo_to_smt_type Ty) _ hWfY
              huTy (by simpa [value_canonical] using huCanon))
            ?_ ?_ N hInstTail v hCI
          · rw [gEnc_forall]
            exact smtx_typeof_not_bool_intro hTailTy
          · rw [gEnc_forall]
            exact hTailTrue
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine M hM hTy hTrue N hInst v hCI
      cases hInst
      rw [gEnc_forall] at hTy hTrue
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sw, Tw, rfl⟩ := exl_cons_bool_var_shape hNotTy
      obtain ⟨sw', Tw', u, hVar, huTy, huCanon, hCITail⟩ := hCI
      cases hVar
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sw) Tw) zs)
            (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sw (__eo_to_smt_type Tw)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy hTrue
      obtain ⟨hTailTy, hWfW⟩ := smtx_typeof_exists_bool_inv hNotTy
      have hTailTrue :=
        (forall_encoding_step_iff M hM sw (__eo_to_smt_type Tw)
          (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G)))
          hWfW hTailTy).1 hTrue u huTy huCanon
      have hStep := ih (CS.apply hSpine hWfW)
        (native_model_push M sw (__eo_to_smt_type Tw) u)
        (model_total_typed_push hM sw (__eo_to_smt_type Tw) u hWfW huTy
          (by simpa [value_canonical] using huCanon))
        (by rw [gEnc_forall]; exact smtx_typeof_not_bool_intro hTailTy)
        (by rw [gEnc_forall]; exact hTailTrue)
        (native_model_push M sw (__eo_to_smt_type Tw) u)
        (ForallInstantiationModel.nil _) v hCITail
      by_cases hKey :
          ({ isVar := true, name := sw, ty := __eo_to_smt_type Tw } :
            SmtModelKey) =
          { isVar := true, name := sx, ty := __eo_to_smt_type xT }
      · rw [native_model_push_shadow_of_key_eq M sw (__eo_to_smt_type Tw)
            u sx (__eo_to_smt_type xT) v hKey] at hStep
        exact hStep
      · rw [native_model_push_comm M sw (__eo_to_smt_type Tw) u
            sx (__eo_to_smt_type xT) v hKey] at hStep
        rw [eval_push_not_free_eq
          (native_model_push M sx (__eo_to_smt_type xT) v) sw Tw u F
          hFTrans hFree] at hStep
        exact hStep
  | @unwrap c G hCxType hSubst =>
      intro hSpine M hM hTy hTrue N hInst v hCI
      cases hInst
      change __smtx_model_eval M (__eo_to_smt c) = v at hCI
      rw [gEnc_forall] at hTy hTrue
      rw [show __eo_to_smt_exists Term.__eo_List_nil
          (SmtTerm.not (__eo_to_smt G)) = SmtTerm.not (__eo_to_smt G)
        from rfl] at hTy hTrue
      have hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool :=
        smtx_typeof_not_bool_inv (smtx_typeof_not_bool_inv hTy)
      have hEnc : gEnc G = __eo_to_smt G := gEnc_eq_eo_to_smt_of_bool hGTy
      obtain ⟨b, hb⟩ := smt_model_eval_bool_is_boolean M hM _ hGTy
      have hGTrue : __smtx_model_eval M (__eo_to_smt G) =
          SmtValue.Boolean true := by
        cases b
        · rw [smtx_model_eval_not_unfold, smtx_model_eval_not_unfold, hb]
            at hTrue
          exact absurd hTrue (by decide)
        · exact hb
      exact conj_final_backward_core sx xT F c G hWfX hFTrans hCxType
        hSubst hSpine M hM hGTy hGTrue v hCI
  | @final cx g hCxType hNotNilForall hSubst =>
      intro hSpine M hM hTy hTrue N hInst v hCI
      cases hInst
      change __smtx_model_eval M (__eo_to_smt cx) = v at hCI
      have hEnc : gEnc g = __eo_to_smt g :=
        gEnc_eq_eo_to_smt_of_not_nil_forall hNotNilForall
      rw [hEnc] at hTy hTrue
      exact conj_final_backward_core sx xT F cx g hWfX hFTrans hCxType
        hSubst hSpine M hM hTy hTrue v hCI

/-! ## Reconstructing a selected constructor branch -/

theorem datatype_name_not_reserved_of_type_wf
    (s : native_String) (d : DatatypeDecl)
    (hWf : __smtx_type_wf
      (__eo_to_smt_type (Term.DatatypeType s d)) = true) :
    __eo_to_smt_reserved_datatype_name s = false := by
  cases hRes : __eo_to_smt_reserved_datatype_name s
  · rfl
  · simp [__eo_to_smt_type, hRes, native_ite, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

theorem smt_model_eval_apply_of_dt_head
    (M : SmtModel) (f u : SmtValue)
    {s : native_String} {d : SmtDatatypeDecl} {i : Nat}
    (hHead : __smtx_apply_head_value f = SmtValue.DtCons s d i)
    (hu : u ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M f u = SmtValue.Apply f u := by
  cases f <;> simp_all [__smtx_apply_head_value, __smtx_model_eval_apply]

theorem conj_final_smt_type
    (sx : native_String) (xT F : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true) :
    ∀ {c ys g : Term}
      (rel : ConjRel (Term.Var (Term.String sx) xT) F c ys g),
      CS c ->
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      __smtx_typeof (__eo_to_smt (conjFinal rel)) =
        __eo_to_smt_type xT := by
  intro c ys g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih hSpine ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih (CS.apply hSpine hWfY) ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @unwrap c G hCxType hSubst =>
      intro hSpine hTy
      have hTrans : RuleProofs.eo_has_smt_translation c :=
        ctor_spine_translation hSpine hCxType hWfX
      change __smtx_typeof (__eo_to_smt c) = __eo_to_smt_type xT
      rw [TranslationProofs.eo_to_smt_typeof_matches_translation c hTrans,
        hCxType]
      rfl
  | @final cx g hCxType hNotForall hSubst =>
      intro hSpine hTy
      have hTrans : RuleProofs.eo_has_smt_translation cx :=
        ctor_spine_translation hSpine hCxType hWfX
      change __smtx_typeof (__eo_to_smt cx) = __eo_to_smt_type xT
      rw [TranslationProofs.eo_to_smt_typeof_matches_translation cx hTrans,
        hCxType]
      rfl

theorem conj_final_ucs
    (sx : native_String) (xT F : Term) :
    ∀ {c ys g : Term}
      (rel : ConjRel (Term.Var (Term.String sx) xT) F c ys g),
      UCS c ->
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      UCS (conjFinal rel) := by
  intro c ys g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih hSpine ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih (UCS.apply hSpine hWfY) ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @unwrap c G hCxType hSubst =>
      intro hSpine hTy
      simpa [conjFinal] using hSpine
  | final hCxType hNotForall hSubst =>
      intro hSpine hTy
      exact hSpine

theorem conj_final_tcs
    (sx : native_String) (xT F : Term) :
    ∀ {c ys g : Term}
      (rel : ConjRel (Term.Var (Term.String sx) xT) F c ys g),
      TCS c ->
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      TCS (conjFinal rel) := by
  intro c ys g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih hSpine ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine hTy
      rw [gEnc_forall] at hTy
      have hNotTy := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      refine ih (TCS.apply hSpine hWfY) ?_
      rw [gEnc_forall]
      exact smtx_typeof_not_bool_intro hTailTy
  | @unwrap c G hCxType hSubst =>
      intro hSpine hTy
      simpa [conjFinal] using hSpine
  | final hCxType hNotForall hSubst =>
      intro hSpine hTy
      exact hSpine

/-- Given values matching the statically typed absorbed fields, instantiate a
selected conjunct so that its final constructor evaluates to the requested
constructor value. -/
private theorem conj_ctor_inst_from_values_aux
    (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false) :
    ∀ {x F c ys g : Term}
      (rel : ConjRel x F c ys g),
      DtEoSpine c s d i ->
      (∀ z, z ∈ conjAbsorbed rel ->
        __contains_atomic_term_list_free_rec c
          (eoCons z Term.__eo_List_nil) Term.__eo_List_nil =
            Term.Boolean false) ->
      (∀ q z zs, c ≠ Term.Apply q (eoCons z zs)) ->
      ∀ (M : SmtModel) (v : SmtValue) (args : List SmtValue),
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      __smtx_typeof (__eo_to_smt (conjFinal rel)) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d) ->
      args.length = (conjAbsorbed rel).length ->
      (∀ j, j < args.length ->
        __smtx_typeof_value args[j]! =
          __smtx_typeof (__eo_to_smt (conjAbsorbed rel)[j]!)) ->
      (∀ u ∈ args, __smtx_value_canonical u = true) ->
      __smtx_apply_head_value (__smtx_model_eval M (__eo_to_smt c)) =
        SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i ->
      v = vsmMkSpine (__smtx_model_eval M (__eo_to_smt c)) args ->
      CtorInst x F rel M v := by
  intro x F c ys g rel
  induction rel with
  | @peel c y ys zs G hFind hTail ih =>
      intro hSpine hFresh hNotList M v args hTy hFinalTy hLen hArgTy hCanon
        hEvalHead hTarget
      rw [gEnc_forall] at hTy
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      change CtorInst x F hTail M v
      refine ih hSpine ?_ hNotList M v args ?_ ?_ ?_ ?_ ?_ hEvalHead hTarget
      · intro z hz
        exact hFresh z (by simpa [conjAbsorbed] using hz)
      · rw [gEnc_forall]
        exact smtx_typeof_not_bool_intro hTailTy
      · simpa [conjFinal] using hFinalTy
      · simpa [conjAbsorbed] using hLen
      · simpa [conjAbsorbed] using hArgTy
      · simpa [conjAbsorbed] using hCanon
  | @absorb c y zs G hFind hFree hTail ih =>
      intro hSpine hFresh hNotList M v args hTy hFinalTy hLen hArgTy hCanon
        hEvalHead hTarget
      have hRelTy := hTy
      rw [gEnc_forall] at hTy
      have hNotTy : __smtx_typeof
          (__eo_to_smt_exists (eoCons y zs) (SmtTerm.not (__eo_to_smt G))) =
          SmtType.Bool := smtx_typeof_not_bool_inv hTy
      obtain ⟨sy, Ty, rfl⟩ := exl_cons_bool_var_shape hNotTy
      rw [show __eo_to_smt_exists
            (eoCons (Term.Var (Term.String sy) Ty) zs)
              (SmtTerm.not (__eo_to_smt G)) =
          SmtTerm.exists sy (__eo_to_smt_type Ty)
            (__eo_to_smt_exists zs (SmtTerm.not (__eo_to_smt G))) from rfl]
        at hNotTy
      obtain ⟨hTailTy, hWfY⟩ := smtx_typeof_exists_bool_inv hNotTy
      obtain ⟨tailVars, hTailEnv⟩ := eoVarEnv_of_exists_bool hTailTy
      cases args with
      | nil => simp [conjAbsorbed] at hLen
      | cons u us =>
        have huTyRaw := hArgTy 0 (by simp)
        have hVarTy : __smtx_typeof
            (__eo_to_smt (Term.Var (Term.String sy) Ty)) =
            __eo_to_smt_type Ty := by
          change __smtx_typeof_guard_wf (__eo_to_smt_type Ty)
            (__eo_to_smt_type Ty) = __eo_to_smt_type Ty
          simp [__smtx_typeof_guard_wf, hWfY, native_ite]
        have huTy : __smtx_typeof_value u = __eo_to_smt_type Ty := by
          change __smtx_typeof_value u = __smtx_typeof
            (__eo_to_smt (Term.Var (Term.String sy) Ty)) at huTyRaw
          rw [hVarTy] at huTyRaw
          exact huTyRaw
        have huCanon : __smtx_value_canonical u = true :=
          hCanon u (by simp)
        have huNN : u ≠ SmtValue.NotValue := by
          intro hu
          subst u
          have hBad := hWfY
          rw [← huTy] at hBad
          simp [__smtx_typeof_value, __smtx_type_wf,
            __smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hBad
        have hNotSel : ∀ s₀ d₀ i₀ j₀,
            __eo_to_smt c ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
          intro s₀ d₀ i₀ j₀ hc
          have hh := dtEoSpine_translation_head hSpine hReserved
          rw [hc] at hh
          simp [qdsSmtApplyHead] at hh
        have hNotTester : ∀ s₀ d₀ i₀,
            __eo_to_smt c ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
          intro s₀ d₀ i₀ hc
          have hh := dtEoSpine_translation_head hSpine hReserved
          rw [hc] at hh
          simp [qdsSmtApplyHead] at hh
        have hCTrans : RuleProofs.eo_has_smt_translation c := by
          have hFullNN : __smtx_typeof (__eo_to_smt (conjFinal hTail)) ≠
              SmtType.None := by
            rw [show conjFinal hTail = conjFinal
              (ConjRel.absorb hFind hFree hTail) from rfl]
            rw [hFinalTy]
            simp
          rw [conjFinal_eq_spine hTail,
            dtEoSpine_spine_translation (DtEoSpine.app
              (Term.Var (Term.String sy) Ty) hSpine)] at hFullNN
          have hPrefixNN := qds_foldl_prefix_non_none
            (conjAbsorbed hTail)
            (dtEoSpine_translation_head
              (DtEoSpine.app (Term.Var (Term.String sy) Ty) hSpine) hReserved)
            hFullNN
          have hApplyTo := dtEoSpine_apply_translation hSpine
            (Term.Var (Term.String sy) Ty)
          rw [hApplyTo] at hPrefixNN
          have hGeneric : generic_apply_type (__eo_to_smt c)
              (__eo_to_smt (Term.Var (Term.String sy) Ty)) :=
            generic_apply_type_of_non_datatype_head hNotSel hNotTester
          have hApplyTypeNN : __smtx_typeof_apply
              (__smtx_typeof (__eo_to_smt c))
              (__smtx_typeof
                (__eo_to_smt (Term.Var (Term.String sy) Ty))) ≠
              SmtType.None := by
            rw [← hGeneric]
            exact hPrefixNN
          rcases typeof_apply_non_none_cases hApplyTypeNN with
            ⟨A, B, hFun, hArg, hA, hB⟩
          unfold RuleProofs.eo_has_smt_translation
          rcases hFun with hFun | hFun <;> rw [hFun] <;> simp
        have hCtorFree :
            __contains_atomic_term_list_free_rec c
              (eoCons (Term.Var (Term.String sy) Ty) Term.__eo_List_nil)
              Term.__eo_List_nil = Term.Boolean false :=
          hFresh _ (by simp [conjAbsorbed])
        have hEvalC : __smtx_model_eval
            (native_model_push M sy (__eo_to_smt_type Ty) u)
              (__eo_to_smt c) =
            __smtx_model_eval M (__eo_to_smt c) :=
          eval_push_not_free_eq M sy Ty u c hCTrans hCtorFree
        have hEvalY : __smtx_model_eval
            (native_model_push M sy (__eo_to_smt_type Ty) u)
              (__eo_to_smt (Term.Var (Term.String sy) Ty)) = u := by
          change native_model_var_lookup
            (native_model_push M sy (__eo_to_smt_type Ty) u)
              sy (__eo_to_smt_type Ty) = u
          simp [native_model_var_lookup, native_model_push]
        have hEvalApply : __smtx_model_eval
            (native_model_push M sy (__eo_to_smt_type Ty) u)
              (__eo_to_smt
                (Term.Apply c (Term.Var (Term.String sy) Ty))) =
            SmtValue.Apply (__smtx_model_eval M (__eo_to_smt c)) u := by
          rw [dtEoSpine_apply_translation hSpine]
          have hGenericEval := generic_apply_eval_of_non_datatype_head
            (x := __eo_to_smt (Term.Var (Term.String sy) Ty))
            hNotSel hNotTester
          unfold generic_apply_eval at hGenericEval
          rw [hGenericEval]
          rw [hEvalC, hEvalY]
          exact smt_model_eval_apply_of_dt_head M _ _ hEvalHead huNN
        refine ⟨sy, Ty, u, rfl, huTy, huCanon, ?_⟩
        have hNodup := conjAbsorbed_nodup_of_typed
          (ConjRel.absorb hFind hFree hTail) hRelTy
        have hCurrentNotTail : Term.Var (Term.String sy) Ty ∉
            conjAbsorbed hTail := by
          simpa [conjAbsorbed] using (List.nodup_cons.mp hNodup).1
        have hTailFresh : ∀ z, z ∈ conjAbsorbed hTail ->
            __contains_atomic_term_list_free_rec
                (Term.Apply c (Term.Var (Term.String sy) Ty))
                (eoCons z Term.__eo_List_nil) Term.__eo_List_nil =
              Term.Boolean false := by
          intro z hz
          obtain ⟨sz, Tz, rfl⟩ :=
            (conjAbsorbed_prefix_of_forall hTail).var_shape_of_mem_env
              hTailEnv hz
          have hHeadNe : Term.Var (Term.String sy) Ty ≠
              Term.Var (Term.String sz) Tz := by
            intro hEq
            apply hCurrentNotTail
            simpa [hEq] using hz
          have hCFree := hFresh (Term.Var (Term.String sz) Tz)
            (by simp [conjAbsorbed, hz])
          have hYFree : __contains_atomic_term_list_free_rec
                (Term.Var (Term.String sy) Ty)
                (eoCons (Term.Var (Term.String sz) Tz) Term.__eo_List_nil)
                Term.__eo_List_nil = Term.Boolean false := by
            have hKeyNe : (sy, Ty) ≠ (sz, Tz) := by
              intro hEq
              cases hEq
              exact hHeadNe rfl
            have hFindNeg : __eo_is_neg
                (__eo_list_find Term.__eo_List_cons
                  (eoCons (Term.Var (Term.String sz) Tz)
                    Term.__eo_List_nil)
                  (Term.Var (Term.String sy) Ty)) = Term.Boolean true :=
              (EoVarEnv.cons EoVarEnv.nil).find_neg_true_of_not_mem
                (by simpa using hKeyNe)
            rw [show __contains_atomic_term_list_free_rec
                  (Term.Var (Term.String sy) Ty)
                  (eoCons (Term.Var (Term.String sz) Tz) Term.__eo_List_nil)
                  Term.__eo_List_nil =
                __eo_ite
                  (__eo_is_neg (__eo_list_find Term.__eo_List_cons
                    (eoCons (Term.Var (Term.String sz) Tz)
                      Term.__eo_List_nil)
                    (Term.Var (Term.String sy) Ty)))
                  (Term.Boolean false)
                  (__eo_is_neg (__eo_list_find Term.__eo_List_cons
                    Term.__eo_List_nil
                    (Term.Var (Term.String sy) Ty))) from rfl,
              hFindNeg]
            rfl
          exact contains_atomic_term_list_free_rec_apply_false_intro
            hNotList hCFree hYFree
        have hTailNotList : ∀ q z zs,
            Term.Apply c (Term.Var (Term.String sy) Ty) ≠
              Term.Apply q (eoCons z zs) := by
          intro q z zs hEq
          injection hEq with hFun hArg
          simp [eoCons] at hArg
        refine ih (DtEoSpine.app (Term.Var (Term.String sy) Ty) hSpine)
          hTailFresh hTailNotList
          (native_model_push M sy (__eo_to_smt_type Ty) u) v us ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [gEnc_forall]
          exact smtx_typeof_not_bool_intro hTailTy
        · simpa [conjFinal] using hFinalTy
        · simpa [conjAbsorbed] using hLen
        · intro j hj
          have hJ := hArgTy (Nat.succ j) (by simpa using Nat.succ_lt_succ hj)
          simpa [conjAbsorbed] using hJ
        · intro a ha
          exact hCanon a (List.mem_cons_of_mem u ha)
        · rw [hEvalApply]
          simpa [__smtx_apply_head_value] using hEvalHead
        · rw [hEvalApply]
          simpa [vsmMkSpine] using hTarget
  | @unwrap c G hCxType hSubst =>
      intro hSpine hFresh hNotList M v args hTy hFinalTy hLen hArgTy hCanon
        hEvalHead hTarget
      cases args with
      | nil =>
        change __smtx_model_eval M (__eo_to_smt c) = v
        exact hTarget.symm
      | cons u us => simp [conjAbsorbed] at hLen
  | @final cx g hCxTy hNotForall hSubst =>
      intro hSpine hFresh hNotList M v args hTy hFinalTy hLen hArgTy hCanon
        hEvalHead hTarget
      cases args with
      | nil =>
        change __smtx_model_eval M (__eo_to_smt cx) = v
        exact hTarget.symm
      | cons u us => simp [conjAbsorbed] at hLen

theorem conj_ctor_inst_from_values
    (s : native_String) (d : DatatypeDecl) (i : Nat)
    (hReserved : __eo_to_smt_reserved_datatype_name s = false) :
    ∀ {x F ys g : Term}
      (rel : ConjRel x F (Term.DtCons s d i) ys g),
      ∀ (M : SmtModel) (v : SmtValue) (args : List SmtValue),
      __smtx_typeof (gEnc g) = SmtType.Bool ->
      __smtx_typeof (__eo_to_smt (conjFinal rel)) =
        SmtType.Datatype s (__eo_to_smt_datatype_decl d) ->
      args.length = (conjAbsorbed rel).length ->
      (∀ j, j < args.length ->
        __smtx_typeof_value args[j]! =
          __smtx_typeof (__eo_to_smt (conjAbsorbed rel)[j]!)) ->
      (∀ u ∈ args, __smtx_value_canonical u = true) ->
      __smtx_apply_head_value
          (__smtx_model_eval M (__eo_to_smt (Term.DtCons s d i))) =
        SmtValue.DtCons s (__eo_to_smt_datatype_decl d) i ->
      v = vsmMkSpine
        (__smtx_model_eval M (__eo_to_smt (Term.DtCons s d i))) args ->
      CtorInst x F rel M v := by
  intro x F ys g rel
  refine conj_ctor_inst_from_values_aux s d i hReserved rel
    (DtEoSpine.root s d i) ?_ ?_
  · intro z hz
    simp [__contains_atomic_term_list_free_rec, __is_closed_rec,
      __eo_requires, native_ite, native_teq, native_not]
  · intro q z zs hEq
    simp [eoCons] at hEq

/-! ## Semantic core

Proof structure for `split_forward` / `split_backward`:

Vocabulary. Work through `smtForallEnc zs B := SmtTerm.not (__eo_to_smt_exists
zs (SmtTerm.not B))`, never through `__eo_to_smt` of virtual `mkForall zs G`
terms (the nil-binder case translates to `SmtTerm.None`).  A single-binder
step-iff (`eval M (not (exists s T tail)) = true ↔ ∀ v typed-canonical, eval
(push M s T v) (not tail) = true`, with `not tail` again an encoding) drives
the per-binder recursion; it is the one-step form of
`forall_encoding_true_iff` above.

Forward.  Characterize the LHS with `forall_encoding_true_iff`, then bridge to
"x pushed last": from `∀ N, Inst M (x::ys) N → eval N F̂ = true` derive
`H(M₀, ysRem) := ∀ N, Inst M₀ ysRem N → ∀ v typed-canonical at D̂, eval (push N
xkey v) F̂ = true` by induction over the `Inst` chain using push-reordering
(function-update equalities: `push_comm` for distinct keys, `push_same` for
equal keys — cf. the private lemmas in `Quant_var_reordering.lean:113,138`);
the x∈ys collision resolves because pushing the colliding retained binder with
`v` yields the same model function.  Then induct on `ConjRel`: `peel` consumes
a binder via step-iff and specializes `H`; `absorb` consumes a constructor-arg
binder (its key is insensitive for F̂ by the guard's freshness check, via
`smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped`);
`unwrap` is double-negation elimination (typing threaded via
`smtx_typeof_exists_tail_bool_of_cons_bool`); at `final`, rewrite with
`InstantiateRule.substitute_simul_eval` (actuals: the single binder x mapped to
the built constructor application cx) and instantiate `H` at `v := eval ĉx`,
which is typed-canonical by the spine lemmas plus the occurrence-typing
inversion below.

Backward.  Intro an LHS instantiation `N`; extract its push list; let `veff` be
the final value at x's key (handles x∈ys); decompose `veff` with
`datatype_value_spine`; the constructor index picks the conjunct out of
`SplitRel` (the guard consumed `__dt_get_constructors` in order, so the i-th
conjunct's seed is `Term.DtCons s d i` — correspondence via
`__eo_datatype_constructors_rec`); instantiate that conjunct's binders with the
retained values and the spine arguments (typed correctly by occurrence-typing);
at `final`, `substitute_simul_eval` gives `eval (push M₂ xkey veff) F̂ = true`
and the model equals `N` up to constructor-arg keys (insensitive) and push
order.

Occurrence-typing inversion: if x occurs free in
F and `__smtx_typeof (__eo_to_smt (substOne x cx F)) ≠ SmtType.None` then
`__smtx_typeof (__eo_to_smt cx) ≠ SmtType.None`; together with the computed
`DtcAppType` chain of `SmtTerm.DtCons` this forces each absorbed binder type to
equal the corresponding (substituted) selector type and the result type to be
`D̂`.  When x is NOT free in F, `substOne x cx F = F` and both directions avoid
the spine entirely: F̂ is insensitive to the constructor-arg keys and to x's
key, and a typed-canonical witness for instantiating comes from
`model_wf` lookups (every well-formed type is inhabited in M).

Both directions case on `__contains_atomic_term_list_free_rec F [x] nil`.
-/

/-- The equality formula concluded by the rule. -/
abbrev qdsFormula (x ys F G : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (mkForall (eoCons x ys) F)) G

theorem smtx_typeof_eq_bool_elim
    {L R : SmtTerm}
    (hTy : __smtx_typeof (SmtTerm.eq L R) = SmtType.Bool) :
    __smtx_typeof L = __smtx_typeof R := by
  rw [show __smtx_typeof (SmtTerm.eq L R) =
    __smtx_typeof_eq (__smtx_typeof L) (__smtx_typeof R) from by
      simp only [__smtx_typeof]] at hTy
  rw [__smtx_typeof_eq] at hTy
  by_cases hEq : native_Teq (__smtx_typeof L) (__smtx_typeof R) = true
  · simpa [native_Teq] using hEq
  · exfalso
    have hf : native_Teq (__smtx_typeof L) (__smtx_typeof R) = false := by
      cases hv : native_Teq (__smtx_typeof L) (__smtx_typeof R)
      · rfl
      · exact absurd hv hEq
    rw [hf] at hTy
    simp only [native_ite] at hTy
    rw [__smtx_typeof_guard] at hTy
    by_cases hN : native_Teq (__smtx_typeof L) SmtType.None = true
    · rw [hN] at hTy
      simp [native_ite] at hTy
    · have hNf : native_Teq (__smtx_typeof L) SmtType.None = false := by
        cases hv : native_Teq (__smtx_typeof L) SmtType.None
        · rfl
        · exact absurd hv hN
      rw [hNf] at hTy
      simp [native_ite] at hTy


theorem smtx_typeof_eq_bool_left_ne_none
    {L R : SmtTerm}
    (hTy : __smtx_typeof (SmtTerm.eq L R) = SmtType.Bool) :
    __smtx_typeof L ≠ SmtType.None := by
  intro hN
  rw [show __smtx_typeof (SmtTerm.eq L R) =
    __smtx_typeof_eq (__smtx_typeof L) (__smtx_typeof R) from by
      simp only [__smtx_typeof]] at hTy
  rw [__smtx_typeof_eq, __smtx_typeof_guard, hN] at hTy
  simp [native_ite, native_Teq] at hTy


theorem smtx_typeof_not_bool_or_none (X : SmtTerm) :
    __smtx_typeof (SmtTerm.not X) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.not X) = SmtType.None := by
  rw [show __smtx_typeof (SmtTerm.not X) =
    native_ite (native_Teq (__smtx_typeof X) SmtType.Bool) SmtType.Bool SmtType.None from by
      simp only [__smtx_typeof]]
  by_cases h : native_Teq (__smtx_typeof X) SmtType.Bool = true
  · rw [h]; left; rfl
  · have hf : native_Teq (__smtx_typeof X) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof X) SmtType.Bool
      · rfl
      · exact absurd hv h
    rw [hf]; right; rfl

/-- EO list of datatype-constructor terms. -/
inductive EoCtorList : Term -> Prop where
  | nil : EoCtorList Term.__eo_List_nil
  | cons {c rest : Term} :
      CH c ->
      EoCtorList rest ->
      EoCtorList (eoCons c rest)

/-- Zero-based membership in an EO constructor list.  Keeping the selected
constructor in the relation makes the correspondence with a datatype value's
constructor index explicit. -/
inductive EoCtorAt : Term -> Nat -> Term -> Prop where
  | head {c rest : Term} : EoCtorAt (eoCons c rest) 0 c
  | tail {h rest c : Term} {i : Nat} :
      EoCtorAt rest i c -> EoCtorAt (eoCons h rest) (Nat.succ i) c

theorem eo_mk_apply_cons_ne_stuck {t y : Term} (hy : y ≠ Term.Stuck) :
    __eo_mk_apply (Term.Apply Term.__eo_List_cons t) y = eoCons t y := by
  cases y <;> first | rfl | exact absurd rfl hy

theorem eoCtorList_datatype_constructors_rec
    (s : native_String) (d : DatatypeDecl) :
    ∀ (d' : Datatype) (i : native_Nat),
      EoCtorList (__eo_datatype_constructors_rec s d d' i)
  | Datatype.null, i => EoCtorList.nil
  | Datatype.sum c d2, i => by
      rw [show __eo_datatype_constructors_rec s d (Datatype.sum c d2) i =
        __eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s d i))
          (__eo_datatype_constructors_rec s d d2 (native_nat_succ i)) from rfl]
      rw [eo_mk_apply_cons_ne_stuck
        (eo_datatype_constructors_rec_ne_stuck s d d2 (native_nat_succ i))]
      exact EoCtorList.cons (CH.datatype s d i)
        (eoCtorList_datatype_constructors_rec s d d2 (native_nat_succ i))

/-- The relative `i`th entry generated from a datatype tail is the constructor
whose absolute index is `start + i`. -/
theorem eoCtorAt_datatype_constructors_rec
    (s : native_String) (root : DatatypeDecl) :
    ∀ (current : Datatype) (start i : Nat),
      i < eoDatatypeNumCtors current ->
      EoCtorAt (__eo_datatype_constructors_rec s root current start) i
        (Term.DtCons s root (start + i))
  | Datatype.null, start, i, hLt => by
      simp [eoDatatypeNumCtors] at hLt
  | Datatype.sum c tail, start, 0, hLt => by
      rw [show __eo_datatype_constructors_rec s root (Datatype.sum c tail) start =
        __eo_mk_apply (Term.Apply Term.__eo_List_cons
          (Term.DtCons s root start))
          (__eo_datatype_constructors_rec s root tail (Nat.succ start)) from rfl]
      rw [eo_mk_apply_cons_ne_stuck
        (eo_datatype_constructors_rec_ne_stuck s root tail (Nat.succ start))]
      simpa using (EoCtorAt.head : EoCtorAt
        (eoCons (Term.DtCons s root start)
          (__eo_datatype_constructors_rec s root tail (Nat.succ start))) 0
        (Term.DtCons s root start))
  | Datatype.sum c tail, start, Nat.succ i, hLt => by
      have hTailLt : i < eoDatatypeNumCtors tail := by
        simpa [eoDatatypeNumCtors] using Nat.succ_lt_succ_iff.mp hLt
      rw [show __eo_datatype_constructors_rec s root (Datatype.sum c tail) start =
        __eo_mk_apply (Term.Apply Term.__eo_List_cons
          (Term.DtCons s root start))
          (__eo_datatype_constructors_rec s root tail (Nat.succ start)) from rfl]
      rw [eo_mk_apply_cons_ne_stuck
        (eo_datatype_constructors_rec_ne_stuck s root tail (Nat.succ start))]
      have hAt := EoCtorAt.tail (h := Term.DtCons s root start)
        (eoCtorAt_datatype_constructors_rec s root tail (Nat.succ start) i hTailLt)
      have hIdx : Nat.succ start + i = start + Nat.succ i := by omega
      rw [← hIdx]
      exact hAt

/-- Truth of an `and` exposes truth of both operands. -/
theorem smt_eval_and_eq_true
    {v₁ v₂ : SmtValue}
    (h : __smtx_model_eval_and v₁ v₂ = SmtValue.Boolean true) :
    v₁ = SmtValue.Boolean true ∧ v₂ = SmtValue.Boolean true := by
  cases v₁ <;> cases v₂ <;> simp [__smtx_model_eval_and] at h
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [SmtEval.native_and] at h ⊢

private theorem smtx_typeof_and_bool_inv_early
    {a b : SmtTerm} (h : __smtx_typeof (SmtTerm.and a b) = SmtType.Bool) :
    __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [show __smtx_typeof (SmtTerm.and a b) =
    native_ite (native_Teq (__smtx_typeof a) SmtType.Bool)
      (native_ite (native_Teq (__smtx_typeof b) SmtType.Bool) SmtType.Bool
        SmtType.None) SmtType.None from by simp only [__smtx_typeof]] at h
  by_cases ha : native_Teq (__smtx_typeof a) SmtType.Bool = true
  · refine ⟨by simpa [native_Teq] using ha, ?_⟩
    rw [ha] at h
    simp only [native_ite, if_true] at h
    by_cases hb : native_Teq (__smtx_typeof b) SmtType.Bool = true
    · simpa [native_Teq] using hb
    · have hbf : native_Teq (__smtx_typeof b) SmtType.Bool = false := by
        cases hv : native_Teq (__smtx_typeof b) SmtType.Bool
        · rfl
        · exact absurd hv hb
      rw [hbf] at h
      simp at h
  · have haf : native_Teq (__smtx_typeof a) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof a) SmtType.Bool
      · rfl
      · exact absurd hv ha
    rw [haf] at h
    simp [native_ite] at h

/-- Select the conjunct corresponding to a constructor-list entry. -/
theorem splitRel_pick_true
    (M : SmtModel) {x ys F cs G c : Term} {i : Nat}
    (rel : SplitRel x ys F cs G)
    (hAt : EoCtorAt cs i c)
    (hTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool)
    (hTrue : __smtx_model_eval M (__eo_to_smt G) =
      SmtValue.Boolean true) :
    ∃ (g : Term) (_ : ConjRel x F c ys g),
      __smtx_typeof (__eo_to_smt g) = SmtType.Bool ∧
      __smtx_model_eval M (__eo_to_smt g) = SmtValue.Boolean true := by
  induction rel generalizing i c with
  | @single c' g hConj =>
      cases hAt with
      | head => exact ⟨g, hConj, hTy, hTrue⟩
      | tail hTail => cases hTail
  | nil_true => cases hAt
  | @step c' cs' g G' hConj hRest ih =>
      rw [show __eo_to_smt (mkAnd g G') =
        SmtTerm.and (__eo_to_smt g) (__eo_to_smt G') from rfl] at hTy
      obtain ⟨hgTy, hG'Ty⟩ := smtx_typeof_and_bool_inv_early hTy
      rw [show __eo_to_smt (mkAnd g G') =
        SmtTerm.and (__eo_to_smt g) (__eo_to_smt G') from rfl] at hTrue
      have hAnd : __smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt g))
          (__smtx_model_eval M (__eo_to_smt G')) =
          SmtValue.Boolean true := by
        simpa only [__smtx_model_eval] using hTrue
      obtain ⟨hg, hG'⟩ := smt_eval_and_eq_true hAnd
      cases hAt with
      | head => exact ⟨g, hConj, hgTy, hg⟩
      | tail hTail => exact ih hTail hG'Ty hG'

/-- Bool-typed `and` inversion. -/
theorem smtx_typeof_and_bool_inv
    {a b : SmtTerm} (h : __smtx_typeof (SmtTerm.and a b) = SmtType.Bool) :
    __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool := by
  rw [show __smtx_typeof (SmtTerm.and a b) =
    native_ite (native_Teq (__smtx_typeof a) SmtType.Bool)
      (native_ite (native_Teq (__smtx_typeof b) SmtType.Bool) SmtType.Bool
        SmtType.None) SmtType.None from by simp only [__smtx_typeof]] at h
  by_cases ha : native_Teq (__smtx_typeof a) SmtType.Bool = true
  · refine ⟨by simpa [native_Teq] using ha, ?_⟩
    rw [ha] at h
    simp only [native_ite, if_true] at h
    by_cases hb : native_Teq (__smtx_typeof b) SmtType.Bool = true
    · simpa [native_Teq] using hb
    · exfalso
      have hbf : native_Teq (__smtx_typeof b) SmtType.Bool = false := by
        cases hv : native_Teq (__smtx_typeof b) SmtType.Bool
        · rfl
        · exact absurd hv hb
      rw [hbf] at h
      simp at h
  · exfalso
    have haf : native_Teq (__smtx_typeof a) SmtType.Bool = false := by
      cases hv : native_Teq (__smtx_typeof a) SmtType.Bool
      · rfl
      · exact absurd hv ha
    rw [haf] at h
    simp [native_ite] at h

theorem splitRel_stuck_false
    {x ys F G : Term} : SplitRel x ys F Term.Stuck G -> False := by
  intro h
  cases h

theorem dt_get_constructors_apply_stuck_of_wf_not_tuple
    (DC T : Term)
    (hNotTuple : ∀ U, DC ≠ Term.Apply (Term.UOp UserOp.Tuple) U)
    (hWf : __smtx_type_wf (__eo_to_smt_type (Term.Apply DC T)) = true) :
    __dt_get_constructors (Term.Apply DC T) = Term.Stuck := by
  cases DC <;>
    simp_all [__dt_get_constructors, __eo_to_smt_type, __smtx_type_wf,
      __smtx_type_wf_component, __smtx_type_wf_rec, native_and]
  case UOp op =>
    cases op <;>
      simp_all [__dt_get_constructors, __eo_dt_constructors,
        __eo_dt_constructors_main, __eo_to_smt_type]
    all_goals
      exfalso
      exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hWf
  case Apply f U =>
    cases f <;>
      simp_all [__dt_get_constructors, __eo_dt_constructors,
        __eo_dt_constructors_main, __eo_to_smt_type]
    all_goals
      try
        exfalso
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hWf
    case UOp op =>
      cases op <;>
        simp_all [__dt_get_constructors, __eo_dt_constructors,
          __eo_dt_constructors_main, __eo_to_smt_type]
      all_goals
        exfalso
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hWf

/--
The non-datatype tracks of the forward direction: tuple/unit-tuple split
variables (deferred) and the impossible junk-type shapes (whose constructor
lists are `Stuck` or whose types are untranslatable).
-/
theorem split_forward_nondatatype
    (M : SmtModel) (hM : model_wf M)
    (sx : native_String) (xT ys F G : Term)
    (hxT : ∀ s d, xT ≠ Term.DatatypeType s d)
    (srel : SplitRel (Term.Var (Term.String sx) xT) ys F
      (__dt_get_constructors xT) G)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F)
    (hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool)
    (hH : ∀ N, ForallInstantiationModel M ys N ->
      ∀ v : SmtValue,
        __smtx_typeof_value v = __eo_to_smt_type xT ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval
            (native_model_push N sx (__eo_to_smt_type xT) v)
            (__eo_to_smt F) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  have chain : ∀ {cs G' : Term},
      SplitRel (Term.Var (Term.String sx) xT) ys F cs G' ->
      EoCtorList cs ->
      __smtx_typeof (__eo_to_smt G') = SmtType.Bool ->
      __smtx_model_eval M (__eo_to_smt G') = SmtValue.Boolean true := by
    intro cs G' rel
    induction rel with
    | @single c g hConj =>
        intro hCs hTy
        have hHead : CH c := by
          cases hCs with
          | cons hHead _ => exact hHead
        have hEnc : gEnc g = __eo_to_smt g :=
          gEnc_eq_eo_to_smt_of_bool hTy
        have hTrue := conj_forward_aux sx xT F hWfX hFTrans hConj
          (CS.head hHead) M hM (by rw [hEnc]; exact hTy) hH
        rwa [hEnc] at hTrue
    | nil_true =>
        intro _ _
        rfl
    | @step c cs' g G'' hConj hRest ih =>
        intro hCs hTy
        have hHead : CH c := by
          cases hCs with
          | cons hHead _ => exact hHead
        have hCs' : EoCtorList cs' := by
          cases hCs with
          | cons _ hTail => exact hTail
        rw [show __eo_to_smt (mkAnd g G'') =
          SmtTerm.and (__eo_to_smt g) (__eo_to_smt G'') from rfl] at hTy ⊢
        obtain ⟨hgTy, hRestTy⟩ := smtx_typeof_and_bool_inv hTy
        have hEnc : gEnc g = __eo_to_smt g :=
          gEnc_eq_eo_to_smt_of_bool hgTy
        have hg : __smtx_model_eval M (__eo_to_smt g) =
            SmtValue.Boolean true := by
          have hTrue := conj_forward_aux sx xT F hWfX hFTrans hConj
            (CS.head hHead) M hM (by rw [hEnc]; exact hgTy) hH
          rwa [hEnc] at hTrue
        have hRestTrue := ih hCs' hRestTy
        rw [show __smtx_model_eval M
            (SmtTerm.and (__eo_to_smt g) (__eo_to_smt G'')) =
          __smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt g))
            (__smtx_model_eval M (__eo_to_smt G'')) from by
              simp only [__smtx_model_eval]]
        rw [hg, hRestTrue]
        rfl
  have impossible (T : Term)
      (hCs : __dt_get_constructors T = Term.Stuck)
      (hRel : SplitRel (Term.Var (Term.String sx) T) ys F
        (__dt_get_constructors T) G) : False := by
    apply splitRel_stuck_false
    simpa [hCs] using hRel
  fun_cases __dt_get_constructors xT
  case case1 => exact False.elim (impossible _ rfl srel)
  case case2 =>
    exact chain srel
      (by simpa [__dt_get_constructors, __eo_dt_constructors,
        __eo_dt_constructors_main] using
          (EoCtorList.cons CH.tuple EoCtorList.nil)) hGTy
  case case3 =>
    exact chain srel
      (by simpa [__dt_get_constructors, __eo_dt_constructors,
        __eo_dt_constructors_main] using
          (EoCtorList.cons CH.tupleUnit EoCtorList.nil)) hGTy
  case case4 =>
    exact False.elim (impossible _
      (dt_get_constructors_apply_stuck_of_wf_not_tuple _ _ (by assumption) hWfX)
      srel)
  case case5 =>
    exact False.elim (impossible _ (by
      simp_all [__dt_get_constructors, __eo_dt_constructors,
        __eo_dt_constructors_main]) srel)

/--
Forward direction over the conjunction: walk the `SplitRel` chain, discharging
each conjunct with `conj_forward_aux`.
-/
theorem split_forward_chain
    (M : SmtModel) (hM : model_wf M)
    (sx : native_String) (xT ys F : Term)
    (hWfX : __smtx_type_wf (__eo_to_smt_type xT) = true)
    (hFTrans : eoHasSmtTranslation F)
    (hH : ∀ N, ForallInstantiationModel M ys N ->
      ∀ v : SmtValue,
        __smtx_typeof_value v = __eo_to_smt_type xT ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval
            (native_model_push N sx (__eo_to_smt_type xT) v)
            (__eo_to_smt F) = SmtValue.Boolean true) :
    ∀ {cs G : Term},
      SplitRel (Term.Var (Term.String sx) xT) ys F cs G ->
      EoCtorList cs ->
      __smtx_typeof (__eo_to_smt G) = SmtType.Bool ->
      __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  intro cs G srel
  induction srel with
  | @single c g hConj =>
      intro hCs hGTy
      have hHead : CH c := by
        cases hCs with
        | cons hHead _ => exact hHead
      have hEnc : gEnc g = __eo_to_smt g := gEnc_eq_eo_to_smt_of_bool hGTy
      have := conj_forward_aux sx xT F hWfX hFTrans hConj
        (CS.head hHead) M hM
        (by rw [hEnc]; exact hGTy) hH
      rw [hEnc] at this
      exact this
  | nil_true =>
      intro _ _
      rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true from rfl]
      rfl
  | @step c cs' g G' hConj hRest ih =>
      intro hCs hGTy
      have hHead : CH c := by
        cases hCs with
        | cons hHead _ => exact hHead
      have hCs' : EoCtorList cs' := by
        cases hCs with
        | cons _ hTail => exact hTail
      rw [show __eo_to_smt (mkAnd g G') =
        SmtTerm.and (__eo_to_smt g) (__eo_to_smt G') from rfl] at hGTy ⊢
      obtain ⟨hgTy, hG'Ty⟩ := smtx_typeof_and_bool_inv hGTy
      have hEnc : gEnc g = __eo_to_smt g := gEnc_eq_eo_to_smt_of_bool hgTy
      have hg : __smtx_model_eval M (__eo_to_smt g) = SmtValue.Boolean true := by
        have := conj_forward_aux sx xT F hWfX hFTrans hConj
          (CS.head hHead) M hM
          (by rw [hEnc]; exact hgTy) hH
        rw [hEnc] at this
        exact this
      have hG' : __smtx_model_eval M (__eo_to_smt G') = SmtValue.Boolean true :=
        ih hCs' hG'Ty
      rw [show __smtx_model_eval M
          (SmtTerm.and (__eo_to_smt g) (__eo_to_smt G')) =
        __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt g))
          (__smtx_model_eval M (__eo_to_smt G')) from by
          simp only [__smtx_model_eval]]
      rw [hg, hG']
      rfl

/--
Forward direction: if the left-hand universal is true, the conjunction produced
by a successful guard run is true.
-/
theorem split_forward
    (M : SmtModel) (hM : model_wf M)
    (x ys F G : Term)
    (srel : SplitRel x ys F (__dt_get_constructors (__eo_typeof x)) G)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool)
    (hLHS : __smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true := by
  -- SMT-side Bool typing of both sides
  have hSmtBool : RuleProofs.eo_has_bool_type (qdsFormula x ys F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTrans hTy
  rw [RuleProofs.eo_has_bool_type] at hSmtBool
  rw [show __eo_to_smt (qdsFormula x ys F G) =
    SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G)
    from rfl] at hSmtBool
  have hLTy : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtType.Bool := by
    have hNe := smtx_typeof_eq_bool_left_ne_none hSmtBool
    have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
        SmtTerm.not (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
      SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil
        (eoCons x ys) F (by intro h; cases h)
    rw [hForm] at hNe ⊢
    rcases smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) with hB | hN
    · exact hB
    · exact absurd hN hNe
  have hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
    rw [← smtx_typeof_eq_bool_elim hSmtBool]
    exact hLTy
  -- the split variable is a string-named variable
  have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
      SmtTerm.not (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
    SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil
      (eoCons x ys) F (by intro h; cases h)
  have hExlTy : __smtx_typeof
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
    rw [hForm] at hLTy
    exact smtx_typeof_not_bool_inv hLTy
  obtain ⟨sx, xT, rfl⟩ := exl_cons_bool_var_shape hExlTy
  rw [show __eo_to_smt_exists (eoCons (Term.Var (Term.String sx) xT) ys)
      (SmtTerm.not (__eo_to_smt F)) =
    SmtTerm.exists sx (__eo_to_smt_type xT)
      (__eo_to_smt_exists ys (SmtTerm.not (__eo_to_smt F))) from rfl] at hExlTy
  obtain ⟨hTailTy, hWfX⟩ := smtx_typeof_exists_bool_inv hExlTy
  -- translation facts for F
  have hFTrans : eoHasSmtTranslation F := by
    have hFBool : RuleProofs.eo_has_bool_type F := by
      exact SubstituteTranslatabilitySupport.forall_body_has_bool_type_of_has_smt_translation
        (eoCons (Term.Var (Term.String sx) xT) ys) F
        (RuleProofs.eo_has_smt_translation_of_has_bool_type _ (by
          rw [RuleProofs.eo_has_bool_type]
          exact hLTy))
    rw [RuleProofs.eo_has_bool_type] at hFBool
    rw [eoHasSmtTranslation, hFBool]
    intro h
    cases h
  -- LHS characterization and the push-last form
  have hLForall : RuleProofs.eo_has_smt_translation
      (mkForall (eoCons (Term.Var (Term.String sx) xT) ys) F) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ (by
      rw [RuleProofs.eo_has_bool_type]
      exact hLTy)
  obtain ⟨vars, hEnv⟩ :=
    SubstituteTranslatabilitySupport.forall_binders_env_of_has_smt_translation
      (eoCons (Term.Var (Term.String sx) xT) ys) F hLForall
  have hWfAll := SubstituteTranslatabilitySupport.forall_binder_types_wf_of_has_smt_translation
    hLForall hEnv
  have hFBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
    have := SubstituteTranslatabilitySupport.forall_body_has_bool_type_of_has_smt_translation
      (eoCons (Term.Var (Term.String sx) xT) ys) F hLForall
    rw [RuleProofs.eo_has_bool_type] at this
    exact this
  have hAllInst : ∀ N, ForallInstantiationModel M
      (eoCons (Term.Var (Term.String sx) xT) ys) N ->
      __smtx_model_eval N (__eo_to_smt F) = SmtValue.Boolean true := by
    have hIff := forall_encoding_true_iff hEnv hWfAll hFBodyTy M hM
    rw [hForm] at hLHS
    exact hIff.1 hLHS
  have hH := lhs_gives_push_last M sx xT ys F hWfX hAllInst
  -- dispatch on the split variable's type
  by_cases hDt : ∃ s d, __eo_typeof (Term.Var (Term.String sx) xT) =
      Term.DatatypeType s d
  · obtain ⟨sD, dD, hxT⟩ := hDt
    rw [show __eo_typeof (Term.Var (Term.String sx) xT) = xT from rfl] at hxT
    subst hxT
    have hCs : EoCtorList (__dt_get_constructors
        (__eo_typeof (Term.Var (Term.String sx)
          (Term.DatatypeType sD dD)))) := by
      rw [show __eo_typeof (Term.Var (Term.String sx)
          (Term.DatatypeType sD dD)) = Term.DatatypeType sD dD from rfl]
      rw [show __dt_get_constructors (Term.DatatypeType sD dD) =
        __eo_datatype_constructors_rec sD dD (__eo_dd_lookup sD dD)
          native_nat_zero from rfl]
      exact eoCtorList_datatype_constructors_rec sD dD
        (__eo_dd_lookup sD dD) native_nat_zero
    exact split_forward_chain M hM sx (Term.DatatypeType sD dD) ys F hWfX hFTrans hH
      srel hCs hGTy
  · refine split_forward_nondatatype M hM sx xT ys F G ?_ ?_ hWfX hFTrans hGTy hH
    · intro s d hc
      exact hDt ⟨s, d, hc⟩
    · rw [show __eo_typeof (Term.Var (Term.String sx) xT) = xT from rfl] at srel
      exact srel

/--
Backward direction: if the conjunction produced by a successful guard run is
true, the left-hand universal is true.
-/
theorem split_backward
    (M : SmtModel) (hM : model_wf M)
    (x ys F G : Term)
    (srel : SplitRel x ys F (__dt_get_constructors (__eo_typeof x)) G)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool)
    (hRHS : __smtx_model_eval M (__eo_to_smt G) = SmtValue.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtValue.Boolean true := by
  have hSmtBool : RuleProofs.eo_has_bool_type (qdsFormula x ys F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTrans hTy
  rw [RuleProofs.eo_has_bool_type] at hSmtBool
  rw [show __eo_to_smt (qdsFormula x ys F G) =
    SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G)
    from rfl] at hSmtBool
  have hLTy : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) =
      SmtType.Bool := by
    have hNe := smtx_typeof_eq_bool_left_ne_none hSmtBool
    have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
        SmtTerm.not
          (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
      SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil
        (eoCons x ys) F (by intro h; cases h)
    rw [hForm] at hNe ⊢
    rcases smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) with
      hB | hN
    · exact hB
    · exact absurd hN hNe
  have hGTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
    rw [← smtx_typeof_eq_bool_elim hSmtBool]
    exact hLTy
  have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
      SmtTerm.not
        (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
    SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil
      (eoCons x ys) F (by intro h; cases h)
  have hExlTy : __smtx_typeof
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
    rw [hForm] at hLTy
    exact smtx_typeof_not_bool_inv hLTy
  obtain ⟨sx, xT, rfl⟩ := exl_cons_bool_var_shape hExlTy
  rw [show __eo_to_smt_exists
        (eoCons (Term.Var (Term.String sx) xT) ys)
          (SmtTerm.not (__eo_to_smt F)) =
      SmtTerm.exists sx (__eo_to_smt_type xT)
        (__eo_to_smt_exists ys (SmtTerm.not (__eo_to_smt F))) from rfl]
    at hExlTy
  obtain ⟨hTailTy, hWfX⟩ := smtx_typeof_exists_bool_inv hExlTy
  have hLForall : RuleProofs.eo_has_smt_translation
      (mkForall (eoCons (Term.Var (Term.String sx) xT) ys) F) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ (by
      rw [RuleProofs.eo_has_bool_type]
      exact hLTy)
  obtain ⟨vars, hEnv⟩ :=
    SubstituteTranslatabilitySupport.forall_binders_env_of_has_smt_translation
      (eoCons (Term.Var (Term.String sx) xT) ys) F hLForall
  have hWfAll :=
    SubstituteTranslatabilitySupport.forall_binder_types_wf_of_has_smt_translation
      hLForall hEnv
  have hFBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool := by
    have h :=
      SubstituteTranslatabilitySupport.forall_body_has_bool_type_of_has_smt_translation
        (eoCons (Term.Var (Term.String sx) xT) ys) F hLForall
    rw [RuleProofs.eo_has_bool_type] at h
    exact h
  have hFTrans : eoHasSmtTranslation F := by
    rw [eoHasSmtTranslation, hFBodyTy]
    simp
  rw [hForm]
  refine forall_encoding_true_of_all_inst hEnv hWfAll hFBodyTy M hM ?_
  intro N hInst
  cases hInst with
  | cons hWfX' hvTy hvCanon hTailInst =>
    obtain ⟨N₀, w, hN₀, hwTy, hwCanon, hN⟩ :=
      inst_rebase_push_last sx (__eo_to_smt_type xT) hvTy hvCanon hTailInst
    by_cases hDt : ∃ s d, xT = Term.DatatypeType s d
    · obtain ⟨sD, dD, rfl⟩ := hDt
      have hReserved := datatype_name_not_reserved_of_type_wf sD dD hWfX
      have hwTyDt : __smtx_typeof_value w =
          SmtType.Datatype sD (__eo_to_smt_datatype_decl dD) := by
        simpa [__eo_to_smt_type, hReserved, native_ite] using hwTy
      obtain ⟨ci, args, hW, hCiLt, hArgLen, hArgTypes⟩ :=
        datatype_value_spine hwTyDt
      obtain ⟨hHeadCanon, hArgsCanon⟩ := vsm_canonical_spine w hwCanon
      have hCiLtEo : ci < eoDatatypeNumCtors (__eo_dd_lookup sD dD) := by
        rw [← TranslationProofs.eo_to_smt_dd_lookup] at hCiLt
        simpa [smtDatatypeNumCtors_eo_to_smt] using hCiLt
      have hAt : EoCtorAt
          (__dt_get_constructors
            (__eo_typeof
              (Term.Var (Term.String sx) (Term.DatatypeType sD dD))))
          ci (Term.DtCons sD dD ci) := by
        rw [show __eo_typeof
          (Term.Var (Term.String sx) (Term.DatatypeType sD dD)) =
            Term.DatatypeType sD dD from rfl]
        rw [show __dt_get_constructors (Term.DatatypeType sD dD) =
          __eo_datatype_constructors_rec sD dD (__eo_dd_lookup sD dD) 0 from rfl]
        simpa using
          (eoCtorAt_datatype_constructors_rec sD dD
            (__eo_dd_lookup sD dD) 0 ci hCiLtEo)
      obtain ⟨g, crel, hgTy, hgTrue⟩ :=
        splitRel_pick_true M srel hAt hGTy hRHS
      have hEnc : gEnc g = __eo_to_smt g :=
        gEnc_eq_eo_to_smt_of_bool hgTy
      have hgEncTy : __smtx_typeof (gEnc g) = SmtType.Bool := by
        rw [hEnc]
        exact hgTy
      have hgEncTrue : __smtx_model_eval M (gEnc g) =
          SmtValue.Boolean true := by
        rw [hEnc]
        exact hgTrue
      have hFinalTy : __smtx_typeof (__eo_to_smt (conjFinal crel)) =
          SmtType.Datatype sD (__eo_to_smt_datatype_decl dD) := by
        have h := conj_final_smt_type sx (Term.DatatypeType sD dD) F hWfX
          crel (CS.head (CH.datatype sD dD ci)) hgEncTy
        simpa [__eo_to_smt_type, hReserved, native_ite] using h
      have hFinalTo : __eo_to_smt (conjFinal crel) =
          List.foldl (fun f a => SmtTerm.Apply f (__eo_to_smt a))
            (SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci)
            (conjAbsorbed crel) := by
        rw [conjFinal_eq_spine crel]
        exact eo_to_smt_spine_dtcons sD dD ci (conjAbsorbed crel) hReserved
      have hQHead : qdsSmtApplyHead (__eo_to_smt (conjFinal crel)) =
          SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci := by
        rw [hFinalTo, qdsSmtApplyHead_foldl]
        rfl
      have hQArgs : qdsSmtApplyArgs (__eo_to_smt (conjFinal crel)) =
          (conjAbsorbed crel).map __eo_to_smt := by
        rw [hFinalTo, qdsSmtApplyArgs_foldl]
        rfl
      have hStaticTypes := qds_smt_dt_cons_arg_types hQHead (by
        rw [hFinalTy]
        simp)
      have hStaticLen := qds_smt_dt_cons_num_args_of_datatype hQHead hFinalTy
      have hFieldsLen : args.length = (conjAbsorbed crel).length := by
        calc
          args.length =
              __smtx_dt_num_sels
                (__smtx_dt_resolve
                  (__smtx_dd_lookup sD (__eo_to_smt_datatype_decl dD))
                  (__eo_to_smt_datatype_decl dD)) ci := hArgLen
          _ = qdsSmtNumApplyArgs (__eo_to_smt (conjFinal crel)) :=
            hStaticLen.symm
          _ = (qdsSmtApplyArgs (__eo_to_smt (conjFinal crel))).length :=
            (qdsSmtApplyArgs_length _).symm
          _ = (conjAbsorbed crel).length := by rw [hQArgs]; simp
      have hMatchTypes : ∀ j, j < args.length ->
          __smtx_typeof_value args[j]! =
            __smtx_typeof (__eo_to_smt (conjAbsorbed crel)[j]!) := by
        intro j hj
        have hStaticBound :
            j < (qdsSmtApplyArgs (__eo_to_smt (conjFinal crel))).length := by
          rw [hQArgs]
          simpa [hFieldsLen] using hj
        have hStatic := hStaticTypes j hStaticBound
        have hMap :
            (qdsSmtApplyArgs (__eo_to_smt (conjFinal crel)))[j]! =
              __eo_to_smt (conjAbsorbed crel)[j]! := by
          rw [hQArgs]
          have hjFields : j < (conjAbsorbed crel).length := by
            simpa [hFieldsLen] using hj
          simp [hjFields]
        calc
          __smtx_typeof_value args[j]! =
              __smtx_ret_typeof_sel_rec
                (__smtx_dt_resolve
                  (__smtx_dd_lookup sD (__eo_to_smt_datatype_decl dD))
                  (__eo_to_smt_datatype_decl dD)) ci j := hArgTypes j hj
          _ = __smtx_typeof
              (qdsSmtApplyArgs (__eo_to_smt (conjFinal crel)))[j]! := hStatic.symm
          _ = __smtx_typeof
              (__eo_to_smt (conjAbsorbed crel)[j]!) := congrArg __smtx_typeof hMap
      have hEvalHead : __smtx_apply_head_value
          (__smtx_model_eval N₀ (__eo_to_smt (Term.DtCons sD dD ci))) =
          SmtValue.DtCons sD (__eo_to_smt_datatype_decl dD) ci := by
        have hRootTo : __eo_to_smt (Term.DtCons sD dD ci) =
            SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci := by
          change native_ite (__eo_to_smt_reserved_datatype_name sD) SmtTerm.None
            (SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci) = _
          rw [hReserved]
          rfl
        rw [hRootTo]
        rfl
      have hTarget : w = vsmMkSpine
          (__smtx_model_eval N₀ (__eo_to_smt (Term.DtCons sD dD ci))) args := by
        have hRootTo : __eo_to_smt (Term.DtCons sD dD ci) =
            SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci := by
          change native_ite (__eo_to_smt_reserved_datatype_name sD) SmtTerm.None
            (SmtTerm.DtCons sD (__eo_to_smt_datatype_decl dD) ci) = _
          rw [hReserved]
          rfl
        rw [hRootTo]
        exact hW
      have hArgsCanon' : ∀ a ∈ args,
          __smtx_value_canonical a = true := by
        intro a ha
        apply hArgsCanon a
        have hArgs : vsmArgs w = args := by
          rw [hW, vsmArgs_vsmMkSpine]
          rfl
        rwa [hArgs]
      have hCI := conj_ctor_inst_from_values sD dD ci hReserved crel
        N₀ w args hgEncTy hFinalTy hFieldsLen
        hMatchTypes hArgsCanon' hEvalHead hTarget
      have hBody := conj_backward_aux sx (Term.DatatypeType sD dD) F hWfX
        hFTrans crel (CS.head (CH.datatype sD dD ci)) M hM hgEncTy hgEncTrue
        N₀ hN₀ w hCI
      rw [hN]
      exact hBody
    · have impossible (T : Term)
          (hCs : __dt_get_constructors T = Term.Stuck)
          (hRel : SplitRel (Term.Var (Term.String sx) T) ys F
            (__dt_get_constructors T) G) : False := by
        apply splitRel_stuck_false
        simpa [hCs] using hRel
      fun_cases __dt_get_constructors xT
      case neg.case1 => exact False.elim (impossible _ rfl srel)
      case neg.case2 =>
        rename_i T₁ T₂
        have hAt : EoCtorAt
            (__dt_get_constructors
              (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂)) 0
            (Term.UOp UserOp.tuple) := by
          simpa [__dt_get_constructors, __eo_dt_constructors,
            __eo_dt_constructors_main] using
              (EoCtorAt.head : EoCtorAt
                (eoCons (Term.UOp UserOp.tuple) Term.__eo_List_nil) 0
                (Term.UOp UserOp.tuple))
        obtain ⟨g, crel, hgTy, hgTrue⟩ :=
          splitRel_pick_true M srel (by exact hAt) hGTy hRHS
        have hEnc : gEnc g = __eo_to_smt g :=
          gEnc_eq_eo_to_smt_of_bool hgTy
        have hgEncTy : __smtx_typeof (gEnc g) = SmtType.Bool := by
          rw [hEnc]
          exact hgTy
        have hgEncTrue : __smtx_model_eval M (gEnc g) =
            SmtValue.Boolean true := by
          rw [hEnc]
          exact hgTrue
        have hTcs : TCS (conjFinal crel) :=
          conj_final_tcs sx
            (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂)
            F crel TCS.head hgEncTy
        obtain ⟨s₁, U₁, s₂, U₂, hFull, hU₁Wf, hU₂Wf⟩ :=
          tcs_full hTcs (conjFinal_typeof crel) hWfX
        have hFinalType := conjFinal_typeof crel
        rw [hFull] at hFinalType
        change __eo_typeof_tuple U₁ U₂ =
          Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂ at hFinalType
        have hFinalTypeWf :
            __smtx_type_wf (__eo_to_smt_type (__eo_typeof_tuple U₁ U₂)) =
              true := by
          rw [hFinalType]
          exact hWfX
        have hFinalTuple := qds_typeof_tuple_eq_of_wf U₁ U₂ hFinalTypeWf
        have hApplied :
            Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) U₁) U₂ =
              Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂ :=
          hFinalTuple.symm.trans hFinalType
        injection hApplied with hLeft hU₂
        injection hLeft with hHead hU₁
        subst U₁
        subst U₂
        have hAbs : conjAbsorbed crel =
            [Term.Var (Term.String s₁) T₁,
              Term.Var (Term.String s₂) T₂] := by
          have hArgs := congrArg eoTermArgs (conjFinal_eq_spine crel)
          rw [hFull] at hArgs
          simpa [eoTermArgs, eoTermArgs_eoTermSpine] using hArgs.symm
        obtain ⟨c, hTailShape, hFullShape⟩ :=
          qds_tuple_type_shape_of_wf T₁ T₂ hWfX
        let A := __eo_to_smt_type T₁
        let tailD := SmtDatatype.sum c SmtDatatype.null
        let tailDD := __eo_to_smt_tuple_decl tailD
        let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
        let fullDD := __eo_to_smt_tuple_decl fullD
        have hLookupFull :
            __smtx_dd_lookup (native_string_lit "@Tuple") fullDD = fullD := by
          simp [fullDD, fullD, __eo_to_smt_tuple_decl,
            __smtx_dd_lookup, native_streq, native_ite]
        have hLookupTail :
            __smtx_dd_lookup (native_string_lit "@Tuple") tailDD = tailD := by
          simp [tailDD, tailD, __eo_to_smt_tuple_decl,
            __smtx_dd_lookup, native_streq, native_ite]
        have hResolveFull :
            __smtx_dt_resolve fullD fullDD = fullD := by
          simpa [fullD, fullDD, A] using
            qds_tuple_resolve_noop_of_eo_type
              (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂)
              (SmtDatatypeCons.cons A c) hFullShape hWfX
        have hResolveTail :
            __smtx_dt_resolve tailD tailDD = tailD := by
          simpa [tailD, tailDD] using
            qds_tuple_resolve_noop_of_eo_type T₂ c hTailShape hU₂Wf
        have hwTyFull : __smtx_typeof_value w =
            SmtType.Datatype (native_string_lit "@Tuple") fullDD := by
          exact hwTy.trans (by simpa [fullD, fullDD, A] using hFullShape)
        obtain ⟨ci, args, hW, hCiLt, hArgLen, hArgTypes⟩ :=
          datatype_value_spine hwTyFull
        have hCi : ci = 0 := by
          rw [hLookupFull] at hCiLt
          simpa [fullD, smtDatatypeNumCtors] using hCiLt
        subst ci
        rw [hLookupFull, hResolveFull] at hArgLen hArgTypes
        cases args with
        | nil =>
            simp [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels] at hArgLen
        | cons u rest =>
            have hRestLen : rest.length = __smtx_dtc_num_sels c := by
              simpa [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels] using hArgLen
            have huTy : __smtx_typeof_value u = A := by
              have h := hArgTypes 0 (by simp)
              simpa [fullD, A, __smtx_ret_typeof_sel_rec] using h
            have hRestTypes : ∀ j, j < rest.length ->
                __smtx_typeof_value rest[j]! =
                  __smtx_ret_typeof_sel_rec tailD 0 j := by
              intro j hj
              have h := hArgTypes (Nat.succ j) (by simpa using Nat.succ_lt_succ hj)
              simpa [fullD, tailD, __smtx_ret_typeof_sel_rec] using h
            have hArgsView : vsmArgs w = u :: rest := by
              rw [hW, vsmArgs_vsmMkSpine]
              rfl
            obtain ⟨hRootCanon, hArgsCanon⟩ := vsm_canonical_spine w hwCanon
            have huCanon : __smtx_value_canonical u = true :=
              hArgsCanon u (by rw [hArgsView]; simp)
            have hRestCanon : ∀ a ∈ rest,
                __smtx_value_canonical a = true := by
              intro a ha
              exact hArgsCanon a (by rw [hArgsView]; simp [ha])
            let tailRoot := SmtValue.DtCons
              (native_string_lit "@Tuple") tailDD native_nat_zero
            let tailVal := vsmMkSpine tailRoot rest
            have hTailRootTy : __smtx_typeof_value tailRoot =
              dt_cons_applied_type_rec (native_string_lit "@Tuple")
                  tailDD tailD native_nat_zero 0 := by
              simp [tailRoot, __smtx_typeof_value, dt_cons_applied_type_rec,
                hLookupTail, hResolveTail]
            have hRetWf : ∀ j, j < __smtx_dt_num_sels tailD 0 ->
                __smtx_type_wf
                  (__smtx_ret_typeof_sel_rec tailD 0 j) = true := by
              intro j hj
              have h := qds_tuple_ret_type_wf_of_eo_type
                T₂ c j hTailShape hU₂Wf
                (by simpa [tailD, __smtx_dt_num_sels] using hj)
              rwa [hResolveTail] at h
            have hTailValTyRaw := vsmMkSpine_dtcons_type
              (native_string_lit "@Tuple") tailDD tailD native_nat_zero rest
                hTailRootTy (by simp [tailD, __smtx_dt_num_sels, hRestLen])
                hRetWf hRestTypes
            have hTailValTy : __smtx_typeof_value tailVal =
                SmtType.Datatype (native_string_lit "@Tuple") tailDD := by
              rw [show tailVal = vsmMkSpine tailRoot rest from rfl,
                hTailValTyRaw, hRestLen,
                qds_dtc_full_arity (native_string_lit "@Tuple") tailDD c]
            have hTailValCanon : __smtx_value_canonical tailVal = true := by
              apply vsm_canonical_of_spine rest tailRoot
              · rfl
              · exact hRestCanon
            have hSourceNe := tuple_absorbed_two_ne_of_typed crel hgEncTy
              s₁ s₂ T₁ T₂ hAbs
            have hT₁Valid : TranslationProofs.eo_type_valid_rec [] T₁ := by
              simpa [TranslationProofs.eo_type_valid,
                TranslationProofs.eo_type_valid_rec] using
                  TranslationProofs.eo_type_valid_of_smt_wf T₁ hU₁Wf
            have hKeyNe :
                ({ isVar := true, name := s₁, ty := A } : SmtModelKey) ≠
                  { isVar := true, name := s₂, ty := __eo_to_smt_type T₂ } := by
              intro hKey
              have hs : s₁ = s₂ := congrArg SmtModelKey.name hKey
              have hATy : A = __eo_to_smt_type T₂ :=
                congrArg SmtModelKey.ty hKey
              have hT : T₁ = T₂ :=
                TranslationProofs.eo_to_smt_type_eq_of_valid hT₁Valid
                  (by simpa [A] using hATy)
              apply hSourceNe
              rw [hs, hT]
            have hHeadTermTy : __smtx_typeof
                (__eo_to_smt (Term.Var (Term.String s₁) T₁)) = A := by
              rw [TranslationProofs.eo_to_smt_var, smtx_typeof_var_term_eq]
              simp [__smtx_typeof_guard_wf, hU₁Wf, A, native_ite]
            have hTailTupleWf : __smtx_type_wf
                (SmtType.Datatype (native_string_lit "@Tuple") tailDD) = true := by
              exact (congrArg __smtx_type_wf hTailShape).symm.trans
                (by simpa [tailD, tailDD] using hU₂Wf)
            have hTailTermTy : __smtx_typeof
                (__eo_to_smt (Term.Var (Term.String s₂) T₂)) =
                  SmtType.Datatype (native_string_lit "@Tuple") tailDD := by
              rw [TranslationProofs.eo_to_smt_var, smtx_typeof_var_term_eq]
              simp [__smtx_typeof_guard_wf, hTailShape, hTailTupleWf,
                tailD, tailDD, native_ite]
            have hFullTrans : RuleProofs.eo_has_smt_translation
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.tuple)
                    (Term.Var (Term.String s₁) T₁))
                  (Term.Var (Term.String s₂) T₂)) := by
              apply ctor_spine_translation
                (CS.apply (CS.apply (CS.head CH.tuple) hU₁Wf) hU₂Wf)
              · exact hFinalType
              · exact hWfX
            have hPrependNN : __smtx_typeof
                (__eo_to_smt_tuple_prepend
                  (__eo_to_smt (Term.Var (Term.String s₁) T₁)) A
                  (__eo_to_smt (Term.Var (Term.String s₂) T₂))) ≠
                SmtType.None := by
              unfold RuleProofs.eo_has_smt_translation at hFullTrans
              change __smtx_typeof
                (__eo_to_smt_tuple_prepend
                  (__eo_to_smt (Term.Var (Term.String s₁) T₁))
                  (__smtx_typeof
                    (__eo_to_smt (Term.Var (Term.String s₁) T₁)))
                  (__eo_to_smt (Term.Var (Term.String s₂) T₂))) ≠
                    SmtType.None at hFullTrans
              rw [hHeadTermTy] at hFullTrans
              exact hFullTrans
            have hTailValTyEo : __smtx_typeof_value tailVal =
                __eo_to_smt_type T₂ := by
              rw [hTailShape]
              simpa [tailD, tailDD] using hTailValTy
            let P := native_model_push
              (native_model_push N₀ s₁ A u)
              s₂ (__eo_to_smt_type T₂) tailVal
            have hN₀Typed : model_wf N₀ := hN₀.total_typed hM
            have hP₁Typed : model_wf
                (native_model_push N₀ s₁ A u) :=
              model_total_typed_push hN₀Typed s₁ A u
                (by simpa [A] using hU₁Wf) huTy
                (by simpa [value_canonical] using huCanon)
            have hPTyped : model_wf P :=
              model_total_typed_push hP₁Typed s₂ (__eo_to_smt_type T₂)
                tailVal hU₂Wf hTailValTyEo
                (by simpa [value_canonical] using hTailValCanon)
            have hEvalHead : __smtx_model_eval P
                (__eo_to_smt (Term.Var (Term.String s₁) T₁)) = u := by
              change native_model_var_lookup P s₁ A = u
              simp [P, native_model_var_lookup, native_model_push, hKeyNe]
            have hEvalTail : __smtx_model_eval P
                (__eo_to_smt (Term.Var (Term.String s₂) T₂)) = tailVal := by
              change native_model_var_lookup P s₂ (__eo_to_smt_type T₂) = tailVal
              simp [P, native_model_var_lookup, native_model_push]
            have hTupleEval := tuple_prepend_eval_eq_value_rec P hPTyped
              (__eo_to_smt (Term.Var (Term.String s₁) T₁))
              (__eo_to_smt (Term.Var (Term.String s₂) T₂))
              A c hHeadTermTy
                (by simpa [tailD, tailDD] using hTailTermTy) hPrependNN
            rw [hEvalHead, hEvalTail] at hTupleEval
            have hRestLenTail : rest.length =
                __smtx_dt_num_sels tailD native_nat_zero := by
              simpa [tailD, __smtx_dt_num_sels] using hRestLen
            have hRec := tuplePrependValueRec_vsmMkSpine tailD tailRoot rest
              (SmtValue.Apply
                (SmtValue.DtCons (native_string_lit "@Tuple") fullDD native_nat_zero)
                u)
              (by rfl) hRestLenTail
            have hEvalFinal : __smtx_model_eval P
                (__eo_to_smt (conjFinal crel)) = w := by
              rw [hFull]
              change __smtx_model_eval P
                (__eo_to_smt_tuple_prepend
                  (__eo_to_smt (Term.Var (Term.String s₁) T₁))
                  (__smtx_typeof
                    (__eo_to_smt (Term.Var (Term.String s₁) T₁)))
                  (__eo_to_smt (Term.Var (Term.String s₂) T₂))) = w
              rw [hHeadTermTy]
              calc
                __smtx_model_eval P
                    (__eo_to_smt_tuple_prepend
                      (__eo_to_smt (Term.Var (Term.String s₁) T₁)) A
                      (__eo_to_smt (Term.Var (Term.String s₂) T₂))) =
                    tuplePrependValueRec tailD tailVal
                      (__smtx_dt_num_sels tailD native_nat_zero)
                      (SmtValue.Apply
                        (SmtValue.DtCons (native_string_lit "@Tuple") fullDD
                          native_nat_zero) u) := by
                            simpa [tailD, tailDD, fullD, fullDD] using hTupleEval
                _ = vsmMkSpine
                    (SmtValue.Apply
                      (SmtValue.DtCons (native_string_lit "@Tuple") fullDD
                          native_nat_zero) u) rest := by
                            exact hRec
                _ = w := by simpa [vsmMkSpine] using hW.symm
            have hCI := ctorInst_of_two_absorbed crel N₀ w
              s₁ T₁ u s₂ T₂ tailVal hAbs
              (by simpa [A] using huTy) huCanon hTailValTyEo hTailValCanon hEvalFinal
            have hBody := conj_backward_aux sx
              (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T₁) T₂)
              F hWfX hFTrans crel (CS.head CH.tuple) M hM
              hgEncTy hgEncTrue N₀ hN₀ w hCI
            rw [hN]
            exact hBody
      case neg.case3 =>
        have hAt : EoCtorAt
            (__dt_get_constructors (Term.UOp UserOp.UnitTuple)) 0
            (Term.UOp UserOp.tuple_unit) := by
          simpa [__dt_get_constructors, __eo_dt_constructors,
            __eo_dt_constructors_main] using
              (EoCtorAt.head : EoCtorAt
                (eoCons (Term.UOp UserOp.tuple_unit) Term.__eo_List_nil) 0
                (Term.UOp UserOp.tuple_unit))
        obtain ⟨g, crel, hgTy, hgTrue⟩ :=
          splitRel_pick_true M srel (by exact hAt) hGTy hRHS
        have hEnc : gEnc g = __eo_to_smt g :=
          gEnc_eq_eo_to_smt_of_bool hgTy
        have hgEncTy : __smtx_typeof (gEnc g) = SmtType.Bool := by
          rw [hEnc]
          exact hgTy
        have hgEncTrue : __smtx_model_eval M (gEnc g) =
            SmtValue.Boolean true := by
          rw [hEnc]
          exact hgTrue
        have hUcs : UCS (conjFinal crel) :=
          conj_final_ucs sx (Term.UOp UserOp.UnitTuple) F crel UCS.head hgEncTy
        have hFull : conjFinal crel = Term.UOp UserOp.tuple_unit :=
          ucs_full hUcs (conjFinal_typeof crel) hWfX
        have hAbs : conjAbsorbed crel = [] := by
          apply eoTermSpine_eq_head_implies_nil
          rw [← conjFinal_eq_spine crel, hFull]
        let unitD :=
          SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null
        let unitDD := __eo_to_smt_tuple_decl unitD
        have hwTyUnit : __smtx_typeof_value w =
            SmtType.Datatype (native_string_lit "@Tuple") unitDD := by
          simpa [unitDD, unitD, __eo_to_smt_tuple_decl,
            TranslationProofs.eo_to_smt_type_unit_tuple] using hwTy
        obtain ⟨ci, args, hW, hCiLt, hArgLen, hArgTypes⟩ :=
          datatype_value_spine hwTyUnit
        have hCi : ci = 0 := by
          simpa [unitDD, unitD, __eo_to_smt_tuple_decl,
            __smtx_dd_lookup, smtDatatypeNumCtors, native_streq,
            native_ite] using hCiLt
        subst ci
        have hArgs : args = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [unitDD, unitD, __eo_to_smt_tuple_decl,
            __smtx_dd_lookup, __smtx_dt_resolve, __smtx_dtc_resolve,
            __smtx_dt_num_sels, __smtx_dtc_num_sels, native_streq,
            native_ite] using hArgLen
        subst args
        have hEval : __smtx_model_eval N₀
            (__eo_to_smt (conjFinal crel)) = w := by
          rw [hFull, TranslationProofs.eo_to_smt_term_tuple_unit]
          simpa [__smtx_model_eval, vsmMkSpine, unitDD, unitD,
            __eo_to_smt_tuple_decl] using hW.symm
        have hCI := ctorInst_of_no_absorbed crel N₀ w hAbs hEval
        have hBody := conj_backward_aux sx (Term.UOp UserOp.UnitTuple) F hWfX
          hFTrans crel (CS.head CH.tupleUnit) M hM hgEncTy hgEncTrue
          N₀ hN₀ w hCI
        rw [hN]
        exact hBody
      case neg.case4 =>
        exact False.elim (impossible _
          (dt_get_constructors_apply_stuck_of_wf_not_tuple _ _
            (by assumption) hWfX) srel)
      case neg.case5 =>
        exact False.elim (impossible _ (by
          simp_all [__dt_get_constructors, __eo_dt_constructors,
            __eo_dt_constructors_main]) srel)

/-! ## Assembly -/

theorem eo_to_smt_qds_eq (x ys F G : Term) :
    __eo_to_smt (qdsFormula x ys F G) =
      SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G) := by
  rfl

/--
Truth of the concluded equality, from a successful guard run.  This is the
target consumed by `Cpc/Proofs/Rules/Quant_dt_split.lean`.
-/
theorem qds_formula_true
    (M : SmtModel) (hM : model_wf M)
    (x ys F G : Term)
    (hGuard : __is_quant_dt_split x (__dt_get_constructors (__eo_typeof x)) ys F G =
      Term.Boolean true)
    (hTrans : RuleProofs.eo_has_smt_translation (qdsFormula x ys F G))
    (hTy : __eo_typeof (qdsFormula x ys F G) = Term.Bool) :
    eo_interprets M (qdsFormula x ys F G) true := by
  obtain ⟨srel⟩ := splitRel_of_guard_true x ys F _ G hGuard
  -- SMT-side typing of the equality
  have hSmtBool : RuleProofs.eo_has_bool_type (qdsFormula x ys F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTrans hTy
  rw [RuleProofs.eo_has_bool_type] at hSmtBool
  rw [eo_to_smt_qds_eq] at hSmtBool
  -- both sides evaluate to Booleans
  have hLTy : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) = SmtType.Bool := by
    have hNe : __smtx_typeof (__eo_to_smt (mkForall (eoCons x ys) F)) ≠ SmtType.None :=
      smtx_typeof_eq_bool_left_ne_none hSmtBool
    have hForm : __eo_to_smt (mkForall (eoCons x ys) F) =
        SmtTerm.not (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) :=
      SubstituteTranslatabilitySupport.eo_to_smt_forall_eq_of_non_nil (eoCons x ys) F (by intro h; cases h)
    rw [hForm] at hNe ⊢
    rcases smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists (eoCons x ys) (SmtTerm.not (__eo_to_smt F))) with hB | hN
    · exact hB
    · exact absurd hN hNe
  have hRTy : __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
    rw [← smtx_typeof_eq_bool_elim hSmtBool]
    exact hLTy
  obtain ⟨bL, hbL⟩ :=
    smt_model_eval_bool_is_boolean M hM _ hLTy
  obtain ⟨bR, hbR⟩ :=
    smt_model_eval_bool_is_boolean M hM _ hRTy
  -- the two sides agree
  have hAgree : bL = bR := by
    cases bL
    · cases bR
      · rfl
      · exfalso
        have := split_backward M hM x ys F G srel hTrans hTy hbR
        rw [hbL] at this
        exact absurd this (by decide)
    · cases bR
      · exfalso
        have := split_forward M hM x ys F G srel hTrans hTy hbL
        rw [hbR] at this
        exact absurd this (by decide)
      · rfl
  -- conclude the equality evaluates to true
  rw [eo_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · rw [eo_to_smt_qds_eq]; exact hSmtBool
  · rw [eo_to_smt_qds_eq]
    rw [show __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt (mkForall (eoCons x ys) F)) (__eo_to_smt G)) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (mkForall (eoCons x ys) F)))
        (__smtx_model_eval M (__eo_to_smt G)) from by
        simp only [__smtx_model_eval]]
    rw [hbL, hbR, hAgree]
    simp [__smtx_model_eval_eq, native_veq]

end QuantDtSplitRule
