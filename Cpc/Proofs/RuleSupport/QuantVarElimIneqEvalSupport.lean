module

public import Cpc.Proofs.RuleSupport.QuantVarElimIneqSupport
import all Cpc.Proofs.RuleSupport.QuantVarElimIneqSupport
public import Cpc.Proofs.RuleSupport.ArithPolyNormSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormSupport
public import Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

public section

/-!
Semantic interpretation of accepted arithmetic literals. A polynomial whose
remaining monomials are free of the eliminated variable has a fixed offset
under assignments to that variable. Every accepted literal is eventually false
in its permitted direction, for both integer and real variables.
-/

open Eo SmtEval Smtm

set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

namespace QuantVarElimIneq

abbrev qvar (s : native_String) (T : Term) : Term := Term.Var (Term.String s) T

private theorem single_env (s : native_String) (T : Term) :
    EoVarEnvPerm (single (qvar s T)) [(s, T)] :=
  EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil)

private theorem nil_env : EoVarEnvPerm Term.__eo_List_nil [] :=
  EoVarEnvPerm.of_exact EoVarEnv.nil

abbrev Agree (s : native_String) (T : Term) (N M : SmtModel) : Prop :=
  model_agrees_except_on_env [(s, __eo_to_smt_type T)] [] N M

theorem free_eval {M N : SmtModel} {s : native_String} {T a : Term}
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hf : __contains_atomic_term_list_free_rec a (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false) (hAgree : Agree s T N M) :
    arith_poly_norm_atom_denote_real N a = arith_poly_norm_atom_denote_real M a := by
  unfold arith_poly_norm_atom_denote_real
  congr 1
  exact smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (single_env s T) nil_env hTrans hf hAgree

private theorem free_cons {s : native_String} {T a p : Term}
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hf : __contains_atomic_term_list_free_rec
      ((Term.__eo_List_cons.Apply a).Apply p) (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false) :
    __contains_atomic_term_list_free_rec a (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec p (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false := by
  have hNotList : ∀ q x ys : Term, Term.__eo_List_cons.Apply a ≠
      q.Apply ((Term.__eo_List_cons.Apply x).Apply ys) := by
    intro q x ys he
    have ha := (Term.Apply.inj he).2
    exact term_not_eo_list_cons_of_has_smt_translation hTrans x ys ha
  obtain ⟨hhead, htail⟩ := contains_atomic_term_list_free_rec_apply_false_cases
    (single_env s T) nil_env hNotList hf
  have hNotList' : ∀ q x ys : Term, Term.__eo_List_cons ≠
      q.Apply ((Term.__eo_List_cons.Apply x).Apply ys) := by
    intros q x ys he; cases he
  exact ⟨(contains_atomic_term_list_free_rec_apply_false_cases
    (single_env s T) nil_env hNotList' hhead).2, htail⟩

theorem free_mvar_eval {M N : SmtModel} {s : native_String} {T a : Term}
    (ha : arith_mvar_rational M a)
    (hf : __contains_atomic_term_list_free_rec a (single (qvar s T)) Term.__eo_List_nil =
      Term.Boolean false) (hAgree : Agree s T N M) :
    arith_mvar_denote_real N a = arith_mvar_denote_real M a := by
  induction ha with
  | nil => rfl
  | cons a p ha hp ih =>
      obtain ⟨hfa, hfp⟩ := free_cons ha.1 hf
      simp only [arith_mvar_denote_real, free_eval ha.1 hfa hAgree, ih hfp]

theorem free_poly_eval {M N : SmtModel} {s : native_String} {T p : Term}
    (hp : arith_poly_rational M p)
    (hf : __poly_contains_atomic_term_free p (qvar s T) = Term.Boolean false)
    (hAgree : Agree s T N M) :
    arith_poly_denote_real N p = arith_poly_denote_real M p := by
  induction hp with
  | zero => rfl
  | cons m p hm hp ih =>
      cases hm with
      | mk a c ha =>
          rw [__poly_contains_atomic_term_free.eq_def] at hf
          obtain ⟨hfa, hfp⟩ := eo_ite_true_eq_false_cases hf
          simp only [arith_poly_denote_real, arith_mon_denote_real,
            free_mvar_eval ha hfa hAgree, ih hfp]

/-- An accepted direction really is an affine function of the eliminated
variable, with the same nonzero coefficient in every agreeing model. -/
theorem linear_eval {M : SmtModel} {s : native_String} {T p : Term} {c : Rat}
    (hp : arith_poly_rational M p) (hl : LinearPart (qvar s T) p c) :
    ∃ b : Rat, ∀ (N : SmtModel) (q : Rat), Agree s T N M →
      arith_poly_norm_atom_denote_real N (qvar s T) = SmtValue.Rational q →
      arith_poly_denote_real N p = SmtValue.Rational (c * q + b) := by
  induction hl with
  | head c p hfree =>
      cases hp with
      | cons _ _ hm hp =>
          obtain ⟨b, hb⟩ := arith_poly_denote_real_rational_of_rational_support M hp
          refine ⟨b, ?_⟩
          intro N q hAgree hq
          have ht := (free_poly_eval hp hfree hAgree).trans hb
          simp [poly, mon, single, arith_poly_denote_real, arith_mon_denote_real,
            arith_mvar_denote_real, hq, ht, __smtx_model_eval_mult,
            __smtx_model_eval_plus, native_qmult, native_qplus, ratOne, Rat.mul_one]
  | skip a d p c hfree hl ih =>
      cases hp with
      | cons _ _ hm hp =>
          cases hm with
          | mk _ _ ha =>
              obtain ⟨b, hb⟩ := ih hp
              obtain ⟨r, hr⟩ := arith_mvar_denote_real_rational_of_rational_support M ha
              refine ⟨d * r + b, ?_⟩
              intro N q hAgree hq
              have hvars := (free_mvar_eval ha hfree hAgree).trans hr
              simp only [poly, mon, arith_poly_denote_real, arith_mon_denote_real,
                hvars, hb N q hAgree hq, __smtx_model_eval_mult, __smtx_model_eval_plus,
                native_qmult, native_qplus]
              congr 1
              exact Rat.add_left_comm _ _ _

def ArithType (T : Term) : Prop := T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real

def arithValue (T : Term) (n : Int) : SmtValue :=
  if T = Term.UOp UserOp.Int then SmtValue.Numeral n else SmtValue.Rational (n : Rat)

abbrev push (M : SmtModel) (s : native_String) (T : Term) (n : Int) : SmtModel :=
  native_model_push M s (__eo_to_smt_type T) (arithValue T n)

theorem arithValue_facts {T : Term} (hT : ArithType T) (n : Int) :
    __smtx_type_wf (__eo_to_smt_type T) = true ∧
      __smtx_typeof_value (arithValue T n) = __eo_to_smt_type T ∧
      __smtx_value_canonical (arithValue T n) = true := by
  rcases hT with rfl | rfl <;>
    simp [arithValue, __eo_to_smt_type, __smtx_typeof_value, __smtx_value_canonical,
      __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec, native_inhabited_type, __smtx_type_default,
      native_Teq, native_not, native_and]

theorem push_wf {M : SmtModel} (hM : model_wf M) (s : native_String) {T : Term}
    (hT : ArithType T) (n : Int) : model_wf (push M s T n) := by
  obtain ⟨hWf, hTy, hCanon⟩ := arithValue_facts hT n
  exact model_total_typed_push hM s (__eo_to_smt_type T) (arithValue T n) hWf hTy hCanon

theorem push_agree (M : SmtModel) (s : native_String) (T : Term) (n : Int) :
    Agree s T (push M s T n) M :=
  model_agrees_except_on_env_push_left_of_mem_except (by simp) (by simp)

theorem push_variable (M : SmtModel) (s : native_String) {T : Term}
    (hT : ArithType T) (n : Int) :
    arith_poly_norm_atom_denote_real (push M s T n) (qvar s T) =
      SmtValue.Rational (n : Rat) := by
  have hn : native_to_real n = (n : Rat) := by
    simpa [native_to_real, native_mk_rational] using (rat_div_one_intCast n)
  rcases hT with rfl | rfl <;>
    simp [arith_poly_norm_atom_denote_real, qvar, __eo_to_smt,
      __eo_to_smt_type, __smtx_model_eval, native_model_var_lookup, push,
      native_model_push, arithValue, __smtx_to_real_coerce, hn]

def Eventually (P : Int → Prop) : Prop := ∃ B : Int, ∀ n : Int, B ≤ n → P n

theorem Eventually.and {P Q : Int → Prop} (hp : Eventually P) (hq : Eventually Q) :
    Eventually (fun n => P n ∧ Q n) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  refine ⟨max a b, fun n hn => ⟨ha n ?_, hb n ?_⟩⟩ <;> omega

def Escapes (M : SmtModel) (s : native_String) (T : Term) (sign : Int) (f : Term) : Prop :=
  Eventually (fun n => __smtx_model_eval (push M s T (sign * n)) (__eo_to_smt f) =
    SmtValue.Boolean false)

abbrev diff (a b : Term) : Term := ((Term.UOp UserOp.neg).Apply a).Apply b

theorem diff_affine (M : SmtModel) (hM : model_wf M) (s : native_String) {T : Term}
    (hT : ArithType T) (a b : Term)
    (hDiffTy : __smtx_typeof (__eo_to_smt (diff a b)) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (diff a b)) = SmtType.Real)
    (d : Int)
    (hd : __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) = Term.Numeral d) :
    ∃ c k : Rat, c ≠ 0 ∧ d = (if c < 0 then -1 else 1) ∧
      ∀ n : Int, arith_atom_denote_real (push M s T n) (diff a b) =
        SmtValue.Rational (c * (n : Rat) + k) := by
  obtain ⟨c, hc, hl, hd⟩ := linear_dir_nonzero (by simp [qvar])
    (nonzeroCoeffs_norm (diff a b)) d hd
  have hp := (arith_poly_norm_facts_of_smt_arith_type M hM (diff a b) hDiffTy).1
  obtain ⟨k, hk⟩ := linear_eval hp hl
  refine ⟨c, k, hc, hd, ?_⟩
  intro n
  have he := hk (push M s T n) (n : Rat) (push_agree M s T n) (push_variable M s hT n)
  rw [arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
    (push M s T n) (push_wf hM s hT n) (diff a b) hDiffTy] at he
  exact he

abbrev binary (op : UserOp) (a b : Term) : Term := ((Term.UOp op).Apply a).Apply b
abbrev qnot (f : Term) : Term := (Term.UOp UserOp.not).Apply f

inductive UpperLiteral (a b : Term) : Term → Prop where
  | lt : UpperLiteral a b (binary UserOp.lt a b)
  | le : UpperLiteral a b (binary UserOp.leq a b)
  | gt : UpperLiteral a b (binary UserOp.gt b a)
  | ge : UpperLiteral a b (binary UserOp.geq b a)
  | not_gt : UpperLiteral a b (qnot (binary UserOp.gt a b))
  | not_ge : UpperLiteral a b (qnot (binary UserOp.geq a b))
  | not_lt : UpperLiteral a b (qnot (binary UserOp.lt b a))
  | not_le : UpperLiteral a b (qnot (binary UserOp.leq b a))

abbrev DiffType (a b : Term) : Prop :=
  __smtx_typeof (__eo_to_smt (diff a b)) = SmtType.Int ∨
    __smtx_typeof (__eo_to_smt (diff a b)) = SmtType.Real

private theorem swapped_gt (M : SmtModel) (a b : Term) :
    __smtx_model_eval M (__eo_to_smt (binary UserOp.gt b a)) =
      __smtx_model_eval M (__eo_to_smt (binary UserOp.lt a b)) := by
  change __smtx_model_eval M (SmtTerm.gt (__eo_to_smt b) (__eo_to_smt a)) =
    __smtx_model_eval M (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b))
  conv => lhs; rw [__smtx_model_eval.eq_def]
  conv => rhs; rw [__smtx_model_eval.eq_def]
  rfl

private theorem swapped_ge (M : SmtModel) (a b : Term) :
    __smtx_model_eval M (__eo_to_smt (binary UserOp.geq b a)) =
      __smtx_model_eval M (__eo_to_smt (binary UserOp.leq a b)) := by
  change __smtx_model_eval M (SmtTerm.geq (__eo_to_smt b) (__eo_to_smt a)) =
    __smtx_model_eval M (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b))
  conv => lhs; rw [__smtx_model_eval.eq_def]
  conv => rhs; rw [__smtx_model_eval.eq_def]
  rfl

private theorem eval_not (M : SmtModel) (f : Term) :
    __smtx_model_eval M (__eo_to_smt (qnot f)) =
      __smtx_model_eval_not (__smtx_model_eval M (__eo_to_smt f)) := by
  change __smtx_model_eval M (SmtTerm.not (__eo_to_smt f)) = _
  rw [__smtx_model_eval.eq_def]

theorem upper_false (M : SmtModel) (hM : model_wf M) {a b f : Term}
    (hTy : DiffType a b) (hf : UpperLiteral a b f) {q : Rat}
    (hv : arith_atom_denote_real M (diff a b) = SmtValue.Rational q) (hq : 0 < q) :
    __smtx_model_eval M (__eo_to_smt f) = SmtValue.Boolean false := by
  obtain ⟨r, hr, hlt, hle, heq, hgt, hge⟩ := arith_rel_eval_bools_of_diff_type M hM a b hTy
  have hrq : r = q := by rw [hv] at hr; exact (SmtValue.Rational.inj hr).symm
  subst r
  have hq0 : 0 ≤ q := Rat.le_of_lt hq
  have hnlt : ¬q < 0 := Rat.not_lt.mpr hq0
  have hnle : ¬q ≤ 0 := Rat.not_le.mpr hq
  simp only [ratZero, native_qlt, native_qleq, decide_eq_false hnlt,
    decide_eq_false hnle, decide_eq_true hq, decide_eq_true hq0] at hlt hle hgt hge
  cases hf with
  | lt => exact hlt
  | le => exact hle
  | gt => exact (swapped_gt M a b).trans hlt
  | ge => exact (swapped_ge M a b).trans hle
  | not_gt => rw [eval_not, hgt]; rfl
  | not_ge => rw [eval_not, hge]; rfl
  | not_lt => rw [eval_not, ← swapped_gt M b a, hgt]; rfl
  | not_le => rw [eval_not, ← swapped_ge M b a, hge]; rfl

theorem equality_false (M : SmtModel) (hM : model_wf M) {a b : Term}
    (hTy : DiffType a b) {q : Rat}
    (hv : arith_atom_denote_real M (diff a b) = SmtValue.Rational q) (hq : q ≠ 0) :
    __smtx_model_eval M (__eo_to_smt (binary UserOp.eq a b)) = SmtValue.Boolean false := by
  obtain ⟨r, hr, _, _, heq, _, _⟩ := arith_rel_eval_bools_of_diff_type M hM a b hTy
  have hrq : r = q := by rw [hv] at hr; exact (SmtValue.Rational.inj hr).symm
  subst r
  simpa [ratZero, native_qeq, hq] using heq

theorem upper_escapes (M : SmtModel) (hM : model_wf M) (s : native_String) {T : Term}
    (hT : ArithType T) {a b f : Term} (hTy : DiffType a b) (hf : UpperLiteral a b f)
    {d sign : Int} (hs : sign = -1 ∨ sign = 1) (hcompat : d * sign ≠ -1)
    (hd : __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) = Term.Numeral d) :
    Escapes M s T sign f := by
  obtain ⟨c, k, hc, hd, hval⟩ := diff_affine M hM s hT a b hTy d hd
  obtain ⟨B, hB⟩ := affine_eventually_pos (c * (sign : Rat)) k (compatible_slope hc hd hs hcompat)
  refine ⟨B, ?_⟩
  intro n hn
  have hv := hval (sign * n)
  rw [Rat.intCast_mul, ← Rat.mul_assoc] at hv
  exact upper_false _ (push_wf hM s hT _) hTy hf hv (hB n hn)

theorem equality_escapes (M : SmtModel) (hM : model_wf M) (s : native_String) {T : Term}
    (hT : ArithType T) {a b : Term} (hTy : DiffType a b) {sign : Int}
    (hs : sign = -1 ∨ sign = 1)
    (hd : __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) ≠ Term.Stuck) :
    Escapes M s T sign (binary UserOp.eq a b) := by
  have hdir : ∃ d : Int,
      __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) = Term.Numeral d := by
    rcases linear_dir_range (qvar s T) (__get_arith_poly_norm (diff a b)) with h | h | h
    · exact False.elim (hd h)
    · exact ⟨-1, h⟩
    · exact ⟨1, h⟩
  obtain ⟨d, hdir⟩ := hdir
  obtain ⟨c, k, hc, _, hval⟩ := diff_affine M hM s hT a b hTy d hdir
  have hslope : c * (sign : Rat) ≠ 0 := by
    intro heq
    rcases Rat.mul_eq_zero.mp heq with hc0 | hs0
    · exact hc hc0
    · rcases hs with rfl | rfl <;> contradiction
  obtain ⟨B, hB⟩ := affine_eventually_ne (c * (sign : Rat)) k hslope
  refine ⟨B, ?_⟩
  intro n hn
  have hv := hval (sign * n)
  rw [Rat.intCast_mul, ← Rat.mul_assoc] at hv
  exact equality_false _ (push_wf hM s hT _) hTy hv (hB n hn)

private abbrev SameArith (a b : Term) : Prop :=
  (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧ __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧ __smtx_typeof (__eo_to_smt b) = SmtType.Real)

private theorem sameArith_swap {a b : Term} (h : SameArith a b) : SameArith b a :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

private theorem diff_type_of_args {a b : Term} (h : SameArith a b) : DiffType a b := by
  change __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) = SmtType.Int ∨
    __smtx_typeof (SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b)) = SmtType.Real
  rw [typeof_neg_eq]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp [__smtx_typeof_arith_overload_op_2, ha, hb]

theorem UpperLiteral.diff_type {a b f : Term} (hf : UpperLiteral a b f)
    (hBool : RuleProofs.eo_has_bool_type f) : DiffType a b := by
  apply diff_type_of_args
  cases hf with
  | lt => exact rel_operands_arith_type_of_lt_has_bool_type a b hBool
  | le => exact rel_operands_arith_type_of_leq_has_bool_type a b hBool
  | gt => exact sameArith_swap (rel_operands_arith_type_of_gt_has_bool_type b a hBool)
  | ge => exact sameArith_swap (rel_operands_arith_type_of_geq_has_bool_type b a hBool)
  | not_gt =>
      exact rel_operands_arith_type_of_gt_has_bool_type a b
        (RuleProofs.eo_has_bool_type_not_arg _ hBool)
  | not_ge =>
      exact rel_operands_arith_type_of_geq_has_bool_type a b
        (RuleProofs.eo_has_bool_type_not_arg _ hBool)
  | not_lt =>
      exact sameArith_swap (rel_operands_arith_type_of_lt_has_bool_type b a
        (RuleProofs.eo_has_bool_type_not_arg _ hBool))
  | not_le =>
      exact sameArith_swap (rel_operands_arith_type_of_leq_has_bool_type b a
        (RuleProofs.eo_has_bool_type_not_arg _ hBool))

private theorem variable_type (s : native_String) {T : Term} (hT : ArithType T) :
    __smtx_typeof (__eo_to_smt (qvar s T)) = __eo_to_smt_type T := by
  have hWf := (arithValue_facts hT 0).1
  change __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = __eo_to_smt_type T
  rw [smtx_typeof_var_term_eq]
  simp [__smtx_typeof_guard_wf, hWf, native_ite]

/-- Even the equality arm must compare arithmetic operands: normalization of
any other translatable sort consists of a single opaque atom. -/
theorem equality_diff_type (s : native_String) {T a b : Term} (hT : ArithType T)
    (hBool : RuleProofs.eo_has_bool_type (binary UserOp.eq a b))
    (hd : __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) ≠ Term.Stuck) :
    DiffType a b := by
  obtain ⟨hSame, hNone⟩ := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hBool
  by_cases hInt : __smtx_typeof (__eo_to_smt a) = SmtType.Int
  · exact diff_type_of_args (Or.inl ⟨hInt, hSame.symm.trans hInt⟩)
  · by_cases hReal : __smtx_typeof (__eo_to_smt a) = SmtType.Real
    · exact diff_type_of_args (Or.inr ⟨hReal, hSame.symm.trans hReal⟩)
    · have hNotIntB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Int := by rwa [← hSame]
      have hNotRealB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Real := by rwa [← hSame]
      have hNoneB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by rwa [← hSame]
      have hA : __get_arith_poly_norm a = atomic a := by
        simpa [arith_atomic_poly, atomic, poly, mon, single, zero, ratOne] using
          get_arith_poly_norm_of_non_arith_smt_type a hInt hReal hNone
      have hB : __get_arith_poly_norm b = atomic b := by
        simpa [arith_atomic_poly, atomic, poly, mon, single, zero, ratOne] using
          get_arith_poly_norm_of_non_arith_smt_type b hNotIntB hNotRealB hNoneB
      have hdir : ∃ d : Int,
          __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) = Term.Numeral d := by
        rcases linear_dir_range (qvar s T) (__get_arith_poly_norm (diff a b)) with h | h | h
        · exact False.elim (hd h)
        · exact ⟨-1, h⟩
        · exact ⟨1, h⟩
      obtain ⟨d, hdir⟩ := hdir
      obtain ⟨c, _, hl, _⟩ := linear_dir_nonzero (by simp [qvar])
        (nonzeroCoeffs_norm (diff a b)) d hdir
      have hnorm : __get_arith_poly_norm (diff a b) =
          __poly_add (atomic a) (__poly_neg (atomic b)) := by
        simp [diff, __get_arith_poly_norm, hA, hB]
      rw [hnorm] at hl
      have hx := hl.atomic_difference
      have hxTy : __smtx_typeof (__eo_to_smt (qvar s T)) = SmtType.Int ∨
          __smtx_typeof (__eo_to_smt (qvar s T)) = SmtType.Real := by
        rw [variable_type s hT]
        rcases hT with rfl | rfl <;> simp [__eo_to_smt_type]
      exfalso
      rcases hx with ha | hb
      · rw [ha] at hxTy
        exact hxTy.elim hInt hReal
      · rw [hb] at hxTy
        exact hxTy.elim hNotIntB hNotRealB

private theorem upper_escapes_raw (M : SmtModel) (hM : model_wf M) (s : native_String)
    {T a b f : Term} (hT : ArithType T) (hf : UpperLiteral a b f)
    (hBool : RuleProofs.eo_has_bool_type f) {d sign : Int}
    (hs : sign = -1 ∨ sign = 1) (hcompat : d * sign ≠ -1)
    (hd : __arith_linear_dir (qvar s T)
      (__poly_add (__get_arith_poly_norm a) (__poly_neg (__get_arith_poly_norm b))) = Term.Numeral d) :
    Escapes M s T sign f := by
  apply upper_escapes M hM s hT (hf.diff_type hBool) hf hs hcompat
  simpa [diff, __get_arith_poly_norm] using hd

private theorem equality_escapes_raw (M : SmtModel) (hM : model_wf M) (s : native_String)
    {T a b : Term} (hT : ArithType T) (hBool : RuleProofs.eo_has_bool_type (binary UserOp.eq a b))
    {d sign : Int} (hs : sign = -1 ∨ sign = 1)
    (hd : __eo_mul (Term.Numeral 0) (__arith_linear_dir (qvar s T)
      (__poly_add (__get_arith_poly_norm a) (__poly_neg (__get_arith_poly_norm b)))) = Term.Numeral d) :
    Escapes M s T sign (binary UserOp.eq a b) := by
  have hraw : __arith_linear_dir (qvar s T) (__get_arith_poly_norm (diff a b)) ≠ Term.Stuck := by
    intro hbad
    have hbad' : __arith_linear_dir (qvar s T)
        (__poly_add (__get_arith_poly_norm a) (__poly_neg (__get_arith_poly_norm b))) = Term.Stuck := by
      simpa [diff, __get_arith_poly_norm] using hbad
    simp [hbad', __eo_mul] at hd
  exact equality_escapes M hM s hT (equality_diff_type s hT hBool hraw) hs hraw

theorem literal_escapes (M : SmtModel) (hM : model_wf M) (s : native_String)
    {T f : Term} (hT : ArithType T) (hBool : RuleProofs.eo_has_bool_type f)
    {d sign : Int} (hs : sign = -1 ∨ sign = 1) (hcompat : d * sign ≠ -1)
    (hd : __get_quant_var_elim_ineq_dir (qvar s T) f = Term.Numeral d) :
    Escapes M s T sign f := by
  rw [__get_quant_var_elim_ineq_dir.eq_def] at hd
  split at hd <;> first
    | exact equality_escapes_raw M hM s hT hBool hs hd
    | exact upper_escapes_raw M hM s hT .lt hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .le hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .gt hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .ge hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .not_gt hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .not_ge hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .not_lt hBool hs hcompat hd
    | exact upper_escapes_raw M hM s hT .not_le hBool hs hcompat hd
    | cases hd
    | contradiction

end QuantVarElimIneq
