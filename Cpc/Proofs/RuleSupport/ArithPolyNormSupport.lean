module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.TypePreservation.CoreArith
import all Cpc.Proofs.TypePreservation.CoreArith
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
TODO: the typing bridge is now local to this file, but the semantic bridge still
needs an arithmetic polynomial-normalization soundness lemma outside the main
TypePreservation development.  The command-level rule below intentionally
depends only on these small local bridges, so it does not pull in the full
TypePreservation proof.
-/
private theorem prog_arith_poly_norm_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  __eo_prog_arith_poly_norm a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_arith_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let nA := __get_arith_poly_norm a
                  let nB := __get_arith_poly_norm b
                  have hReq :
                      __eo_requires nA nB
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_arith_poly_norm, nA, nB] using hProg
                  by_cases hEq : native_teq nA nB = true
                  · by_cases hSt : native_teq nA Term.Stuck = true
                    · exfalso
                      simp [__eo_requires, hEq, hSt, native_ite, native_not,
                        SmtEval.native_not] at hReq
                    · have hNormEq : nA = nB := by
                        simpa [native_teq] using hEq
                      have hNormNotStuck : nA ≠ Term.Stuck := by
                        intro hNA
                        have hDec : native_teq nA Term.Stuck = true := by
                          simp [hNA, native_teq]
                        exact hSt hDec
                      have hNormEq' :
                          __get_arith_poly_norm a = __get_arith_poly_norm b := by
                        simpa [nA, nB] using hNormEq
                      have hNormNotStuck' :
                          __get_arith_poly_norm a ≠ Term.Stuck := by
                        simpa [nA] using hNormNotStuck
                      have hNormNotStuckB' :
                          __get_arith_poly_norm b ≠ Term.Stuck := by
                        intro hNB
                        apply hNormNotStuck'
                        rw [hNormEq']
                        exact hNB
                      simp [__eo_prog_arith_poly_norm, __eo_requires, hNormEq',
                        hNormNotStuckB', native_ite, native_teq, native_not,
                        SmtEval.native_not]
                  · exfalso
                    simp [__eo_requires, hEq, native_ite
                      ] at hReq
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem eq_args_of_prog_arith_poly_norm_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  ∃ a b,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b ∧
    __get_arith_poly_norm a = __get_arith_poly_norm b ∧
    __get_arith_poly_norm a ≠ Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_arith_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let nA := __get_arith_poly_norm a
                  let nB := __get_arith_poly_norm b
                  have hReq :
                      __eo_requires nA nB
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_arith_poly_norm, nA, nB] using hProg
                  by_cases hEq : native_teq nA nB = true
                  · have hNormEq : nA = nB := by
                      simpa [native_teq] using hEq
                    by_cases hSt : native_teq nA Term.Stuck = true
                    · exfalso
                      simp [__eo_requires, hEq, hSt, native_ite, native_not,
                        SmtEval.native_not] at hReq
                    · have hNormNotStuck : nA ≠ Term.Stuck := by
                        intro hNA
                        have hDec : native_teq nA Term.Stuck = true := by
                          simp [hNA, native_teq]
                        exact hSt hDec
                      refine ⟨a, b, rfl, ?_, ?_⟩
                      · simpa [nA, nB] using hNormEq
                      · simpa [nA] using hNormNotStuck
                  · exfalso
                    simp [__eo_requires, hEq, native_ite
                      ] at hReq
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem typed___eo_prog_arith_poly_norm_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_poly_norm a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_arith_poly_norm a1 = a1 :=
    prog_arith_poly_norm_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
          SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
      rfl
    rw [← hTranslate]
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem smtx_model_eval_to_int_to_real_of_numeral
    (n : native_Int) :
  __smtx_model_eval_to_int (__smtx_to_real_coerce (SmtValue.Numeral n)) =
    SmtValue.Numeral n := by
  change SmtValue.Numeral (Rat.floor ((n : Rat) / 1)) = SmtValue.Numeral n
  congr
  have hDiv : ((n : Rat) / 1 : Rat) = (n : Rat) := by
    change ((n : Rat) * ((1 : Rat)⁻¹)) = (n : Rat)
    rw [Rat.inv_def]
    change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    exact Rat.mul_one _
  rw [hDiv]
  exact Rat.floor_intCast n

private theorem smtx_model_eval_to_real_idempotent
    (v : SmtValue) :
  __smtx_to_real_coerce (__smtx_to_real_coerce v) =
    __smtx_to_real_coerce v := by
  cases v <;> simp [__smtx_to_real_coerce]

noncomputable def arith_poly_norm_atom_denote_real (M : SmtModel) (t : Term) : SmtValue :=
  __smtx_to_real_coerce (__smtx_model_eval M (__eo_to_smt t))

noncomputable def arith_mvar_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.__eo_List_nil => SmtValue.Rational (native_mk_rational 1 1)
  | Term.Apply (Term.Apply Term.__eo_List_cons a) rest =>
      __smtx_model_eval_mult (arith_poly_norm_atom_denote_real M a)
        (arith_mvar_denote_real M rest)
  | _ => SmtValue.NotValue

noncomputable def arith_mon_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c) =>
      __smtx_model_eval_mult (SmtValue.Rational c) (arith_mvar_denote_real M vars)
  | _ => SmtValue.NotValue

noncomputable def arith_poly_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.UOp UserOp._at__at_poly_zero => SmtValue.Rational (native_mk_rational 0 1)
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p =>
      __smtx_model_eval_plus (arith_mon_denote_real M m) (arith_poly_denote_real M p)
  | _ => SmtValue.NotValue

private inductive arith_mvar_wf : Term -> Prop where
  | nil : arith_mvar_wf Term.__eo_List_nil
  | cons (a rest : Term) :
      arith_mvar_wf rest ->
      arith_mvar_wf (Term.Apply (Term.Apply Term.__eo_List_cons a) rest)

private inductive arith_mon_wf : Term -> Prop where
  | mk (vars : Term) (c : native_Rat) :
      arith_mvar_wf vars ->
      arith_mon_wf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))

private inductive arith_poly_wf : Term -> Prop where
  | zero : arith_poly_wf (Term.UOp UserOp._at__at_poly_zero)
  | cons (m p : Term) :
      arith_mon_wf m ->
      arith_poly_wf p ->
      arith_poly_wf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p)

theorem native_mk_rational_zero :
    native_mk_rational 0 1 = (0 : Rat) := by
  native_decide

theorem native_mk_rational_one :
    native_mk_rational 1 1 = (1 : Rat) := by
  native_decide

private theorem rat_mkRat_one_eq_intCast
    (n : native_Int) :
  mkRat n 1 = (n : Rat) := by
  unfold mkRat
  simp
  rw [Rat.normalize_eq]
  simp

theorem rat_div_one_intCast
    (n : native_Int) :
  ((n : Rat) / (1 : Rat)) = (n : Rat) := by
  change ((n : Rat) / ((1 : Int) : Rat)) = (n : Rat)
  rw [← Rat.divInt_eq_div n 1]
  change Rat.divInt n ((1 : Nat) : Int) = (n : Rat)
  rw [Rat.divInt_ofNat]
  exact rat_mkRat_one_eq_intCast n

private theorem arith_poly_norm_atom_denote_real_rational_or_notValue
    (M : SmtModel) (t : Term) :
  (∃ q, arith_poly_norm_atom_denote_real M t = SmtValue.Rational q) ∨
    arith_poly_norm_atom_denote_real M t = SmtValue.NotValue := by
  unfold arith_poly_norm_atom_denote_real
  cases hEval : __smtx_model_eval M (__eo_to_smt t) <;>
    simp [__smtx_to_real_coerce]

theorem arith_poly_norm_atom_denote_real_rational_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
  ∃ q, arith_poly_norm_atom_denote_real M t = SmtValue.Rational q := by
  have hNonNone : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rcases hTy with hTy | hTy <;> simp [hTy]
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNonNone
  rcases hTy with hTy | hTy
  · have hEvalInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hTy] using hEvalTy
    rcases int_value_canonical hEvalInt with ⟨n, hEval⟩
    refine ⟨native_to_real n, ?_⟩
    simp [arith_poly_norm_atom_denote_real, hEval, __smtx_to_real_coerce]
  · have hEvalReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hTy] using hEvalTy
    rcases real_value_canonical hEvalReal with ⟨q, hEval⟩
    exact ⟨q, by simp [arith_poly_norm_atom_denote_real, hEval, __smtx_to_real_coerce]⟩

private inductive arith_mvar_rational (M : SmtModel) : Term -> Prop where
  | nil : arith_mvar_rational M Term.__eo_List_nil
  | cons (a rest : Term) :
      (∃ q, arith_poly_norm_atom_denote_real M a = SmtValue.Rational q) ->
      arith_mvar_rational M rest ->
      arith_mvar_rational M (Term.Apply (Term.Apply Term.__eo_List_cons a) rest)

private inductive arith_mon_rational (M : SmtModel) : Term -> Prop where
  | mk (vars : Term) (c : native_Rat) :
      arith_mvar_rational M vars ->
      arith_mon_rational M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))

private inductive arith_poly_rational (M : SmtModel) : Term -> Prop where
  | zero : arith_poly_rational M (Term.UOp UserOp._at__at_poly_zero)
  | cons (m p : Term) :
      arith_mon_rational M m ->
      arith_poly_rational M p ->
      arith_poly_rational M (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p)

private theorem arith_mvar_rational_ne_stuck
    {M : SmtModel} {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  vars ≠ Term.Stuck := by
  intro hSt
  cases hvars <;> cases hSt

private theorem arith_mon_rational_ne_stuck
    {M : SmtModel} {m : Term}
    (hm : arith_mon_rational M m) :
  m ≠ Term.Stuck := by
  intro hSt
  cases hm <;> cases hSt

private theorem arith_poly_rational_ne_stuck
    {M : SmtModel} {p : Term}
    (hp : arith_poly_rational M p) :
  p ≠ Term.Stuck := by
  intro hSt
  cases hp <;> cases hSt

private theorem arith_mvar_wf_of_rational
    {M : SmtModel} {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  arith_mvar_wf vars := by
  induction hvars with
  | nil =>
      exact arith_mvar_wf.nil
  | cons a rest _ hRest ih =>
      exact arith_mvar_wf.cons a rest ih

private theorem arith_mon_wf_of_rational
    {M : SmtModel} {m : Term}
    (hm : arith_mon_rational M m) :
  arith_mon_wf m := by
  cases hm with
  | mk vars c hvars =>
      exact arith_mon_wf.mk vars c (arith_mvar_wf_of_rational hvars)

private theorem arith_poly_wf_of_rational
    {M : SmtModel} {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_wf p := by
  induction hp with
  | zero =>
      exact arith_poly_wf.zero
  | cons m p hm hp ih =>
      exact arith_poly_wf.cons m p (arith_mon_wf_of_rational hm) ih

private theorem arith_mvar_denote_real_rational_of_rational_support
    (M : SmtModel) {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  ∃ q, arith_mvar_denote_real M vars = SmtValue.Rational q := by
  induction hvars with
  | nil =>
      exact ⟨native_mk_rational 1 1, rfl⟩
  | cons a rest hA hRest ih =>
      rcases hA with ⟨qa, hA⟩
      rcases ih with ⟨qr, hRest⟩
      refine ⟨native_qmult qa qr, ?_⟩
      simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult, native_qmult]

private theorem arith_mon_denote_real_rational_of_rational_support
    (M : SmtModel) {m : Term}
    (hm : arith_mon_rational M m) :
  ∃ q, arith_mon_denote_real M m = SmtValue.Rational q := by
  cases hm with
  | mk vars c hvars =>
      rcases arith_mvar_denote_real_rational_of_rational_support M hvars with ⟨qv, hVars⟩
      refine ⟨native_qmult c qv, ?_⟩
      simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult]

private theorem arith_poly_denote_real_rational_of_rational_support
    (M : SmtModel) {p : Term}
    (hp : arith_poly_rational M p) :
  ∃ q, arith_poly_denote_real M p = SmtValue.Rational q := by
  induction hp with
  | zero =>
      exact ⟨native_mk_rational 0 1, rfl⟩
  | cons m p hm hp ih =>
      rcases arith_mon_denote_real_rational_of_rational_support M hm with ⟨qm, hMon⟩
      rcases ih with ⟨qp, hPoly⟩
      refine ⟨native_qplus qm qp, ?_⟩
      simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus, native_qplus]

private def arith_const_mon (q : native_Rat) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil) (Term.Rational q)

private theorem arith_atom_ne_stuck_of_rational_support
    {M : SmtModel} {a : Term}
    (hA : ∃ q, arith_poly_norm_atom_denote_real M a = SmtValue.Rational q) :
  a ≠ Term.Stuck := by
  intro hSt
  subst a
  rcases hA with ⟨q, hA⟩
  unfold arith_poly_norm_atom_denote_real at hA
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hA
  simp [__smtx_model_eval, __smtx_to_real_coerce] at hA

private theorem mvar_mul_mvar_nil_left
    (vars : Term) :
  __mvar_mul_mvar Term.__eo_List_nil vars = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_nil_right
    (vars : Term) :
  __mvar_mul_mvar vars Term.__eo_List_nil = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_cons_cons_true
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = true) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons a1)
      (__mvar_mul_mvar rest1
        (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2)) := by
  simp [__mvar_mul_mvar, __eo_cmp, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem mvar_mul_mvar_cons_cons_false
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = false) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons c1)
      (__mvar_mul_mvar
        (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2) := by
  simp [__mvar_mul_mvar, __eo_cmp, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem mon_mul_mon_of_const_left
    (q c : native_Rat) (vars : Term)
    (hVars : vars ≠ Term.Stuck) :
  __mon_mul_mon (arith_const_mon q)
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)) =
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
      (Term.Rational (native_qmult q c)) := by
  cases vars <;>
    simp [arith_const_mon, __mon_mul_mon, __mvar_mul_mvar, __eo_mk_apply, __eo_mul] at hVars ⊢

private theorem poly_of_mon_mul_mon_const_left
    (q c : native_Rat) (vars : Term)
    (hVars : vars ≠ Term.Stuck) :
  __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
        (__mon_mul_mon (arith_const_mon q)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))))
      (Term.UOp UserOp._at__at_poly_zero) =
    Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_poly)
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
          (Term.Rational (native_qmult q c))))
      (Term.UOp UserOp._at__at_poly_zero) := by
  rw [mon_mul_mon_of_const_left q c vars hVars]
  simp [__eo_mk_apply]

private theorem arith_poly_rational_of_poly_neg
    (M : SmtModel) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_neg p) := by
  induction hp with
  | zero =>
      simpa [__poly_neg] using arith_poly_rational.zero (M := M)
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_rational_ne_stuck ih
          simpa [__poly_neg, __eo_mk_apply, __eo_neg, hTail] using
            (arith_poly_rational.cons
              (M := M)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qneg c)))
              (__poly_neg p)
              (arith_mon_rational.mk (M := M) vars (native_qneg c) hvars)
              ih)

private theorem arith_poly_rational_of_poly_add
    (M : SmtModel) {P1 P2 : Term}
    (h1 : arith_poly_rational M P1)
    (h2 : arith_poly_rational M P2) :
  arith_poly_rational M (__poly_add P1 P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_rational.zero (M := M)
      | @cons m2 p2 hm2 hp2 =>
          simpa [__poly_add] using arith_poly_rational.cons (M := M) m2 p2 hm2 hp2
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_rational.cons (M := M) m1 p1 hm1 hp1
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec : arith_poly_rational M (__poly_add p1 p2) :=
                      arith_poly_rational_of_poly_add M hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero'] using hRec
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero', __eo_mk_apply, hTail] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_qplus c1 c2)))
                          (__poly_add p1 p2)
                          (arith_mon_rational.mk (M := M) vars1 (native_qplus c1 c2) hvars1)
                          hRec)
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec : arith_poly_rational M
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational c2)))
                                p2)) :=
                          arith_poly_rational_of_poly_add M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational c2))
                              p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2) ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational c1))
                          (__poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2))
                          (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                          hRec)
                    · have hRec : arith_poly_rational M
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational c1)))
                                p1)
                              p2) :=
                          arith_poly_rational_of_poly_add M
                            (arith_poly_rational.cons
                              (M := M)
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational c1))
                              p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational c2))
                          (__poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2)
                          (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                          hRec)
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_rational_of_poly_mul_mon_const
    (M : SmtModel) (q : native_Rat) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_mul_mon (arith_const_mon q) p) := by
  induction hp with
  | zero =>
      simpa [arith_const_mon, __poly_mul_mon] using arith_poly_rational.zero (M := M)
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hVars : vars ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars
          have hHead :
              arith_poly_rational M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_poly)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational (native_qmult q c))))
                  (Term.UOp UserOp._at__at_poly_zero)) := by
            exact arith_poly_rational.cons
              (M := M)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qmult q c)))
              (Term.UOp UserOp._at__at_poly_zero)
              (arith_mon_rational.mk (M := M) vars (native_qmult q c) hvars)
              (arith_poly_rational.zero (M := M))
          change arith_poly_rational M
            (__poly_add
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                  (__mon_mul_mon (arith_const_mon q)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational c))))
                (Term.UOp UserOp._at__at_poly_zero))
              (__poly_mul_mon (arith_const_mon q) p))
          rw [poly_of_mon_mul_mon_const_left q c vars hVars]
          exact arith_poly_rational_of_poly_add M hHead ih

private theorem arith_mvar_rational_of_mvar_mul_mvar
    (M : SmtModel) {vars1 vars2 : Term}
    (hvars1 : arith_mvar_rational M vars1)
    (hvars2 : arith_mvar_rational M vars2) :
  arith_mvar_rational M (__mvar_mul_mvar vars1 vars2) := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      exact hvars2
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          exact arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1
      | cons c1 rest2 hC1 hRest2 =>
          have hA1NotStuck : a1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hA1
          have hC1NotStuck : c1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hC1
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hTail :
                __mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp]
            simpa [__eo_mk_apply, hTail] using
              (arith_mvar_rational.cons (M := M) a1
                (__mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2))
                hA1
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)))
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false =>
                  rfl
              | true =>
                  exfalso
                  exact hCmp hT
            have hTail :
                __mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2 ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp']
            simpa [__eo_mk_apply, hTail] using
              (arith_mvar_rational.cons (M := M) c1
                (__mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2)
                hC1
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2))
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem arith_mon_rational_of_mon_mul_mon
    (M : SmtModel) {m1 m2 : Term}
    (hm1 : arith_mon_rational M m1)
    (hm2 : arith_mon_rational M m2) :
  arith_mon_rational M (__mon_mul_mon m1 m2) := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            arith_mvar_rational_ne_stuck
              (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1) (Term.Rational c1))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2) (Term.Rational c2)) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_qmult c1 c2)) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply]]
          exact arith_mon_rational.mk (M := M) (__mvar_mul_mvar vars1 vars2)
            (native_qmult c1 c2) (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)

private theorem arith_poly_rational_of_poly_mul_mon
    (M : SmtModel) {m p : Term}
    (hm : arith_mon_rational M m)
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_mul_mon m p) := by
  have hMNe : m ≠ Term.Stuck := arith_mon_rational_ne_stuck hm
  induction hp with
  | zero =>
      simpa [__poly_mul_mon, hMNe] using arith_poly_rational.zero (M := M)
  | @cons m2 p2 hm2 hp2 ih =>
      have hMul : arith_mon_rational M (__mon_mul_mon m m2) :=
        arith_mon_rational_of_mon_mul_mon M hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        arith_mon_rational_ne_stuck hMul
      have hHead :
          arith_poly_rational M
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_poly_zero)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (arith_poly_rational.cons
            (M := M)
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_poly_zero)
            hMul
            (arith_poly_rational.zero (M := M)))
      simpa [__poly_mul_mon, hMNe] using arith_poly_rational_of_poly_add M hHead ih

private theorem arith_poly_rational_of_poly_mul
    (M : SmtModel) {p1 p2 : Term}
    (hp1 : arith_poly_rational M p1)
    (hp2 : arith_poly_rational M p2) :
  arith_poly_rational M (__poly_mul p1 p2) := by
  have hP2Ne : p2 ≠ Term.Stuck := arith_poly_rational_ne_stuck hp2
  induction hp1 with
  | zero =>
      simpa [__poly_mul, hP2Ne] using arith_poly_rational.zero (M := M)
  | @cons m p1 hm hp1 ih =>
      simpa [__poly_mul, hP2Ne] using
        arith_poly_rational_of_poly_add M
          (arith_poly_rational_of_poly_mul_mon M hm hp2)
          ih

private theorem arith_mvar_denote_real_rational_or_notValue
    (M : SmtModel) (vars : Term) :
  (∃ q, arith_mvar_denote_real M vars = SmtValue.Rational q) ∨
    arith_mvar_denote_real M vars = SmtValue.NotValue := by
  cases vars with
  | __eo_List_nil =>
      exact Or.inl ⟨native_mk_rational 1 1, rfl⟩
  | Apply f rest =>
      cases f with
      | Apply g a =>
          cases g with
          | __eo_List_cons =>
              rcases arith_poly_norm_atom_denote_real_rational_or_notValue M a with hA | hA
              · rcases hA with ⟨qa, hA⟩
                rcases arith_mvar_denote_real_rational_or_notValue M rest with hRest | hRest
                · rcases hRest with ⟨qr, hRest⟩
                  refine Or.inl ?_
                  refine ⟨native_qmult qa qr, ?_⟩
                  simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult, native_qmult]
                · exact Or.inr (by
                    simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult])
              · exact Or.inr (by
                  simp [arith_mvar_denote_real, hA, __smtx_model_eval_mult])
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl
termination_by sizeOf vars
decreasing_by
  simp_wf
  all_goals omega

private theorem arith_mon_denote_real_rational_or_notValue
    (M : SmtModel) (m : Term) :
  (∃ q, arith_mon_denote_real M m = SmtValue.Rational q) ∨
    arith_mon_denote_real M m = SmtValue.NotValue := by
  cases m with
  | Apply f c =>
      cases f with
      | Apply g vars =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_mon =>
                  cases c with
                  | Rational q =>
                      rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
                      · rcases hVars with ⟨qv, hVars⟩
                        refine Or.inl ?_
                        refine ⟨native_qmult q qv, ?_⟩
                        simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult]
                      · exact Or.inr (by
                          simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult])
                  | _ =>
                      exact Or.inr rfl
              | _ =>
                  exact Or.inr rfl
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl

private theorem arith_poly_denote_real_rational_or_notValue
    (M : SmtModel) (p : Term) :
  (∃ q, arith_poly_denote_real M p = SmtValue.Rational q) ∨
    arith_poly_denote_real M p = SmtValue.NotValue := by
  cases p with
  | UOp op =>
      cases op with
      | _at__at_poly_zero =>
          exact Or.inl ⟨native_mk_rational 0 1, rfl⟩
      | _ =>
          exact Or.inr rfl
  | Apply f tail =>
      cases f with
      | Apply g m =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_poly =>
                  rcases arith_mon_denote_real_rational_or_notValue M m with hMon | hMon
                  · rcases hMon with ⟨qm, hMon⟩
                    rcases arith_poly_denote_real_rational_or_notValue M tail with hPoly | hPoly
                    · rcases hPoly with ⟨qp, hPoly⟩
                      refine Or.inl ?_
                      refine ⟨native_qplus qm qp, ?_⟩
                      simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus, native_qplus]
                    · exact Or.inr (by
                        simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus])
                  · exact Or.inr (by
                      simp [arith_poly_denote_real, hMon, __smtx_model_eval_plus])
              | _ =>
                  exact Or.inr rfl
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl
termination_by sizeOf p
decreasing_by
  simp_wf
  all_goals omega

private theorem smtx_model_eval_plus_zero_left_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_plus (SmtValue.Rational (native_mk_rational 0 1)) v = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, native_mk_rational_zero, Rat.zero_add]

private theorem smtx_model_eval_plus_zero_right_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_plus v (SmtValue.Rational (native_mk_rational 0 1)) = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, native_mk_rational_zero, Rat.add_zero]

private theorem smtx_model_eval_mult_one_left_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult (SmtValue.Rational (native_mk_rational 1 1)) v = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, native_mk_rational_one]

private theorem smtx_model_eval_mult_one_right_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult v (SmtValue.Rational (native_mk_rational 1 1)) = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, native_mk_rational_one]

private theorem smtx_model_eval_plus_uneg_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus (__smtx_model_eval_uneg v1) (__smtx_model_eval_uneg v2) =
    __smtx_model_eval_uneg (__smtx_model_eval_plus v1 v2) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, __smtx_model_eval_uneg, native_qplus, native_qneg,
      Rat.neg_add]

private theorem smtx_model_eval_plus_comm_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus v1 v2 = __smtx_model_eval_plus v2 v1 := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, Rat.add_comm]

private theorem smtx_model_eval_plus_assoc_of_rational_or_notValue
    {v1 v2 v3 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue)
    (h3 : (∃ q, v3 = SmtValue.Rational q) ∨ v3 = SmtValue.NotValue) :
  __smtx_model_eval_plus (__smtx_model_eval_plus v1 v2) v3 =
    __smtx_model_eval_plus v1 (__smtx_model_eval_plus v2 v3) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;>
    rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    rcases h3 with ⟨q3, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, Rat.add_assoc]

private theorem smtx_model_eval_mult_comm_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_mult v1 v2 = __smtx_model_eval_mult v2 v1 := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, Rat.mul_comm]

private theorem smtx_model_eval_mult_assoc_of_rational_or_notValue
    {v1 v2 v3 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue)
    (h3 : (∃ q, v3 = SmtValue.Rational q) ∨ v3 = SmtValue.NotValue) :
  __smtx_model_eval_mult (__smtx_model_eval_mult v1 v2) v3 =
    __smtx_model_eval_mult v1 (__smtx_model_eval_mult v2 v3) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;>
    rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    rcases h3 with ⟨q3, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, Rat.mul_assoc]

private theorem smtx_model_eval_mult_neg_left_of_rational_or_notValue
    (q : native_Rat) {v : SmtValue}
    (hv : (∃ qv, v = SmtValue.Rational qv) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult (SmtValue.Rational (native_qneg q)) v =
    __smtx_model_eval_uneg (__smtx_model_eval_mult (SmtValue.Rational q) v) := by
  rcases hv with ⟨qv, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, __smtx_model_eval_uneg, native_qmult, native_qneg,
      Rat.neg_mul]

private theorem smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
    (q : native_Rat) (v1 v2 : SmtValue)
    (hv1 : (∃ q1, v1 = SmtValue.Rational q1) ∨ v1 = SmtValue.NotValue)
    (hv2 : (∃ q2, v2 = SmtValue.Rational q2) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus
      (__smtx_model_eval_mult (SmtValue.Rational q) v1)
      (__smtx_model_eval_mult (SmtValue.Rational q) v2) =
    __smtx_model_eval_mult
      (SmtValue.Rational q)
      (__smtx_model_eval_plus v1 v2) := by
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · rcases h1 with ⟨q1, rfl⟩
    rcases h2 with ⟨q2, rfl⟩
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus, native_qmult, native_qplus,
      Rat.mul_add]
  · rcases h1 with ⟨q1, rfl⟩
    simp [h2, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · rcases h2 with ⟨q2, rfl⟩
    simp [h1, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · simp [h1, h2, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem smtx_model_eval_mult_rational_right_distrib_plus_of_rational_or_notValue
    (q : native_Rat) (v1 v2 : SmtValue)
    (hv1 : (∃ q1, v1 = SmtValue.Rational q1) ∨ v1 = SmtValue.NotValue)
    (hv2 : (∃ q2, v2 = SmtValue.Rational q2) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus
      (__smtx_model_eval_mult v1 (SmtValue.Rational q))
      (__smtx_model_eval_mult v2 (SmtValue.Rational q)) =
    __smtx_model_eval_mult
      (__smtx_model_eval_plus v1 v2)
      (SmtValue.Rational q) := by
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · rcases h1 with ⟨q1, rfl⟩
    rcases h2 with ⟨q2, rfl⟩
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus, native_qmult, native_qplus,
      Rat.add_mul]
  · rcases h1 with ⟨q1, rfl⟩
    simp [h2, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · rcases h2 with ⟨q2, rfl⟩
    simp [h1, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · simp [h1, h2, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_mon_denote_real_of_coeff_add
    (M : SmtModel) (vars : Term) (c1 c2 : native_Rat) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_qplus c1 c2))) =
    __smtx_model_eval_plus
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c1)))
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c2))) := by
  rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
  · rcases hVars with ⟨qv, hVars⟩
    simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, __smtx_model_eval_plus,
      native_qmult, native_qplus, Rat.add_mul]
  · simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_mon_denote_real_of_coeff_mul
    (M : SmtModel) (vars : Term) (c1 c2 : native_Rat) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_qmult c1 c2))) =
    __smtx_model_eval_mult
      (SmtValue.Rational c1)
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c2))) := by
  rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
  · rcases hVars with ⟨qv, hVars⟩
    simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult, Rat.mul_assoc]
  · simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult]

private theorem arith_mvar_denote_real_of_mvar_mul_mvar_rational
    (M : SmtModel) {vars1 vars2 : Term}
    (hvars1 : arith_mvar_rational M vars1)
    (hvars2 : arith_mvar_rational M vars2) :
  arith_mvar_denote_real M (__mvar_mul_mvar vars1 vars2) =
    __smtx_model_eval_mult (arith_mvar_denote_real M vars1) (arith_mvar_denote_real M vars2) := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      exact (smtx_model_eval_mult_one_left_of_rational_or_notValue
        (Or.inl (arith_mvar_denote_real_rational_of_rational_support M hvars2))).symm
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          exact (smtx_model_eval_mult_one_right_of_rational_or_notValue
            (Or.inl (arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1)))).symm
      | cons c1 rest2 hC1 hRest2 =>
          let vars1' := Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1
          let vars2' := Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2
          have hRest1Val : ∃ q, arith_mvar_denote_real M rest1 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hRest1
          have hVars1Val : ∃ q, arith_mvar_denote_real M vars1' = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1)
          have hRest2Val : ∃ q, arith_mvar_denote_real M rest2 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hRest2
          have hVars2Val : ∃ q, arith_mvar_denote_real M vars2' = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)
          have hA1NotStuck : a1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hA1
          have hC1NotStuck : c1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hC1
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hRec :
                arith_mvar_denote_real M (__mvar_mul_mvar rest1 vars2') =
                  __smtx_model_eval_mult (arith_mvar_denote_real M rest1)
                    (arith_mvar_denote_real M vars2') :=
              arith_mvar_denote_real_of_mvar_mul_mvar_rational M hRest1
                (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)
            have hTail :
                __mvar_mul_mvar rest1 vars2' ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp]
            calc
              arith_mvar_denote_real M (__eo_mk_apply (Term.Apply Term.__eo_List_cons a1)
                  (__mvar_mul_mvar rest1 vars2')) =
                __smtx_model_eval_mult (arith_poly_norm_atom_denote_real M a1)
                  (__smtx_model_eval_mult (arith_mvar_denote_real M rest1)
                    (arith_mvar_denote_real M vars2')) := by
                  simp [__eo_mk_apply, arith_mvar_denote_real, hRec]
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_poly_norm_atom_denote_real M a1)
                    (arith_mvar_denote_real M rest1))
                  (arith_mvar_denote_real M vars2') := by
                  exact
                    (smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hA1) (Or.inl hRest1Val) (Or.inl hVars2Val)).symm
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (arith_mvar_denote_real M vars2') := by
                  simp [vars1', arith_mvar_denote_real]
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false =>
                  rfl
              | true =>
                  exfalso
                  exact hCmp hT
            have hRec :
                arith_mvar_denote_real M (__mvar_mul_mvar vars1' rest2) =
                  __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_mvar_denote_real M rest2) :=
              arith_mvar_denote_real_of_mvar_mul_mvar_rational M
                (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2
            have hTail :
                __mvar_mul_mvar vars1' rest2 ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp']
            calc
              arith_mvar_denote_real M (__eo_mk_apply (Term.Apply Term.__eo_List_cons c1)
                  (__mvar_mul_mvar vars1' rest2)) =
                __smtx_model_eval_mult (arith_poly_norm_atom_denote_real M c1)
                  (__smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_mvar_denote_real M rest2)) := by
                  simp [__eo_mk_apply, arith_mvar_denote_real, hRec]
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_poly_norm_atom_denote_real M c1)
                    (arith_mvar_denote_real M vars1'))
                  (arith_mvar_denote_real M rest2) := by
                  exact
                    (smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hC1) (Or.inl hVars1Val) (Or.inl hRest2Val)).symm
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_poly_norm_atom_denote_real M c1))
                  (arith_mvar_denote_real M rest2) := by
                  rw [smtx_model_eval_mult_comm_of_rational_or_notValue
                    (Or.inl hC1) (Or.inl hVars1Val)]
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (__smtx_model_eval_mult (arith_poly_norm_atom_denote_real M c1)
                    (arith_mvar_denote_real M rest2)) := by
                  exact
                    smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hVars1Val) (Or.inl hC1) (Or.inl hRest2Val)
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (arith_mvar_denote_real M vars2') := by
                  simp [vars2', arith_mvar_denote_real]
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem arith_mon_denote_real_of_mon_mul_mon_rational
    (M : SmtModel) {m1 m2 : Term}
    (hm1 : arith_mon_rational M m1)
    (hm2 : arith_mon_rational M m2) :
  arith_mon_denote_real M (__mon_mul_mon m1 m2) =
    __smtx_model_eval_mult (arith_mon_denote_real M m1) (arith_mon_denote_real M m2) := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            arith_mvar_rational_ne_stuck
              (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)
          have hVars1Val : ∃ q, arith_mvar_denote_real M vars1 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hvars1
          have hVars2Val : ∃ q, arith_mvar_denote_real M vars2 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hvars2
          rcases hVars1Val with ⟨q1, hVars1Val⟩
          rcases hVars2Val with ⟨q2, hVars2Val⟩
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1) (Term.Rational c1))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2) (Term.Rational c2)) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_qmult c1 c2)) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply]]
          rw [arith_mon_denote_real_of_coeff_mul M (__mvar_mul_mvar vars1 vars2) c1 c2]
          simp [arith_mon_denote_real]
          rw [arith_mvar_denote_real_of_mvar_mul_mvar_rational M hvars1 hvars2]
          rw [hVars1Val, hVars2Val]
          simp [__smtx_model_eval_mult, native_qmult]
          calc
            c1 * (c2 * (q1 * q2)) = c1 * ((c2 * q1) * q2) := by rw [Rat.mul_assoc c2 q1 q2]
            _ = c1 * ((q1 * c2) * q2) := by rw [Rat.mul_comm c2 q1]
            _ = c1 * (q1 * (c2 * q2)) := by rw [← Rat.mul_assoc q1 c2 q2]
            _ = c1 * q1 * (c2 * q2) := by rw [Rat.mul_assoc c1 q1 (c2 * q2)]

private theorem arith_mon_denote_real_zero_coeff_of_rational
    (M : SmtModel) (vars : Term)
    (hVars : ∃ qv, arith_mvar_denote_real M vars = SmtValue.Rational qv) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_mk_rational 0 1))) =
    SmtValue.Rational (native_mk_rational 0 1) := by
  rcases hVars with ⟨qv, hVars⟩
  simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult,
    native_mk_rational_zero, Rat.zero_mul]

private theorem arith_mvar_wf_ne_stuck
    {vars : Term}
    (hvars : arith_mvar_wf vars) :
  vars ≠ Term.Stuck := by
  intro hSt
  cases hvars <;> cases hSt

private theorem arith_poly_wf_ne_stuck
    {p : Term}
    (hp : arith_poly_wf p) :
  p ≠ Term.Stuck := by
  intro hSt
  cases hp <;> cases hSt

private theorem arith_poly_wf_of_poly_neg
    {p : Term}
    (hp : arith_poly_wf p) :
  arith_poly_wf (__poly_neg p) := by
  induction hp with
  | zero =>
      simpa [__poly_neg] using arith_poly_wf.zero
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_wf_ne_stuck ih
          simpa [__poly_neg, __eo_mk_apply, __eo_neg, hTail] using
            (arith_poly_wf.cons
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qneg c)))
              (__poly_neg p)
              (arith_mon_wf.mk vars (native_qneg c) hvars)
              ih)

private theorem arith_poly_wf_of_poly_add
    {P1 P2 : Term}
    (h1 : arith_poly_wf P1)
    (h2 : arith_poly_wf P2) :
  arith_poly_wf (__poly_add P1 P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_wf.zero
      | @cons m2 p2 hm2 hp2 =>
          simpa [__poly_add] using arith_poly_wf.cons m2 p2 hm2 hp2
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_wf.cons m1 p1 hm1 hp1
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_wf_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_wf_ne_stuck hvars2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec : arith_poly_wf (__poly_add p1 p2) :=
                        arith_poly_wf_of_poly_add hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero']
                        using hRec
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                          arith_poly_wf_ne_stuck hRec
                      have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero', __eo_mk_apply, hTail] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_qplus c1 c2)))
                          (__poly_add p1 p2)
                          (arith_mon_wf.mk vars1 (native_qplus c1 c2) hvars1)
                          hRec)
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec : arith_poly_wf
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational c2)))
                                p2)) :=
                          arith_poly_wf_of_poly_add hp1
                            (arith_poly_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational c2))
                              p2
                              (arith_mon_wf.mk vars2 c2 hvars2)
                              hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2) ≠ Term.Stuck :=
                        arith_poly_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational c1))
                          (__poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2))
                          (arith_mon_wf.mk vars1 c1 hvars1)
                          hRec)
                    · have hRec : arith_poly_wf
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational c1)))
                                p1)
                              p2) :=
                          arith_poly_wf_of_poly_add
                            (arith_poly_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational c1))
                              p1
                              (arith_mon_wf.mk vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2 ≠ Term.Stuck :=
                        arith_poly_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail, __eo_add, hRec, native_ite, native_mk_rational] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational c2))
                          (__poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2)
                          (arith_mon_wf.mk vars2 c2 hvars2)
                          hRec)
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_denote_real_of_poly_neg_wf
    (M : SmtModel) {p : Term}
    (hp : arith_poly_wf p) :
  arith_poly_denote_real M (__poly_neg p) =
    __smtx_model_eval_uneg (arith_poly_denote_real M p) := by
  induction hp with
  | zero =>
      simp [__poly_neg, arith_poly_denote_real, __smtx_model_eval_uneg, native_qneg,
        native_mk_rational_zero]
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_wf_ne_stuck (arith_poly_wf_of_poly_neg hp)
          have hMult :
              __smtx_model_eval_mult (SmtValue.Rational (native_qneg c))
                  (arith_mvar_denote_real M vars) =
                __smtx_model_eval_uneg
                  (__smtx_model_eval_mult (SmtValue.Rational c) (arith_mvar_denote_real M vars)) :=
            smtx_model_eval_mult_neg_left_of_rational_or_notValue c
              (arith_mvar_denote_real_rational_or_notValue M vars)
          simp [__poly_neg, __eo_mk_apply, __eo_neg, arith_poly_denote_real,
            arith_mon_denote_real, ih]
          rw [hMult]
          exact
            smtx_model_eval_plus_uneg_of_rational_or_notValue
              (arith_mon_denote_real_rational_or_notValue M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)))
              (arith_poly_denote_real_rational_or_notValue M p)

private theorem arith_poly_denote_real_of_poly_add_rational
    (M : SmtModel) {P1 P2 : Term}
    (h1 : arith_poly_rational M P1)
    (h2 : arith_poly_rational M P2) :
  arith_poly_denote_real M (__poly_add P1 P2) =
    __smtx_model_eval_plus (arith_poly_denote_real M P1) (arith_poly_denote_real M P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simp [__poly_add, arith_poly_denote_real, __smtx_model_eval_plus, native_qplus,
            native_mk_rational_zero, Rat.zero_add]
      | @cons m2 p2 hm2 hp2 =>
          have hP2Val :
              ∃ q, arith_poly_denote_real M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m2) p2) =
                  SmtValue.Rational q :=
            arith_poly_denote_real_rational_of_rational_support M
              (arith_poly_rational.cons (M := M) m2 p2 hm2 hp2)
          simpa [__poly_add, arith_poly_denote_real] using
            (smtx_model_eval_plus_zero_left_of_rational_or_notValue (Or.inl hP2Val)).symm
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          have hP1Val :
              ∃ q, arith_poly_denote_real M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m1) p1) =
                  SmtValue.Rational q :=
            arith_poly_denote_real_rational_of_rational_support M
              (arith_poly_rational.cons (M := M) m1 p1 hm1 hp1)
          simpa [__poly_add, arith_poly_denote_real] using
            (smtx_model_eval_plus_zero_right_of_rational_or_notValue (Or.inl hP1Val)).symm
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars2
                  let mon1 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                      (Term.Rational c1)
                  let mon2 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                      (Term.Rational c2)
                  let poly1 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon1) p1
                  let poly2 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon2) p2
                  have hMon1Val : ∃ q, arith_mon_denote_real M mon1 = SmtValue.Rational q := by
                    simpa [mon1] using
                      arith_mon_denote_real_rational_of_rational_support M
                        (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                  have hMon2Val : ∃ q, arith_mon_denote_real M mon2 = SmtValue.Rational q := by
                    simpa [mon2] using
                      arith_mon_denote_real_rational_of_rational_support M
                        (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                  have hP1Val : ∃ q, arith_poly_denote_real M p1 = SmtValue.Rational q :=
                    arith_poly_denote_real_rational_of_rational_support M hp1
                  have hP2Val : ∃ q, arith_poly_denote_real M p2 = SmtValue.Rational q :=
                    arith_poly_denote_real_rational_of_rational_support M hp2
                  rcases hMon1Val with ⟨qm1, hMon1Eq⟩
                  rcases hMon2Val with ⟨qm2, hMon2Eq⟩
                  rcases hP1Val with ⟨qp1, hP1Eq⟩
                  rcases hP2Val with ⟨qp2, hP2Eq⟩
                  have hPoly1Val : ∃ q, arith_poly_denote_real M poly1 = SmtValue.Rational q := by
                    refine ⟨native_qplus qm1 qp1, ?_⟩
                    simp [poly1, mon1, arith_poly_denote_real, hMon1Eq, hP1Eq,
                      __smtx_model_eval_plus, native_qplus]
                  have hPoly2Val : ∃ q, arith_poly_denote_real M poly2 = SmtValue.Rational q := by
                    refine ⟨native_qplus qm2 qp2, ?_⟩
                    simp [poly2, mon2, arith_poly_denote_real, hMon2Eq, hP2Eq,
                      __smtx_model_eval_plus, native_qplus]
                  have hP12Val :
                      ∃ q,
                        __smtx_model_eval_plus
                          (arith_poly_denote_real M p1)
                          (arith_poly_denote_real M p2) = SmtValue.Rational q := by
                    refine ⟨native_qplus qp1 qp2, ?_⟩
                    simp [hP1Eq, hP2Eq, __smtx_model_eval_plus, native_qplus]
                  have hM2P1Val :
                      ∃ q,
                        __smtx_model_eval_plus
                          (arith_mon_denote_real M mon2)
                          (arith_poly_denote_real M p1) = SmtValue.Rational q := by
                    refine ⟨native_qplus qm2 qp1, ?_⟩
                    simp [hMon2Eq, hP1Eq, __smtx_model_eval_plus, native_qplus]
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec :
                        arith_poly_denote_real M (__poly_add p1 p2) =
                          __smtx_model_eval_plus
                            (arith_poly_denote_real M p1)
                            (arith_poly_denote_real M p2) :=
                      arith_poly_denote_real_of_poly_add_rational M hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      have hVarsRat :
                          ∃ qv, arith_mvar_denote_real M vars1 = SmtValue.Rational qv :=
                        arith_mvar_denote_real_rational_of_rational_support M hvars1
                      have hMonSum :
                          __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (arith_mon_denote_real M mon2) =
                            SmtValue.Rational (native_mk_rational 0 1) := by
                        have hCoeffZero :
                            arith_mon_denote_real M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_qplus c1 c2))) =
                              SmtValue.Rational (native_mk_rational 0 1) := by
                          simpa [hZero', mon2] using
                            arith_mon_denote_real_zero_coeff_of_rational M vars1 hVarsRat
                        exact (arith_mon_denote_real_of_coeff_add M vars1 c1 c2).symm.trans
                          hCoeffZero
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M p1)
                              (arith_poly_denote_real M p2) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            __eo_add, native_ite, native_teq, hZero',
                            hRec]
                        _ =
                            __smtx_model_eval_plus
                              (SmtValue.Rational (native_mk_rational 0 1))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          symm
                          exact
                            smtx_model_eval_plus_zero_left_of_rational_or_notValue
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          rw [← hMonSum]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_poly_denote_real M p2))) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p1))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_assoc_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)
                            (Or.inl ⟨qp2, hP2Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_mon_denote_real M mon2))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p2))) := by
                          simpa using congrArg
                            (__smtx_model_eval_plus (arith_mon_denote_real M mon1))
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩))
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          simp [poly2, mon2, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                    · have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      have hTail :
                          __poly_add p1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck (arith_poly_rational_of_poly_add M hp1 hp2)
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_qplus c1 c2))))
                              (arith_poly_denote_real M (__poly_add p1 p2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            __eo_add, native_ite, native_teq, hZero', __eo_mk_apply,
                            arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (arith_poly_denote_real M (__poly_add p1 p2)) := by
                          rw [arith_mon_denote_real_of_coeff_add M vars1 c1 c2]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_poly_denote_real M p2))) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p1))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_assoc_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)
                            (Or.inl ⟨qp2, hP2Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_mon_denote_real M mon2))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p2))) := by
                          simpa using congrArg
                            (__smtx_model_eval_plus (arith_mon_denote_real M mon1))
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩))
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          simp [poly2, mon2, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec :
                            arith_poly_denote_real M (__poly_add p1 poly2) =
                              __smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2) :=
                          arith_poly_denote_real_of_poly_add_rational M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              mon2 p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2)
                      have hTail : __poly_add p1 poly2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck
                          (arith_poly_rational_of_poly_add M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              mon2 p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2))
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (arith_poly_denote_real M (__poly_add p1 poly2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            native_ite, native_teq, hEq', __eo_cmp, hCmp,
                            __eo_mk_apply, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                    · have hRec :
                            arith_poly_denote_real M (__poly_add poly1 p2) =
                              __smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_poly_denote_real M p2) :=
                          arith_poly_denote_real_of_poly_add_rational M
                            (arith_poly_rational.cons
                              (M := M) mon1 p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hCmp' : native_tcmp vars2 vars1 = false := by
                        cases hT : native_tcmp vars2 vars1 with
                        | false =>
                            rfl
                        | true =>
                            cases (hCmp hT)
                      have hTail : __poly_add poly1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck
                          (arith_poly_rational_of_poly_add M
                            (arith_poly_rational.cons
                              (M := M) mon1 p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2)
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon2)
                              (arith_poly_denote_real M (__poly_add poly1 p2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            native_ite, native_teq, hEq', __eo_cmp, hCmp',
                            __eo_mk_apply, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon2)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_poly_denote_real M p2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (arith_poly_denote_real M poly1))
                              (arith_poly_denote_real M p2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hPoly1Val)
                              (Or.inl ⟨qp2, hP2Eq⟩)).symm
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_mon_denote_real M mon2))
                              (arith_poly_denote_real M p2) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl hPoly1Val)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (arith_poly_denote_real M p2)) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl hPoly1Val)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩)
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly2, mon2, arith_poly_denote_real]
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_denote_real_of_poly_mul_mon_rational
    (M : SmtModel) {m p : Term}
    (hm : arith_mon_rational M m)
    (hp : arith_poly_rational M p) :
  arith_poly_denote_real M (__poly_mul_mon m p) =
    __smtx_model_eval_mult (arith_mon_denote_real M m) (arith_poly_denote_real M p) := by
  have hMNe : m ≠ Term.Stuck := arith_mon_rational_ne_stuck hm
  rcases arith_mon_denote_real_rational_of_rational_support M hm with ⟨qm, hMonEq⟩
  induction hp with
  | zero =>
      rw [hMonEq]
      simp [__poly_mul_mon, arith_poly_denote_real, __smtx_model_eval_mult, native_qmult,
        native_mk_rational_zero, Rat.mul_zero]
  | @cons m2 p2 hm2 hp2 ih =>
      have hMul : arith_mon_rational M (__mon_mul_mon m m2) :=
        arith_mon_rational_of_mon_mul_mon M hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        arith_mon_rational_ne_stuck hMul
      have hHead :
          arith_poly_rational M
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_poly_zero)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (arith_poly_rational.cons
            (M := M)
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_poly_zero)
            hMul
            (arith_poly_rational.zero (M := M)))
      have hMulTail : arith_poly_rational M (__poly_mul_mon m p2) :=
        arith_poly_rational_of_poly_mul_mon M hm hp2
      have hMon2Val : ∃ q, arith_mon_denote_real M m2 = SmtValue.Rational q :=
        arith_mon_denote_real_rational_of_rational_support M hm2
      have hPoly2Val : ∃ q, arith_poly_denote_real M p2 = SmtValue.Rational q :=
        arith_poly_denote_real_rational_of_rational_support M hp2
      have hHeadEq :
          arith_poly_denote_real M
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
                (Term.UOp UserOp._at__at_poly_zero)) =
            __smtx_model_eval_mult (arith_mon_denote_real M m) (arith_mon_denote_real M m2) := by
        rcases hMon2Val with ⟨qm2, hMon2Eq⟩
        simp [arith_poly_denote_real, __eo_mk_apply, __smtx_model_eval_plus,
          native_qplus, native_mk_rational_zero]
        rw [arith_mon_denote_real_of_mon_mul_mon_rational M hm hm2, hMonEq, hMon2Eq]
        simpa [__smtx_model_eval_plus, __smtx_model_eval_mult, native_qmult,
          native_mk_rational_zero] using
          congrArg SmtValue.Rational (Rat.add_zero (qm * qm2))
      have hStep :
          arith_poly_denote_real M
              (__poly_mul_mon m
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m2) p2)) =
            __smtx_model_eval_plus
              (arith_poly_denote_real M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
                  (Term.UOp UserOp._at__at_poly_zero)))
              (arith_poly_denote_real M (__poly_mul_mon m p2)) := by
        simpa [__poly_mul_mon, hMNe] using arith_poly_denote_real_of_poly_add_rational M hHead hMulTail
      rcases hMon2Val with ⟨qm2, hMon2Eq⟩
      rcases hPoly2Val with ⟨qp2, hPoly2Eq⟩
      rw [hStep, hHeadEq, ih, hMonEq]
      simpa [arith_poly_denote_real, hMon2Eq, hPoly2Eq] using
        (smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
          qm (arith_mon_denote_real M m2) (arith_poly_denote_real M p2)
          (Or.inl ⟨qm2, hMon2Eq⟩) (Or.inl ⟨qp2, hPoly2Eq⟩))

private theorem arith_poly_denote_real_of_poly_mul_rational
    (M : SmtModel) {p1 p2 : Term}
    (hp1 : arith_poly_rational M p1)
    (hp2 : arith_poly_rational M p2) :
  arith_poly_denote_real M (__poly_mul p1 p2) =
    __smtx_model_eval_mult (arith_poly_denote_real M p1) (arith_poly_denote_real M p2) := by
  have hP2Ne : p2 ≠ Term.Stuck := arith_poly_rational_ne_stuck hp2
  rcases arith_poly_denote_real_rational_of_rational_support M hp2 with ⟨qp2, hPoly2Eq⟩
  induction hp1 with
  | zero =>
      rw [hPoly2Eq]
      simp [__poly_mul, arith_poly_denote_real, __smtx_model_eval_mult, native_qmult,
        native_mk_rational_zero, Rat.zero_mul]
  | @cons m p1 hm hp1 ih =>
      have hMulHead : arith_poly_rational M (__poly_mul_mon m p2) :=
        arith_poly_rational_of_poly_mul_mon M hm hp2
      have hMulTail : arith_poly_rational M (__poly_mul p1 p2) :=
        arith_poly_rational_of_poly_mul M hp1 hp2
      have hStep :
          arith_poly_denote_real M
              (__poly_mul (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p1) p2) =
            __smtx_model_eval_plus
              (arith_poly_denote_real M (__poly_mul_mon m p2))
              (arith_poly_denote_real M (__poly_mul p1 p2)) := by
        simpa [__poly_mul, hP2Ne] using arith_poly_denote_real_of_poly_add_rational M hMulHead hMulTail
      have hMonVal : ∃ q, arith_mon_denote_real M m = SmtValue.Rational q :=
        arith_mon_denote_real_rational_of_rational_support M hm
      have hPoly1Val : ∃ q, arith_poly_denote_real M p1 = SmtValue.Rational q :=
        arith_poly_denote_real_rational_of_rational_support M hp1
      rcases hMonVal with ⟨qm, hMonEq⟩
      rcases hPoly1Val with ⟨qp1, hPoly1Eq⟩
      rw [hStep, arith_poly_denote_real_of_poly_mul_mon_rational M hm hp2, ih, hPoly2Eq]
      simpa [arith_poly_denote_real, hMonEq, hPoly1Eq] using
        (smtx_model_eval_mult_rational_right_distrib_plus_of_rational_or_notValue
          qp2 (arith_mon_denote_real M m) (arith_poly_denote_real M p1)
          (Or.inl ⟨qm, hMonEq⟩) (Or.inl ⟨qp1, hPoly1Eq⟩))

private theorem arith_poly_denote_real_of_poly_mul_mon_const_rational
    (M : SmtModel) (q : native_Rat) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p) =
    __smtx_model_eval_mult (SmtValue.Rational q) (arith_poly_denote_real M p) := by
  induction hp with
  | zero =>
      simp [arith_const_mon, __poly_mul_mon, arith_poly_denote_real, __smtx_model_eval_mult,
        native_qmult, native_mk_rational_zero, Rat.mul_zero]
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          let mon : Term :=
            Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)
          have hVars : vars ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars
          have hHead :
              arith_poly_rational M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_poly)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational (native_qmult q c))))
                  (Term.UOp UserOp._at__at_poly_zero)) := by
            exact arith_poly_rational.cons
              (M := M)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qmult q c)))
              (Term.UOp UserOp._at__at_poly_zero)
              (arith_mon_rational.mk (M := M) vars (native_qmult q c) hvars)
              (arith_poly_rational.zero (M := M))
          have hMulTail :
              arith_poly_rational M (__poly_mul_mon (arith_const_mon q) p) :=
            arith_poly_rational_of_poly_mul_mon_const M q hp
          have hMonVal :
              ∃ qm, arith_mon_denote_real M mon = SmtValue.Rational qm := by
            simpa [mon] using
              arith_mon_denote_real_rational_of_rational_support M
                (arith_mon_rational.mk (M := M) vars c hvars)
          have hPolyVal :
              ∃ qp, arith_poly_denote_real M p = SmtValue.Rational qp :=
            arith_poly_denote_real_rational_of_rational_support M hp
          have hHeadEq :
              arith_poly_denote_real M
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_poly_zero)) =
                __smtx_model_eval_mult (SmtValue.Rational q) (arith_mon_denote_real M mon) := by
            rw [arith_poly_denote_real, arith_mon_denote_real_of_coeff_mul]
            rcases hMonVal with ⟨qm, hMonVal⟩
            simp [arith_poly_denote_real, mon, hMonVal, __smtx_model_eval_mult,
              __smtx_model_eval_plus, native_qmult, native_qplus, native_mk_rational_zero,
              Rat.add_zero]
          have hStep :
              arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_poly) mon) p)) =
                __smtx_model_eval_plus
                  (arith_poly_denote_real M
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_qmult q c))))
                      (Term.UOp UserOp._at__at_poly_zero)))
                  (arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p)) := by
            change arith_poly_denote_real M
              (__poly_add
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                    (__mon_mul_mon (arith_const_mon q) mon))
                  (Term.UOp UserOp._at__at_poly_zero))
                (__poly_mul_mon (arith_const_mon q) p)) =
              __smtx_model_eval_plus
                (arith_poly_denote_real M
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_poly_zero)))
                (arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p))
            rw [show __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                  (__mon_mul_mon (arith_const_mon q) mon))
                (Term.UOp UserOp._at__at_poly_zero) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_poly_zero) by
                  simpa [mon] using poly_of_mon_mul_mon_const_left q c vars hVars]
            exact arith_poly_denote_real_of_poly_add_rational M hHead hMulTail
          rw [hStep, hHeadEq, ih]
          rcases hMonVal with ⟨qm, hMonVal⟩
          rcases hPolyVal with ⟨qp, hPolyVal⟩
          simpa [arith_poly_denote_real, mon, hMonVal, hPolyVal] using
            (smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
              q (arith_mon_denote_real M mon) (arith_poly_denote_real M p)
              (Or.inl ⟨qm, hMonVal⟩) (Or.inl ⟨qp, hPolyVal⟩))

private theorem arith_poly_denote_real_of_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Rational q)) =
    SmtValue.Rational q := by
  by_cases hZero : q = native_mk_rational 0 1
  · subst hZero
    have hGet :
        __get_arith_poly_norm (Term.Rational (native_mk_rational 0 1)) =
          Term.UOp UserOp._at__at_poly_zero := by
      native_decide
    rw [hGet]
    rfl
  · have hZero' : ¬ native_mk_rational 0 1 = q := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = q) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Rational q) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                (Term.Rational q)))
            (Term.UOp UserOp._at__at_poly_zero) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    change SmtValue.Rational (q * native_mk_rational 1 1 + native_mk_rational 0 1) =
      SmtValue.Rational q
    congr
    have hOne : native_mk_rational 1 1 = (1 : Rat) := by
      native_decide
    have hZeroRat : native_mk_rational 0 1 = (0 : Rat) := by
      native_decide
    rw [hOne, hZeroRat]
    rw [Rat.mul_one, Rat.add_zero]

private theorem arith_poly_denote_real_of_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Numeral n)) =
    SmtValue.Rational (native_to_real n) := by
  by_cases hZero : native_to_real n = native_mk_rational 0 1
  · have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.UOp UserOp._at__at_poly_zero := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hZero, SmtEval.native_and, SmtEval.native_not]
    rw [hGet, hZero]
    rfl
  · have hZero' : ¬ native_mk_rational 0 1 = native_to_real n := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = native_to_real n) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                (Term.Rational (native_to_real n))))
            (Term.UOp UserOp._at__at_poly_zero) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    change SmtValue.Rational (native_to_real n * native_mk_rational 1 1 + native_mk_rational 0 1) =
      SmtValue.Rational (native_to_real n)
    congr
    have hOne : native_mk_rational 1 1 = (1 : Rat) := by
      native_decide
    have hZeroRat : native_mk_rational 0 1 = (0 : Rat) := by
      native_decide
    rw [hOne, hZeroRat]
    rw [Rat.mul_one, Rat.add_zero]

private theorem arith_poly_norm_atom_denote_real_of_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_norm_atom_denote_real M (Term.Rational q) = SmtValue.Rational q := by
  unfold arith_poly_norm_atom_denote_real
  rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
  simp [__smtx_model_eval, __smtx_to_real_coerce]

private theorem arith_poly_norm_atom_denote_real_of_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_norm_atom_denote_real M (Term.Numeral n) = SmtValue.Rational (native_to_real n) := by
  unfold arith_poly_norm_atom_denote_real
  rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
  simp [__smtx_model_eval, __smtx_to_real_coerce]

private theorem arith_poly_norm_atom_denote_real_of_to_real
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hInt : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.UOp UserOp.to_real) t) =
    arith_poly_norm_atom_denote_real M t := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hInt] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hInt])
  rcases int_value_canonical hEvalTy with ⟨n, hEval⟩
  unfold arith_poly_norm_atom_denote_real
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) t) =
    SmtTerm.to_real (__eo_to_smt t) by rfl]
  rw [__smtx_model_eval.eq_21, hEval]
  simp [__smtx_model_eval_to_real, __smtx_to_real_coerce]

private theorem native_to_real_neg
    (n : native_Int) :
  native_to_real (native_zneg n) = native_qneg (native_to_real n) := by
  change (-((n : Rat)) * ((1 : Rat)⁻¹)) = -((n : Rat) * ((1 : Rat)⁻¹))
  exact Rat.neg_mul _ _

private theorem native_to_real_add
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 n2) =
    native_qplus (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qplus, native_zplus,
    native_mk_rational, native_mk_rational, native_mk_rational]
  rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div, ← Rat.divInt_eq_div]
  simp [Int.mul_one]

theorem native_to_real_sub
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 (native_zneg n2)) =
    native_qplus (native_to_real n1) (native_qneg (native_to_real n2)) := by
  rw [native_to_real_add, native_to_real_neg]

private theorem native_to_real_mul
    (n1 n2 : native_Int) :
  native_to_real (native_zmult n1 n2) =
    native_qmult (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qmult, native_zmult,
    native_mk_rational, native_mk_rational, native_mk_rational]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 n2 (d₁ := 1) (d₂ := 1)).symm

private theorem native_to_real_qdiv_total
    (n1 n2 : native_Int) :
  native_qdiv_total (native_to_real n1) (native_to_real n2) =
    native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational, native_mk_rational,
    native_mk_rational]
  rw [Rat.div_def]
  have hInv : ((↑n2 / ↑(1 : Int) : Rat)⁻¹) = ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

private theorem arith_poly_norm_atom_denote_real_of_uneg
    (M : SmtModel) (t : Term) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) =
    __smtx_model_eval_uneg (arith_poly_norm_atom_denote_real M t) := by
  unfold arith_poly_norm_atom_denote_real
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) =
    SmtTerm.uneg (__eo_to_smt t) by rfl]
  cases hEval : __smtx_model_eval M (__eo_to_smt t) <;>
    simp [__smtx_model_eval, __smtx_to_real_coerce, __smtx_model_eval_uneg, hEval,
      native_to_real, native_mk_rational, native_zneg, native_qneg]
  case Numeral n =>
    change (-((n : Rat)) * ((1 : Rat)⁻¹)) = -((n : Rat) * ((1 : Rat)⁻¹))
    exact Rat.neg_mul _ _

private theorem arith_poly_norm_atom_denote_real_of_plus
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Real) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
    __smtx_model_eval_plus (arith_poly_norm_atom_denote_real M t1) (arith_poly_norm_atom_denote_real M t2) := by
  have ht : term_has_non_none_type (SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
        SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
      (typeof_plus_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
      SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_14, hEval1, hEval2]
    simp [__smtx_to_real_coerce, __smtx_model_eval_plus, native_to_real_add]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
      SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_14, hEval1, hEval2]
    simp [__smtx_to_real_coerce, __smtx_model_eval_plus]

private theorem arith_poly_norm_atom_denote_real_of_neg
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Real) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
    __smtx_model_eval_plus (arith_poly_norm_atom_denote_real M t1)
      (__smtx_model_eval_uneg (arith_poly_norm_atom_denote_real M t2)) := by
  have ht : term_has_non_none_type (SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
        SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
      SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_15, hEval1, hEval2]
    simp [__smtx_to_real_coerce, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__, native_to_real_sub]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
      SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_15, hEval1, hEval2]
    simp [__smtx_to_real_coerce, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__]

private theorem arith_poly_norm_atom_denote_real_of_mult
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Real) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
    __smtx_model_eval_mult (arith_poly_norm_atom_denote_real M t1) (arith_poly_norm_atom_denote_real M t2) := by
  have ht : term_has_non_none_type (SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
        SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
      SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_to_real_coerce,
      __smtx_model_eval_mult, native_to_real_mul]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
      SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_to_real_coerce,
      __smtx_model_eval_mult]

private theorem arith_poly_norm_atom_denote_real_of_qdiv_total
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
    __smtx_model_eval_qdiv_total (arith_poly_norm_atom_denote_real M t1) (arith_poly_norm_atom_denote_real M t2) := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
        SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
      SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_to_real_coerce,
      __smtx_model_eval_qdiv_total, native_to_real_qdiv_total]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simp [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simp [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_poly_norm_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
      SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_to_real_coerce,
      __smtx_model_eval_qdiv_total]

private def arith_atomic_poly (t : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_poly)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_mon)
          (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
        (Term.Rational (native_mk_rational 1 1))))
    (Term.UOp UserOp._at__at_poly_zero)

private theorem arith_atomic_poly_injective
    {a b : Term} :
  arith_atomic_poly a = arith_atomic_poly b ->
  a = b := by
  intro h
  simpa [arith_atomic_poly] using h

private theorem arith_mvar_rational_singleton
    (M : SmtModel) (t : Term)
    (hRat : ∃ q, arith_poly_norm_atom_denote_real M t = SmtValue.Rational q) :
  arith_mvar_rational M (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil) := by
  exact arith_mvar_rational.cons t Term.__eo_List_nil hRat (arith_mvar_rational.nil (M := M))

private theorem arith_poly_rational_of_arith_atomic_poly
    (M : SmtModel) (t : Term)
    (hRat : ∃ q, arith_poly_norm_atom_denote_real M t = SmtValue.Rational q) :
  arith_poly_rational M (arith_atomic_poly t) := by
  unfold arith_atomic_poly
  exact arith_poly_rational.cons
    (M := M)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_mon)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
      (Term.Rational (native_mk_rational 1 1)))
    (Term.UOp UserOp._at__at_poly_zero)
    (arith_mon_rational.mk
      (M := M)
      (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil)
      (native_mk_rational 1 1)
      (arith_mvar_rational_singleton M t hRat))
    (arith_poly_rational.zero (M := M))

private theorem arith_poly_denote_real_of_arith_atomic_poly
    (M : SmtModel) (t : Term) :
  arith_poly_denote_real M (arith_atomic_poly t) = arith_poly_norm_atom_denote_real M t := by
  rcases arith_poly_norm_atom_denote_real_rational_or_notValue M t with hAtom | hAtom
  · rcases hAtom with ⟨q, hAtom⟩
    rw [arith_atomic_poly, arith_poly_denote_real, arith_mon_denote_real, arith_mvar_denote_real,
      hAtom]
    simp [arith_mvar_denote_real, arith_poly_denote_real, __smtx_model_eval_mult,
      __smtx_model_eval_plus, native_qmult, native_qplus, native_mk_rational_zero,
      native_mk_rational_one, Rat.one_mul, Rat.mul_one, Rat.add_zero]
  · rw [arith_atomic_poly, arith_poly_denote_real, arith_mon_denote_real, arith_mvar_denote_real,
      hAtom]
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_poly_denote_real_eq_arith_poly_norm_atom_denote_real_of_norm_eq_atomic
    (M : SmtModel) (t : Term)
    (hNorm : __get_arith_poly_norm t = arith_atomic_poly t) :
  arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t := by
  rw [hNorm]
  exact arith_poly_denote_real_of_arith_atomic_poly M t

private theorem eo_to_smt_uneg_eq
    (x : Term) :
  __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) =
    (__eo_to_smt x).uneg := by
  rfl

private theorem eo_to_smt_to_real_eq
    (x : Term) :
  __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x) =
    (__eo_to_smt x).to_real := by
  rfl

private theorem eo_to_smt_plus_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x) =
    (__eo_to_smt y).plus (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_neg_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x) =
    (__eo_to_smt y).neg (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_mult_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x) =
    (__eo_to_smt y).mult (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_qdiv_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x) =
    (__eo_to_smt y).qdiv (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_qdiv_total_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x) =
    (__eo_to_smt y).qdiv_total (__eo_to_smt x) := by
  rfl

private theorem get_arith_poly_norm_of_non_arith_smt_type
    (t : Term)
    (hNotInt : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Int)
    (hNotReal : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Real)
    (hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
  __get_arith_poly_norm t = arith_atomic_poly t := by
  cases t with
  | Numeral n =>
      exfalso
      exact hNotInt (by
        rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
        rw [__smtx_typeof.eq_2])
  | Rational q =>
      exfalso
      exact hNotReal (by
        rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
        rw [__smtx_typeof.eq_3])
  | Stuck =>
      exfalso
      exact hNonNone (by
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
        exact TranslationProofs.smtx_typeof_none)
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;>
            try
              simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
          case __eoo_neg_2 =>
            exfalso
            have ht : term_has_non_none_type ((__eo_to_smt x).uneg) := by
              unfold term_has_non_none_type
              rw [← eo_to_smt_uneg_eq x]
              exact hNonNone
            rcases arith_unop_arg_of_non_none
                (op := SmtTerm.uneg) (t := __eo_to_smt x)
                (typeof_uneg_eq (__eo_to_smt x)) ht with hArg | hArg
            · exact hNotInt <| by
                rw [eo_to_smt_uneg_eq, typeof_uneg_eq]
                simp [__smtx_typeof_arith_overload_op_1, hArg]
            · exact hNotReal <| by
                rw [eo_to_smt_uneg_eq, typeof_uneg_eq]
                simp [__smtx_typeof_arith_overload_op_1, hArg]
          case to_real =>
            exfalso
            have ht : term_has_non_none_type ((__eo_to_smt x).to_real) := by
              unfold term_has_non_none_type
              rw [← eo_to_smt_to_real_eq x]
              exact hNonNone
            have hArg := to_real_arg_of_non_none (t := __eo_to_smt x) ht
            exact hNotReal <| by
              rw [eo_to_smt_to_real_eq, typeof_to_real_eq]
              simp [native_ite, native_Teq, hArg]
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                try
                  simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
              case plus =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.plus (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_plus_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
                    (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_plus_eq, typeof_plus_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_plus_eq, typeof_plus_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case neg =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_neg_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
                    (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_neg_eq, typeof_neg_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_neg_eq, typeof_neg_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case mult =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_mult_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
                    (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_mult_eq, typeof_mult_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_mult_eq, typeof_mult_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case qdiv =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.qdiv (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_qdiv_eq y x]
                  exact hNonNone
                rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
                    (R := SmtType.Real)
                    (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
              case qdiv_total =>
                exfalso
                have ht : term_has_non_none_type
                    ((__eo_to_smt y).qdiv_total (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_qdiv_total_eq y x]
                  exact hNonNone
                rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
                    (R := SmtType.Real)
                    (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x)) ht with
                    hArgs | hArgs
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          | _ =>
              simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
      | _ =>
          simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
            __eo_is_q_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not]
  | _ =>
      simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
        __eo_is_q_internal, __eo_ite, native_ite, native_teq,
        SmtEval.native_and, SmtEval.native_not]

private theorem non_none_of_smt_arith_type
    {t : SmtTerm}
    (hTy : __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real) :
  term_has_non_none_type t := by
  unfold term_has_non_none_type
  intro hNone
  rcases hTy with hInt | hReal
  · cases hInt.symm.trans hNone
  · cases hReal.symm.trans hNone

private theorem arith_poly_rational_of_const_poly
    (M : SmtModel) (q : native_Rat) :
  arith_poly_rational M
    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon q))
      (Term.UOp UserOp._at__at_poly_zero)) := by
  exact arith_poly_rational.cons
    (M := M)
    (arith_const_mon q)
    (Term.UOp UserOp._at__at_poly_zero)
    (arith_mon_rational.mk
      (M := M)
      Term.__eo_List_nil
      q
      (arith_mvar_rational.nil (M := M)))
    (arith_poly_rational.zero (M := M))

private theorem arith_poly_rational_of_get_arith_poly_norm_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Rational q)) := by
  by_cases hZero : q = native_mk_rational 0 1
  · subst q
    have hGet :
        __get_arith_poly_norm (Term.Rational (native_mk_rational 0 1)) =
          Term.UOp UserOp._at__at_poly_zero := by
      native_decide
    rw [hGet]
    exact arith_poly_rational.zero (M := M)
  · have hZero' : ¬ native_mk_rational 0 1 = q := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = q) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Rational q) =
          Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon q))
            (Term.UOp UserOp._at__at_poly_zero) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not,
        arith_const_mon, __eo_mk_apply]
    rw [hGet]
    exact arith_poly_rational_of_const_poly M q

private theorem arith_poly_rational_of_get_arith_poly_norm_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Numeral n)) := by
  by_cases hZero : native_to_real n = native_mk_rational 0 1
  · have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.UOp UserOp._at__at_poly_zero := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hZero, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    exact arith_poly_rational.zero (M := M)
  · have hZero' : ¬ native_mk_rational 0 1 = native_to_real n := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = native_to_real n) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon (native_to_real n)))
            (Term.UOp UserOp._at__at_poly_zero) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not,
        arith_const_mon, __eo_mk_apply]
    rw [hGet]
    exact arith_poly_rational_of_const_poly M (native_to_real n)

private theorem arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real)
    (hNorm : __get_arith_poly_norm t = arith_atomic_poly t) :
  arith_poly_rational M (__get_arith_poly_norm t) := by
  rw [hNorm]
  exact arith_poly_rational_of_arith_atomic_poly M t
    (arith_poly_norm_atom_denote_real_rational_of_smt_arith_type M hM t hTy)

private theorem arith_poly_denote_real_of_get_arith_poly_norm_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Rational q)) =
    arith_poly_norm_atom_denote_real M (Term.Rational q) := by
  rw [arith_poly_denote_real_of_rational, arith_poly_norm_atom_denote_real_of_rational]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Numeral n)) =
    arith_poly_norm_atom_denote_real M (Term.Numeral n) := by
  rw [arith_poly_denote_real_of_numeral, arith_poly_norm_atom_denote_real_of_numeral]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_to_real
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hInt : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hRec : arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) t)) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.UOp UserOp.to_real) t) := by
  simpa [__get_arith_poly_norm,
    arith_poly_norm_atom_denote_real_of_to_real M hM t hInt] using hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_to_real
    (M : SmtModel) (t : Term)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t)) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) t)) := by
  simpa [__get_arith_poly_norm] using hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_uneg
    (M : SmtModel) (t : Term)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t)) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_neg M hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_plus
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_add M hRec1 hRec2

private theorem arith_poly_rational_of_get_arith_poly_norm_neg
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) := by
  simpa [__get_arith_poly_norm] using
    arith_poly_rational_of_poly_add M hRec1 (arith_poly_rational_of_poly_neg M hRec2)

private theorem arith_poly_rational_of_get_arith_poly_norm_mult
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_mul M hRec1 hRec2

private theorem arith_poly_denote_real_of_get_arith_poly_norm_uneg
    (M : SmtModel) (t : Term)
    (hWf : arith_poly_wf (__get_arith_poly_norm t))
    (hRec : arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t)) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_neg_wf M hWf,
    arith_poly_norm_atom_denote_real_of_uneg]
  simp [hRec]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_plus
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Real)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_poly_norm_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_add_rational M hRat1 hRat2, hRec1,
    hRec2]
  exact (arith_poly_norm_atom_denote_real_of_plus M hM t1 t2 hTy).symm

private theorem arith_poly_denote_real_of_get_arith_poly_norm_neg
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Real)
    (hWf2 : arith_poly_wf (__get_arith_poly_norm t2))
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_poly_norm_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) := by
  have hNegRec :
      arith_poly_denote_real M (__poly_neg (__get_arith_poly_norm t2)) =
        __smtx_model_eval_uneg (arith_poly_norm_atom_denote_real M t2) := by
    rw [arith_poly_denote_real_of_poly_neg_wf M hWf2, hRec2]
  rw [__get_arith_poly_norm,
    arith_poly_denote_real_of_poly_add_rational M hRat1
      (arith_poly_rational_of_poly_neg M hRat2),
    hRec1, hNegRec]
  exact (arith_poly_norm_atom_denote_real_of_neg M hM t1 t2 hTy).symm

private theorem arith_poly_denote_real_of_get_arith_poly_norm_mult
    (M : SmtModel) (hM : model_wf M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Real)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_poly_norm_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_mul_rational M hRat1 hRat2, hRec1,
    hRec2]
  exact (arith_poly_norm_atom_denote_real_of_mult M hM t1 t2 hTy).symm

private theorem get_arith_poly_norm_qdiv_of_rational
    (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) q))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem get_arith_poly_norm_qdiv_total_of_rational
    (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) q))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_of_rational
    (M : SmtModel) (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q))) := by
  rw [get_arith_poly_norm_qdiv_of_rational t1 q hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) q) hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_rational
    (M : SmtModel) (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q))) := by
  rw [get_arith_poly_norm_qdiv_total_of_rational t1 q hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) q) hRec

private theorem get_arith_poly_norm_qdiv_of_numeral
    (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ native_to_real n := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem get_arith_poly_norm_qdiv_total_of_numeral
    (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ native_to_real n := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_of_numeral
    (M : SmtModel) (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n))) := by
  rw [get_arith_poly_norm_qdiv_of_numeral t1 n hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_numeral
    (M : SmtModel) (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) := by
  rw [get_arith_poly_norm_qdiv_total_of_numeral t1 n hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRec

private theorem smt_typeof_qdiv_left_of_rational_right
    (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real) :
  __smtx_typeof (__eo_to_smt t1) = SmtType.Real := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt (Term.Rational q))) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
          (Term.Rational q))) = SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt (Term.Rational q))) ht with hArgs | hArgs
  · have hQTy : __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Real := by
      rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
      rw [__smtx_typeof.eq_3]
    cases hQTy.symm.trans hArgs.2
  · exact hArgs.1

private theorem arith_poly_norm_atom_denote_real_of_qdiv_rational
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) =
    __smtx_model_eval_qdiv_total (arith_poly_norm_atom_denote_real M t1) (SmtValue.Rational q) := by
  have hT1Real : __smtx_typeof (__eo_to_smt t1) = SmtType.Real :=
    smt_typeof_qdiv_left_of_rational_right t1 q hTy
  have hEval1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        __smtx_typeof (__eo_to_smt t1) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simp [term_has_non_none_type, hT1Real])
  rcases real_value_canonical (by simpa [hT1Real] using hEval1Ty) with ⟨q1, hEval1⟩
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational q1 := by
    simp [arith_poly_norm_atom_denote_real, hEval1, __smtx_to_real_coerce]
  have hEvalQ : __smtx_model_eval M (__eo_to_smt (Term.Rational q)) = SmtValue.Rational q := by
    rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
    simp [__smtx_model_eval]
  rw [hAtom1]
  unfold arith_poly_norm_atom_denote_real
  rw [eo_to_smt_qdiv_eq, smtx_eval_qdiv_term_eq, hEvalQ, hEval1]
  simp [__smtx_to_real_coerce, __smtx_model_eval_qdiv_total, __smtx_model_eval_ite,
    __smtx_model_eval_eq, native_veq, hZero]

private theorem smt_typeof_qdiv_left_of_numeral_right
    (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real) :
  __smtx_typeof (__eo_to_smt t1) = SmtType.Int := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt (Term.Numeral n))) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
          (Term.Numeral n))) = SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt (Term.Numeral n))) ht with hArgs | hArgs
  · exact hArgs.1
  · have hNTy : __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
      rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
      rw [__smtx_typeof.eq_2]
    cases hNTy.symm.trans hArgs.2

private theorem arith_poly_norm_atom_denote_real_of_qdiv_numeral
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n ≠ native_mk_rational 0 1) :
  arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) =
    __smtx_model_eval_qdiv_total (arith_poly_norm_atom_denote_real M t1)
      (SmtValue.Rational (native_to_real n)) := by
  have hT1Int : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    smt_typeof_qdiv_left_of_numeral_right t1 n hTy
  have hEval1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        __smtx_typeof (__eo_to_smt t1) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simp [term_has_non_none_type, hT1Int])
  rcases int_value_canonical (by simpa [hT1Int] using hEval1Ty) with ⟨n1, hEval1⟩
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational (native_to_real n1) := by
    simp [arith_poly_norm_atom_denote_real, hEval1, __smtx_to_real_coerce]
  have hEvalN : __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
    rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
    simp [__smtx_model_eval]
  have hZeroTest :
      __smtx_model_eval_eq (SmtValue.Rational (native_to_real n))
        (SmtValue.Rational (native_mk_rational 0 1)) =
        SmtValue.Boolean false := by
    simp [__smtx_model_eval_eq, native_veq, hZero]
  rw [hAtom1]
  unfold arith_poly_norm_atom_denote_real
  rw [eo_to_smt_qdiv_eq]
  simp [__smtx_model_eval, hEval1, hEvalN, hZeroTest, __smtx_model_eval_ite,
    __smtx_to_real_coerce, __smtx_model_eval_qdiv_total, native_to_real_qdiv_total]

private theorem smtx_model_eval_mult_const_recip_eq_qdiv_total
    (q1 q : native_Rat) :
  __smtx_model_eval_mult
      (SmtValue.Rational (native_qdiv_total (native_mk_rational 1 1) q))
      (SmtValue.Rational q1) =
    __smtx_model_eval_qdiv_total (SmtValue.Rational q1) (SmtValue.Rational q) := by
  simp [__smtx_model_eval_mult, __smtx_model_eval_qdiv_total, native_qmult, native_qdiv_total,
    native_mk_rational_one, Rat.div_def, Rat.mul_comm]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_rational
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q))) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_of_rational t1 q hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) q) hRat1,
    hRec1]
  rw [arith_poly_norm_atom_denote_real_of_qdiv_rational M hM t1 q hTy hZero, hAtom1]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 q

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_numeral
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n))) =
    arith_poly_norm_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_of_numeral t1 n hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRat1,
    hRec1]
  rw [arith_poly_norm_atom_denote_real_of_qdiv_numeral M hM t1 n hTy hZero, hAtom1]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 (native_to_real n)

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_rational
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q))) =
    arith_poly_norm_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_total_of_rational t1 q hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) q) hRat1,
    hRec1]
  rw [arith_poly_norm_atom_denote_real_of_qdiv_total M hM t1 (Term.Rational q) hTy, hAtom1,
    arith_poly_norm_atom_denote_real_of_rational]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 q

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral
    (M : SmtModel) (hM : model_wf M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_poly_norm_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) =
    arith_poly_norm_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_poly_norm_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_total_of_numeral t1 n hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRat1,
    hRec1]
  rw [arith_poly_norm_atom_denote_real_of_qdiv_total M hM t1 (Term.Numeral n) hTy, hAtom1,
    arith_poly_norm_atom_denote_real_of_numeral]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 (native_to_real n)

private theorem smt_typeof_qdiv_of_smt_arith_type
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    rcases hTy with hInt | hReal
    · cases hInt.symm.trans hNone'
    · cases hReal.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem smt_typeof_qdiv_total_of_smt_arith_type
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_total_eq]
      exact hNone
    rcases hTy with hInt | hReal
    · cases hInt.symm.trans hNone'
    · cases hReal.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem smt_typeof_qdiv_of_qdiv_total
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_total_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral_zero
    (M : SmtModel) (_hM : model_wf M) (t1 : Term) (n : native_Int)
    (_hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n = native_mk_rational 0 1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) =
    arith_poly_norm_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
  have hNorm :
      __get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) =
        arith_atomic_poly
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
    simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
      __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, hZero,
      arith_atomic_poly]
  exact arith_poly_denote_real_eq_arith_poly_norm_atom_denote_real_of_norm_eq_atomic M _ hNorm

theorem arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M) :
    (t : Term) ->
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
    arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t := by
  intro t hTy
  let finishAtomic :
      (t : Term) ->
      (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
      (__get_arith_poly_norm t = arith_atomic_poly t) ->
      arith_poly_rational M (__get_arith_poly_norm t) ∧
        arith_poly_wf (__get_arith_poly_norm t) ∧
        arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t :=
    fun t hTy hNorm => by
      have hRat : arith_poly_rational M (__get_arith_poly_norm t) :=
        arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type M hM t hTy hNorm
      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
      exact arith_poly_denote_real_eq_arith_poly_norm_atom_denote_real_of_norm_eq_atomic M t hNorm
  let rec go (t : Term)
      (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
      arith_poly_rational M (__get_arith_poly_norm t) ∧
        arith_poly_wf (__get_arith_poly_norm t) ∧
        arith_poly_denote_real M (__get_arith_poly_norm t) = arith_poly_norm_atom_denote_real M t := by
    cases hEq : t with
    | Rational q =>
        have hRat : arith_poly_rational M (__get_arith_poly_norm (Term.Rational q)) :=
          arith_poly_rational_of_get_arith_poly_norm_rational M q
        refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
        exact arith_poly_denote_real_of_get_arith_poly_norm_rational M q
    | Numeral n =>
        have hRat : arith_poly_rational M (__get_arith_poly_norm (Term.Numeral n)) :=
          arith_poly_rational_of_get_arith_poly_norm_numeral M n
        refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
        exact arith_poly_denote_real_of_get_arith_poly_norm_numeral M n
    | Stuck =>
        have hTy' :
            __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.Real := by
          simpa [hEq] using hTy
        exfalso
        rcases hTy' with hInt | hReal
        · rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
            TranslationProofs.smtx_typeof_none] at hInt
          cases hInt
        · rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
            TranslationProofs.smtx_typeof_none] at hReal
          cases hReal
    | Apply f x =>
        have hTy :
            __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.Real := by
          simpa [hEq] using hTy
        let tApplyF := Term.Apply f x
        cases f with
        | UOp op =>
            let tUnary := Term.Apply (Term.UOp op) x
            cases op with
            | __eoo_neg_2 =>
                have ht : term_has_non_none_type ((__eo_to_smt x).uneg) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_uneg_eq x]
                  exact non_none_of_smt_arith_type hTy
                have hXTy :
                    __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
                      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
                  arith_unop_arg_of_non_none
                    (op := SmtTerm.uneg)
                    (t := __eo_to_smt x)
                    (typeof_uneg_eq (__eo_to_smt x)) ht
                rcases go x hXTy with ⟨hRatX, hWfX, hRecX⟩
                have hRat :
                    arith_poly_rational M
                      (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) :=
                  arith_poly_rational_of_get_arith_poly_norm_uneg M x hRatX
                refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                exact arith_poly_denote_real_of_get_arith_poly_norm_uneg M x hWfX hRecX
            | to_real =>
                have ht : term_has_non_none_type ((__eo_to_smt x).to_real) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_to_real_eq x]
                  exact non_none_of_smt_arith_type hTy
                have hXInt : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
                  to_real_arg_of_non_none ht
                rcases go x (Or.inl hXInt) with ⟨hRatX, _hWfX, hRecX⟩
                have hRat :
                    arith_poly_rational M
                      (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) x)) :=
                  arith_poly_rational_of_get_arith_poly_norm_to_real M x hRatX
                refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                exact arith_poly_denote_real_of_get_arith_poly_norm_to_real M hM x hXInt hRecX
            | _ =>
                have hNorm :
                    __get_arith_poly_norm tUnary =
                      arith_atomic_poly tUnary := by
                  simp [tUnary, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
                exact finishAtomic tUnary hTy hNorm
        | Apply g y =>
            let tApplyG := Term.Apply (Term.Apply g y) x
            cases g with
            | UOp op =>
                let tBinary := Term.Apply (Term.Apply (Term.UOp op) y) x
                cases op with
                | plus =>
                    have ht : term_has_non_none_type
                        (SmtTerm.plus (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_plus_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.plus)
                        (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_plus M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_plus
                        M hM y x hTy hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_plus M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_plus
                        M hM y x hTy hRatY hRatX hRecY hRecX
                | neg =>
                    have ht : term_has_non_none_type
                        (SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_neg_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.neg)
                        (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_neg M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_neg
                        M hM y x hTy hWfX hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_neg M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_neg
                        M hM y x hTy hWfX hRatY hRatX hRecY hRecX
                | mult =>
                    have ht : term_has_non_none_type
                        (SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_mult_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.mult)
                        (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_mult M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_mult
                        M hM y x hTy hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_mult M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_mult
                        M hM y x hTy hRatY hRatX hRecY hRecX
                | qdiv =>
                    let tQdiv := Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x
                    have hQdivTy :
                        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x)) =
                          SmtType.Real :=
                      smt_typeof_qdiv_of_smt_arith_type y x hTy
                    cases x with
                    | Rational q =>
                        by_cases hZero : q = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, hZero,
                              arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q))
                            hTy hNorm
                        · rcases go y (Or.inr (smt_typeof_qdiv_left_of_rational_right y q hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_of_rational M y q hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_rational
                            M hM y q hQdivTy hZero hRatY hRecY
                    | Numeral n =>
                        by_cases hZero : native_to_real n = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, hZero,
                              arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n))
                            hTy hNorm
                        · rcases go y (Or.inl (smt_typeof_qdiv_left_of_numeral_right y n hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_of_numeral M y n hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_numeral
                            M hM y n hQdivTy hZero hRatY hRecY
                    | _ =>
                        have hNorm :
                            __get_arith_poly_norm tQdiv =
                              arith_atomic_poly tQdiv := by
                          simp [tQdiv, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                            __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                            SmtEval.native_and, SmtEval.native_not]
                        exact finishAtomic tQdiv hTy hNorm
                | qdiv_total =>
                    let tQdivTotal := Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x
                    have hQdivTotalTy :
                        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x)) =
                          SmtType.Real :=
                      smt_typeof_qdiv_total_of_smt_arith_type y x hTy
                    cases x with
                    | Rational q =>
                        by_cases hZero : q = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, hZero,
                              arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q))
                            hTy hNorm
                        · have hQdivTy :
                              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y)
                                (Term.Rational q))) = SmtType.Real :=
                            smt_typeof_qdiv_of_qdiv_total y (Term.Rational q) hQdivTotalTy
                          rcases go y (Or.inr (smt_typeof_qdiv_left_of_rational_right y q hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_rational M y q hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_rational
                            M hM y q hQdivTotalTy hZero hRatY hRecY
                    | Numeral n =>
                        by_cases hZero : native_to_real n = native_mk_rational 0 1
                        · have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type
                              M hM
                              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))
                              hTy
                              (by
                                simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                                  __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                                  SmtEval.native_not, SmtEval.native_and, hZero,
                                  arith_atomic_poly])
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral_zero
                            M hM y n hQdivTotalTy hZero
                        · have hQdivTy :
                              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y)
                                (Term.Numeral n))) = SmtType.Real :=
                            smt_typeof_qdiv_of_qdiv_total y (Term.Numeral n) hQdivTotalTy
                          rcases go y (Or.inl (smt_typeof_qdiv_left_of_numeral_right y n hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_numeral M y n hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral
                            M hM y n hQdivTotalTy hZero hRatY hRecY
                    | _ =>
                        have hNorm :
                            __get_arith_poly_norm tQdivTotal =
                              arith_atomic_poly tQdivTotal := by
                          simp [tQdivTotal, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                            __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                            SmtEval.native_and, SmtEval.native_not]
                        exact finishAtomic
                          tQdivTotal hTy hNorm
                | _ =>
                    have hNorm :
                        __get_arith_poly_norm tBinary = arith_atomic_poly tBinary := by
                      simp [tBinary, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                        __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                        SmtEval.native_and, SmtEval.native_not]
                    exact finishAtomic tBinary hTy hNorm
            | _ =>
                have hNorm :
                    __get_arith_poly_norm tApplyG =
                      arith_atomic_poly tApplyG := by
                  simp [tApplyG, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
                exact finishAtomic tApplyG hTy hNorm
        | _ =>
            have hNorm :
                __get_arith_poly_norm tApplyF = arith_atomic_poly tApplyF := by
              simp [tApplyF, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
            exact finishAtomic tApplyF hTy hNorm
    | _ =>
        have hTy' :
            __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
          simpa [hEq] using hTy
        have hNorm : __get_arith_poly_norm t = arith_atomic_poly t := by
          simp [hEq, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
            __eo_is_q_internal, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not]
        simpa [hEq] using finishAtomic t hTy' hNorm
  exact (go t hTy).2.2

private theorem smt_value_rel_of_eq_arith_poly_norm_atom_denote_real_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
    __smtx_typeof (__eo_to_smt a) = SmtType.Real) ->
  arith_poly_norm_atom_denote_real M a = arith_poly_norm_atom_denote_real M b ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hArithTy hAtomEq
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with ⟨hTy, hNonNoneA⟩
  have hNonNoneB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
    rw [← hTy]
    exact hNonNoneA
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        __smtx_typeof (__eo_to_smt a) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
      (by simpa [term_has_non_none_type] using hNonNoneA)
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt b) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt b)
      (by simpa [term_has_non_none_type] using hNonNoneB)
  rcases hArithTy with hAInt | hAReal
  · have hBInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int := by
      exact hTy.symm.trans hAInt
    have hEvalAInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) = SmtType.Int := by
      simpa [hAInt] using hEvalATy
    have hEvalBInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) = SmtType.Int := by
      simpa [hBInt] using hEvalBTy
    rcases int_value_canonical hEvalAInt with ⟨nA, hEvalA⟩
    rcases int_value_canonical hEvalBInt with ⟨nB, hEvalB⟩
    have hToRealEq :
        __smtx_to_real_coerce (SmtValue.Numeral nA) =
          __smtx_to_real_coerce (SmtValue.Numeral nB) := by
      simpa [arith_poly_norm_atom_denote_real, hEvalA, hEvalB] using hAtomEq
    have hValEq : SmtValue.Numeral nA = SmtValue.Numeral nB := by
      simpa [smtx_model_eval_to_int_to_real_of_numeral] using
        congrArg __smtx_model_eval_to_int hToRealEq
    cases hValEq
    simpa [hEvalA, hEvalB] using RuleProofs.smt_value_rel_refl (SmtValue.Numeral nA)
  · have hBReal : __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
      exact hTy.symm.trans hAReal
    have hEvalAReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) = SmtType.Real := by
      simpa [hAReal] using hEvalATy
    have hEvalBReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) = SmtType.Real := by
      simpa [hBReal] using hEvalBTy
    rcases real_value_canonical hEvalAReal with ⟨qA, hEvalA⟩
    rcases real_value_canonical hEvalBReal with ⟨qB, hEvalB⟩
    have hToRealEq :
        __smtx_to_real_coerce (SmtValue.Rational qA) =
          __smtx_to_real_coerce (SmtValue.Rational qB) := by
      simpa [arith_poly_norm_atom_denote_real, hEvalA, hEvalB] using hAtomEq
    have hValEq : SmtValue.Rational qA = SmtValue.Rational qB := by
      simpa [__smtx_to_real_coerce] using hToRealEq
    cases hValEq
    simpa [hEvalA, hEvalB] using RuleProofs.smt_value_rel_refl (SmtValue.Rational qA)

private theorem smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
    __smtx_typeof (__eo_to_smt a) = SmtType.Real) ->
  __get_arith_poly_norm a = __get_arith_poly_norm b ->
  __get_arith_poly_norm a ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hArithTy hNormEq _hNormNotStuck
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with ⟨hTy, _hNonNoneA⟩
  have hBArithTy :
      __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hArithTy with hAInt | hAReal
    · exact Or.inl (hTy.symm.trans hAInt)
    · exact Or.inr (hTy.symm.trans hAReal)
  have hDenoteA :
      arith_poly_denote_real M (__get_arith_poly_norm a) = arith_poly_norm_atom_denote_real M a :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type M hM a hArithTy
  have hDenoteB :
      arith_poly_denote_real M (__get_arith_poly_norm b) = arith_poly_norm_atom_denote_real M b :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type M hM b hBArithTy
  have hAtomEq : arith_poly_norm_atom_denote_real M a = arith_poly_norm_atom_denote_real M b := by
    calc
      arith_poly_norm_atom_denote_real M a =
          arith_poly_denote_real M (__get_arith_poly_norm a) := hDenoteA.symm
      _ = arith_poly_denote_real M (__get_arith_poly_norm b) := by rw [hNormEq]
      _ = arith_poly_norm_atom_denote_real M b := hDenoteB
  exact smt_value_rel_of_eq_arith_poly_norm_atom_denote_real_of_smt_arith_type
    M hM a b hEqTrans hArithTy hAtomEq

private theorem smt_value_rel_of_equal_arith_poly_norm
    (M : SmtModel) (hM : model_wf M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  __get_arith_poly_norm a = __get_arith_poly_norm b ->
  __get_arith_poly_norm a ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hNormEq _hNormNotStuck
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with
    ⟨hTy, hNonNone⟩
  by_cases hInt : __smtx_typeof (__eo_to_smt a) = SmtType.Int
  · exact smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
      M hM a b hEqTrans (Or.inl hInt) hNormEq _hNormNotStuck
  · by_cases hReal : __smtx_typeof (__eo_to_smt a) = SmtType.Real
    · exact smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
        M hM a b hEqTrans (Or.inr hReal) hNormEq _hNormNotStuck
    · have hNotIntB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Int := by
        intro hIntB
        exact hInt (hTy.trans hIntB)
      have hNotRealB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Real := by
        intro hRealB
        exact hReal (hTy.trans hRealB)
      have hNormA :
          __get_arith_poly_norm a = arith_atomic_poly a :=
        get_arith_poly_norm_of_non_arith_smt_type a hInt hReal hNonNone
      have hNormB :
          __get_arith_poly_norm b = arith_atomic_poly b := by
        have hNonNoneB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
          rw [← hTy]
          exact hNonNone
        exact get_arith_poly_norm_of_non_arith_smt_type b hNotIntB hNotRealB hNonNoneB
      have hEqTerms : a = b := by
        apply arith_atomic_poly_injective
        rw [← hNormA, ← hNormB]
        exact hNormEq
      subst a
      exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt b))

theorem facts___eo_prog_arith_poly_norm_impl
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_poly_norm a1) true := by
  intro hA1Trans hResultTy
  obtain ⟨a, b, rfl, hNormEq, hNormNotStuck⟩ :=
    eq_args_of_prog_arith_poly_norm_typeof_bool a1 hResultTy
  have hNormNotStuckB : __get_arith_poly_norm b ≠ Term.Stuck := by
    intro hNB
    apply hNormNotStuck
    rw [hNormEq]
    exact hNB
  have hProgEq :
      __eo_prog_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
    simp [__eo_prog_arith_poly_norm, __eo_requires, hNormEq,
      hNormNotStuckB, native_ite, native_teq, native_not, SmtEval.native_not]
  have hEqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hA1Trans hEqTy
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M a b hEqBool
    (smt_value_rel_of_equal_arith_poly_norm M hM a b hA1Trans hNormEq hNormNotStuck)
