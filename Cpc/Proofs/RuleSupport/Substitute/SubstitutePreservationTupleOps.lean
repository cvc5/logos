module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationUOp1
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationUOp1

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

private theorem substitute_tuple_prepend_rec_ne_dt_sel
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
      ∀ s d i j,
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
          SmtTerm.DtSel s d i j
  | native_nat_zero, acc, hAcc, s, d, i, j => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i j
  | native_nat_succ k, acc, hAcc, s, d, i, j => by
      simp [__eo_to_smt_tuple_prepend_rec,
        substitute_tuple_prepend_rec_ne_dt_sel tailDD tailD tail k acc hAcc]

private theorem substitute_tuple_prepend_rec_ne_dt_tester
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
      ∀ s d i,
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
          SmtTerm.DtTester s d i
  | native_nat_zero, acc, hAcc, s, d, i => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i
  | native_nat_succ k, acc, hAcc, s, d, i => by
      simp [__eo_to_smt_tuple_prepend_rec,
        substitute_tuple_prepend_rec_ne_dt_tester tailDD tailD tail k acc hAcc]

private theorem substitute_tuple_prepend_rec_type_congr
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail tail' acc acc' : SmtTerm)
    (hTail : __smtx_typeof tail = __smtx_typeof tail')
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hAcc'Sel : ∀ s d i j, acc' ≠ SmtTerm.DtSel s d i j)
    (hAcc'Tester : ∀ s d i, acc' ≠ SmtTerm.DtTester s d i)
    (hAcc : __smtx_typeof acc = __smtx_typeof acc') :
    ∀ k,
      __smtx_typeof (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
        __smtx_typeof (__eo_to_smt_tuple_prepend_rec tailDD tailD tail' k acc')
  | native_nat_zero => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc
  | native_nat_succ k => by
      let recTerm := __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc
      let recTerm' := __eo_to_smt_tuple_prepend_rec tailDD tailD tail' k acc'
      let argTerm :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD
          native_nat_zero k) tail
      let argTerm' :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD
          native_nat_zero k) tail'
      have hRecTy : __smtx_typeof recTerm = __smtx_typeof recTerm' := by
        simpa [recTerm, recTerm'] using
          substitute_tuple_prepend_rec_type_congr tailDD tailD tail tail' acc acc'
            hTail hAccSel hAccTester hAcc'Sel hAcc'Tester hAcc k
      have hArgTy : __smtx_typeof argTerm = __smtx_typeof argTerm' := by
        simp [argTerm, argTerm', __smtx_typeof, hTail]
      have hGen : generic_apply_type recTerm argTerm :=
        generic_apply_type_of_non_datatype_head
          (by
            intro s d i j h
            exact
              substitute_tuple_prepend_rec_ne_dt_sel tailDD tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              substitute_tuple_prepend_rec_ne_dt_tester tailDD tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      have hGen' : generic_apply_type recTerm' argTerm' :=
        generic_apply_type_of_non_datatype_head
          (by
            intro s d i j h
            exact
              substitute_tuple_prepend_rec_ne_dt_sel tailDD tailD tail' k acc'
                hAcc'Sel s d i j (by simpa [recTerm'] using h))
          (by
            intro s d i h
            exact
              substitute_tuple_prepend_rec_ne_dt_tester tailDD tailD tail' k acc'
                hAcc'Tester s d i (by simpa [recTerm'] using h))
      unfold generic_apply_type at hGen hGen'
      change
        __smtx_typeof (SmtTerm.Apply recTerm argTerm) =
          __smtx_typeof (SmtTerm.Apply recTerm' argTerm')
      rw [hGen, hGen', hRecTy, hArgTy]

private theorem substitute_tuple_prepend_type_congr
    (head head' tail tail' : SmtTerm) (headTy headTy' : SmtType) :
    __smtx_typeof head = __smtx_typeof head' ->
    headTy = headTy' ->
    __smtx_typeof tail = __smtx_typeof tail' ->
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
        __smtx_typeof (__eo_to_smt_tuple_prepend head' headTy' tail') := by
  intro hHead hHeadTy hTail
  subst headTy'
  unfold __eo_to_smt_tuple_prepend
  rw [← hTail]
  cases hTailTy : __smtx_typeof tail with
  | Datatype s dd =>
      cases dd with
      | nil =>
          simp [__eo_to_smt_tuple_prepend_of_type]
      | cons s2 d rest =>
          cases rest with
          | cons s3 d3 rest3 =>
              simp [__eo_to_smt_tuple_prepend_of_type]
          | nil =>
              cases d with
              | null =>
                  simp [__eo_to_smt_tuple_prepend_of_type]
              | sum c dTail =>
                  cases dTail with
                  | sum c2 d2 =>
                      simp [__eo_to_smt_tuple_prepend_of_type]
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          let tailD := SmtDatatype.sum c SmtDatatype.null
                          let tailDD := __eo_to_smt_tuple_decl tailD
                          let fullD :=
                            SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                              SmtDatatype.null
                          let fullDD := __eo_to_smt_tuple_decl fullD
                          let seed :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
                                native_nat_zero) head
                          let seed' :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
                                native_nat_zero) head'
                          cases hWf :
                              __smtx_type_wf
                                (SmtType.Datatype
                                  (native_string_lit "@Tuple") fullDD)
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_and, native_streq, hWf, fullD, fullDD]
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_and, native_streq, hWf, fullD, fullDD]
                            exact
                              substitute_tuple_prepend_rec_type_congr
                                tailDD tailD tail tail' seed seed' hTail
                                (by intro s d i j h; simp [seed] at h)
                                (by intro s d i h; simp [seed] at h)
                                (by intro s d i j h; simp [seed'] at h)
                                (by intro s d i h; simp [seed'] at h)
                                (by simp [seed, seed', __smtx_typeof, hHead])
                                (__smtx_dt_num_sels tailD native_nat_zero)
                        · simp [__eo_to_smt_tuple_prepend_of_type, hs2,
                            native_streq, native_and, native_ite]
                      · simp [__eo_to_smt_tuple_prepend_of_type, hs,
                          native_streq, native_and, native_ite]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type]

private theorem substitute_smt_apply_same_head_type_congr
    (f x y : SmtTerm) :
    __smtx_typeof x = __smtx_typeof y ->
      __smtx_typeof (SmtTerm.Apply f x) =
        __smtx_typeof (SmtTerm.Apply f y) := by
  intro h
  cases f <;> simp [__smtx_typeof, __smtx_typeof_apply, h]

private theorem substitute_updater_rec_type_congr
    (sel : SmtTerm) (n : native_Nat)
    (t u acc t' u' : SmtTerm) :
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_updater_rec sel n t u acc) =
        __smtx_typeof (__eo_to_smt_updater_rec sel n t' u' acc) := by
  intro ht hu
  induction n generalizing acc with
  | zero =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
  | succ k ih =>
      cases sel <;> simp [__eo_to_smt_updater_rec]
      case DtSel s d i j =>
        have hArg :
            __smtx_typeof
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) =
              __smtx_typeof
                (native_ite (native_nateq j k) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t')) := by
          cases hEq : native_nateq j k <;>
            simp [native_ite, ht, hu, __smtx_typeof,
              __smtx_typeof_apply]
        cases k with
        | zero =>
            simpa [__eo_to_smt_updater_rec] using
              substitute_smt_apply_same_head_type_congr acc
                (native_ite (native_nateq j 0) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t))
                (native_ite (native_nateq j 0) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t')) hArg
        | succ k' =>
            have hGeneric :
                generic_apply_type
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t u acc)
                  (native_ite (native_nateq j (Nat.succ k')) u
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t)) :=
              generic_apply_type_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            have hGeneric' :
                generic_apply_type
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t' u' acc)
                  (native_ite (native_nateq j (Nat.succ k')) u'
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t')) :=
              generic_apply_type_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            unfold generic_apply_type at hGeneric hGeneric'
            rw [hGeneric, hGeneric']
            rw [ih acc]
            rw [hArg]

private theorem substitute_updater_type_congr
    (sel t u t' u' : SmtTerm) :
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_updater sel t u) =
        __smtx_typeof (__eo_to_smt_updater sel t' u') := by
  intro ht hu
  cases sel <;> simp [__eo_to_smt_updater]
  case DtSel s d i j =>
    cases hGuard :
        native_zlt (native_nat_to_int j)
          (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s d) i))
    · simp [native_ite, hGuard]
    · simp [native_ite, hGuard]
      rw [typeof_ite_eq, typeof_ite_eq]
      have hCond :
          __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) t) =
            __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) t') := by
        simp [__smtx_typeof, __smtx_typeof_apply, ht]
      have hThen :
          __smtx_typeof
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i)) =
            __smtx_typeof
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t' u' (SmtTerm.DtCons s d i)) :=
        substitute_updater_rec_type_congr
          (SmtTerm.DtSel s d i j)
          (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
          t u (SmtTerm.DtCons s d i) t' u' ht hu
      rw [hCond, hThen, ht]

private theorem substitute_tuple_update_type_congr
    (T T' : SmtType) (idx t u t' u' : SmtTerm) :
    T = T' ->
    __smtx_typeof t = __smtx_typeof t' ->
    __smtx_typeof u = __smtx_typeof u' ->
      __smtx_typeof (__eo_to_smt_tuple_update T idx t u) =
        __smtx_typeof (__eo_to_smt_tuple_update T' idx t' u') := by
  intro hT ht hu
  subst T'
  cases T <;> cases idx <;> simp [__eo_to_smt_tuple_update]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp [__eo_to_smt_tuple_update]
    | cons s2 d rest =>
        cases rest with
        | cons s3 d3 rest3 =>
            simp [__eo_to_smt_tuple_update]
        | nil =>
            by_cases hs : s = native_string_lit "@Tuple"
            · subst s
              by_cases hs2 : s2 = native_string_lit "@Tuple"
              · subst s2
                cases hNonneg : native_zleq 0 n
                · simp [native_ite, native_and, native_streq, hNonneg]
                · simp [native_ite, native_and, native_streq, hNonneg]
                  exact substitute_updater_type_congr
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl d) native_nat_zero
                      (native_int_to_nat n))
                    t u t' u' ht hu
              · simp [__eo_to_smt_tuple_update, native_ite, native_and,
                  native_streq, hs2]
            · simp [__eo_to_smt_tuple_update, native_ite, native_and,
                native_streq, hs]
theorem substitute_simul_tuple_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.tuple) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)
          xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp UserOp.tuple) xs ts bvs =
        Term.UOp UserOp.tuple :=
    substitute_simul_rec_uop_eq_self UserOp.tuple xs ts bvs
      hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.tuple) x) xs ts bvs =
        __eo_mk_apply (Term.UOp UserOp.tuple) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp UserOp.tuple) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)
          xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.tuple) xSub)
          ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp UserOp.tuple) x) y
        xs ts bvs hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.tuple) xSub)
            ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.tuple) xSub)
          ySub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.tuple) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.tuple) xSub =
        Term.Apply (Term.UOp UserOp.tuple) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.tuple) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub)
        ySub) ≠ Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases tuple_args_have_smt_translation_of_has_smt_translation hFTransEo with
    ⟨hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hXSubTy : __eo_typeof xSub ≠ Term.Stuck := by
    intro hXStuck
    apply hTyApply
    change __eo_typeof_tuple (__eo_typeof xSub) (__eo_typeof ySub) =
      Term.Stuck
    rw [hXStuck]
    exact SubstituteSupport.eo_typeof_tuple_stuck_left (__eo_typeof ySub)
  have hYSubTy : __eo_typeof ySub ≠ Term.Stuck := by
    intro hYStuck
    apply hTyApply
    change __eo_typeof_tuple (__eo_typeof xSub) (__eo_typeof ySub) =
      Term.Stuck
    rw [hYStuck]
    exact SubstituteSupport.eo_typeof_tuple_stuck_right (__eo_typeof xSub)
  have hXBoth := hRecX hXTrans hXSubTy
  have hYBoth := hRecY hYTrans hYSubTy
  have hTypeApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub)
        ySub) =
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) := by
    change __eo_typeof_tuple (__eo_typeof xSub) (__eo_typeof ySub) =
      __eo_typeof_tuple (__eo_typeof x) (__eo_typeof y)
    rw [hXBoth.1, hYBoth.1]
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hOuterMk]
    exact hTypeApply
  · have hOrigNN :
        __smtx_typeof
            (__eo_to_smt_tuple_prepend (__eo_to_smt x)
              (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)) ≠
          SmtType.None := by
      unfold RuleProofs.eo_has_smt_translation at hFTrans
      change
        __smtx_typeof
            (__eo_to_smt_tuple_prepend (__eo_to_smt x)
              (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)) ≠
          SmtType.None at hFTrans
      exact hFTrans
    have hXSmtEq :
        __smtx_typeof (__eo_to_smt xSub) =
          __smtx_typeof (__eo_to_smt x) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation xSub hXBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
      rw [hSubMatch, hOrigMatch, hXBoth.1]
    have hYSmtEq :
        __smtx_typeof (__eo_to_smt ySub) =
          __smtx_typeof (__eo_to_smt y) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation ySub hYBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
      rw [hSubMatch, hOrigMatch, hYBoth.1]
    have hTupleTyEq :
        __smtx_typeof
            (__eo_to_smt_tuple_prepend (__eo_to_smt xSub)
              (__smtx_typeof (__eo_to_smt xSub)) (__eo_to_smt ySub)) =
          __smtx_typeof
            (__eo_to_smt_tuple_prepend (__eo_to_smt x)
              (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)) :=
      substitute_tuple_prepend_type_congr
        (__eo_to_smt xSub) (__eo_to_smt x)
        (__eo_to_smt ySub) (__eo_to_smt y)
        (__smtx_typeof (__eo_to_smt xSub))
        (__smtx_typeof (__eo_to_smt x))
        hXSmtEq hXSmtEq hYSmtEq
    rw [hSubstEq, hInnerMk, hOuterMk]
    unfold RuleProofs.eo_has_smt_translation
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt xSub)
            (__smtx_typeof (__eo_to_smt xSub)) (__eo_to_smt ySub)) ≠
        SmtType.None
    rw [hTupleTyEq]
    exact hOrigNN

theorem substitute_simul_uop1_update_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp1 UserOp1.update idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 UserOp1.update idx) xs ts bvs =
        Term.UOp1 UserOp1.update idx :=
    substitute_simul_rec_uop1_eq_self UserOp1.update idx xs ts bvs
      hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.update idx) x) xs ts bvs =
        __eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp1 UserOp1.update idx) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ts bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp1 UserOp1.update idx) x) y
        xs ts bvs hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub)
          ySub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 UserOp1.update idx) xSub =
        Term.Apply (Term.UOp1 UserOp1.update idx) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp1 UserOp1.update idx) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp1 UserOp1.update idx) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp1 UserOp1.update idx) xSub) ySub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases update_index_sel_and_args_have_smt_translation hFTransEo with
    ⟨_hIdx, hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hXSubTy : __eo_typeof xSub ≠ Term.Stuck := by
    intro hXStuck
    apply hTyApply
    change __eo_typeof_update (__eo_typeof idx) (__eo_typeof xSub)
      (__eo_typeof ySub) = Term.Stuck
    rw [hXStuck]
    cases __eo_typeof idx <;> rfl
  have hYSubTy : __eo_typeof ySub ≠ Term.Stuck := by
    intro hYStuck
    apply hTyApply
    change __eo_typeof_update (__eo_typeof idx) (__eo_typeof xSub)
      (__eo_typeof ySub) = Term.Stuck
    rw [hYStuck]
    cases __eo_typeof idx <;> cases __eo_typeof xSub <;> rfl
  have hXBoth := hRecX hXTrans hXSubTy
  have hYBoth := hRecY hYTrans hYSubTy
  have hTypeApply :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) xSub) ySub) =
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y) := by
    change __eo_typeof_update (__eo_typeof idx) (__eo_typeof xSub)
      (__eo_typeof ySub) =
        __eo_typeof_update (__eo_typeof idx) (__eo_typeof x) (__eo_typeof y)
    rw [hXBoth.1, hYBoth.1]
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hOuterMk]
    exact hTypeApply
  · have hOrigNN :
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
              (__eo_to_smt y)) ≠
          SmtType.None := by
      unfold RuleProofs.eo_has_smt_translation at hFTrans
      change
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
              (__eo_to_smt y)) ≠
          SmtType.None at hFTrans
      exact hFTrans
    have hXSmtEq :
        __smtx_typeof (__eo_to_smt xSub) =
          __smtx_typeof (__eo_to_smt x) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation xSub hXBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
      rw [hSubMatch, hOrigMatch, hXBoth.1]
    have hYSmtEq :
        __smtx_typeof (__eo_to_smt ySub) =
          __smtx_typeof (__eo_to_smt y) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation ySub hYBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
      rw [hSubMatch, hOrigMatch, hYBoth.1]
    have hUpdateTyEq :
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt xSub)
              (__eo_to_smt ySub)) =
          __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
              (__eo_to_smt y)) :=
      substitute_updater_type_congr
        (__eo_to_smt idx) (__eo_to_smt xSub) (__eo_to_smt ySub)
        (__eo_to_smt x) (__eo_to_smt y) hXSmtEq hYSmtEq
    rw [hSubstEq, hInnerMk, hOuterMk]
    unfold RuleProofs.eo_has_smt_translation
    change
      __smtx_typeof
          (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt xSub)
            (__eo_to_smt ySub)) ≠
        SmtType.None
    rw [hUpdateTyEq]
    exact hOrigNN

theorem substitute_simul_uop1_tuple_update_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 UserOp1.tuple_update idx) xs ts bvs =
        Term.UOp1 UserOp1.tuple_update idx :=
    substitute_simul_rec_uop1_eq_self UserOp1.tuple_update idx xs ts bvs
      hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) xs ts bvs =
        __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp1 UserOp1.tuple_update idx) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ts bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y
        xs ts bvs hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub)
            ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub)
          ySub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx) xSub =
        Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp1 UserOp1.tuple_update idx) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub)
          ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub) ySub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases tuple_update_index_nat_valid_and_args_have_smt_translation
      hFTransEo with
    ⟨_hIdx, hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hXSubTy : __eo_typeof xSub ≠ Term.Stuck := by
    intro hXStuck
    apply hTyApply
    change __eo_typeof_tuple_update (__eo_typeof idx) idx
      (__eo_typeof xSub) (__eo_typeof ySub) = Term.Stuck
    rw [hXStuck]
    cases __eo_typeof idx <;> cases idx <;> rfl
  have hYSubTy : __eo_typeof ySub ≠ Term.Stuck := by
    intro hYStuck
    apply hTyApply
    change __eo_typeof_tuple_update (__eo_typeof idx) idx
      (__eo_typeof xSub) (__eo_typeof ySub) = Term.Stuck
    rw [hYStuck]
    cases __eo_typeof idx <;> cases idx <;> cases __eo_typeof xSub <;> rfl
  have hXBoth := hRecX hXTrans hXSubTy
  have hYBoth := hRecY hYTrans hYSubTy
  have hTypeApply :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) xSub) ySub) =
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y) := by
    change __eo_typeof_tuple_update (__eo_typeof idx) idx
      (__eo_typeof xSub) (__eo_typeof ySub) =
        __eo_typeof_tuple_update (__eo_typeof idx) idx
          (__eo_typeof x) (__eo_typeof y)
    rw [hXBoth.1, hYBoth.1]
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hOuterMk]
    exact hTypeApply
  · have hOrigNN :
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
              (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y)) ≠
          SmtType.None := by
      unfold RuleProofs.eo_has_smt_translation at hFTrans
      change
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
              (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y)) ≠
          SmtType.None at hFTrans
      exact hFTrans
    have hXSmtEq :
        __smtx_typeof (__eo_to_smt xSub) =
          __smtx_typeof (__eo_to_smt x) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation xSub hXBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
      rw [hSubMatch, hOrigMatch, hXBoth.1]
    have hYSmtEq :
        __smtx_typeof (__eo_to_smt ySub) =
          __smtx_typeof (__eo_to_smt y) := by
      have hSubMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation ySub hYBoth.2
      have hOrigMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
      rw [hSubMatch, hOrigMatch, hYBoth.1]
    have hTupleUpdateTyEq :
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt xSub))
              (__eo_to_smt idx) (__eo_to_smt xSub) (__eo_to_smt ySub)) =
          __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
              (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y)) :=
      substitute_tuple_update_type_congr
        (__smtx_typeof (__eo_to_smt xSub))
        (__smtx_typeof (__eo_to_smt x))
        (__eo_to_smt idx) (__eo_to_smt xSub) (__eo_to_smt ySub)
        (__eo_to_smt x) (__eo_to_smt y)
        hXSmtEq hXSmtEq hYSmtEq
    rw [hSubstEq, hInnerMk, hOuterMk]
    unfold RuleProofs.eo_has_smt_translation
    change
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt xSub))
            (__eo_to_smt idx) (__eo_to_smt xSub) (__eo_to_smt ySub)) ≠
        SmtType.None
    rw [hTupleUpdateTyEq]
    exact hOrigNN


/-! ### `tuple.project` -/

theorem substitute_tuple_select_type_congr_proj
    (T : SmtType) (idx x y : SmtTerm)
    (hTy : __smtx_typeof x = __smtx_typeof y) :
    __smtx_typeof (__eo_to_smt_tuple_select T idx x) =
      __smtx_typeof (__eo_to_smt_tuple_select T idx y) := by
  cases T <;> cases idx <;>
    try simp [__eo_to_smt_tuple_select]
  case Datatype.Numeral s dd n =>
    cases dd with
    | nil =>
        simp
    | cons s2 body rest =>
        cases rest with
        | nil =>
            cases hc :
                native_and
                  (native_and (native_streq s (native_string_lit "@Tuple"))
                    (native_streq s2 (native_string_lit "@Tuple")))
                  (native_zleq 0 n) <;>
              simp [native_ite, hc, __smtx_typeof, hTy]
        | cons s3 body3 rest3 =>
            simp

theorem substitute_tuple_project_rec_type_congr
    (T : SmtType) (x y : SmtTerm) (hTy : __smtx_typeof x = __smtx_typeof y) :
    (k : Nat) → (is : Term) → sizeOf is < k →
      __smtx_typeof (__eo_to_smt_tuple_project_rec is T x) =
        __smtx_typeof (__eo_to_smt_tuple_project_rec is T y)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, is, h => by
      by_cases hc : ∃ n is', is =
          Term.Apply (Term.Apply Term.__eo_List_cons (Term.Numeral n)) is'
      · obtain ⟨n, is', rfl⟩ := hc
        change
          __smtx_typeof
              (__eo_to_smt_tuple_prepend (__eo_to_smt_tuple_select T (SmtTerm.Numeral n) x)
                (__smtx_typeof (__eo_to_smt_tuple_select T (SmtTerm.Numeral n) x))
                (__eo_to_smt_tuple_project_rec is' T x)) =
            __smtx_typeof
              (__eo_to_smt_tuple_prepend (__eo_to_smt_tuple_select T (SmtTerm.Numeral n) y)
                (__smtx_typeof (__eo_to_smt_tuple_select T (SmtTerm.Numeral n) y))
                (__eo_to_smt_tuple_project_rec is' T y))
        have hSel := substitute_tuple_select_type_congr_proj T (SmtTerm.Numeral n) x y hTy
        exact substitute_tuple_prepend_type_congr _ _ _ _ _ _ hSel hSel
          (substitute_tuple_project_rec_type_congr T x y hTy k is' (by simp at h; omega))
      · by_cases hn : is = Term.__eo_List_nil
        · subst hn
          rfl
        · rw [TranslationProofs.tuple_project_rec_eq_none_of_not_list hn hc,
            TranslationProofs.tuple_project_rec_eq_none_of_not_list hn hc]

theorem substitute_tuple_project_type_congr
    (is : Term) (T : SmtType) (x y : SmtTerm) (hTy : __smtx_typeof x = __smtx_typeof y) :
    __smtx_typeof (__eo_to_smt_tuple_project is T x) =
      __smtx_typeof (__eo_to_smt_tuple_project is T y) := by
  by_cases hn : is = Term.__eo_List_nil
  · subst hn
    rfl
  · rw [TranslationProofs.tuple_project_eq_rec_of_ne_nil hn,
      TranslationProofs.tuple_project_eq_rec_of_ne_nil hn]
    exact substitute_tuple_project_rec_type_congr T x y hTy _ is (Nat.lt_succ_self _)

private theorem eo_typeof_tuple_project_arg_ne_stuck_of_ne_stuck {A idx X : Term}
    (h : __eo_typeof_tuple_project A idx X ≠ Term.Stuck) : X ≠ Term.Stuck := by
  intro hX
  subst hX
  apply h
  unfold __eo_typeof_tuple_project
  split <;> simp_all

theorem substitute_simul_apply_tuple_project_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (idx a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.tuple_project idx) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp1 UserOp1.tuple_project idx) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_project idx) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.tuple_project idx) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_project idx) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop1_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp1.tuple_project idx a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop1_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_tuple_project (__eo_typeof idx) idx (__eo_typeof X) ≠
            Term.Stuck at hApp
        exact eo_typeof_tuple_project_arg_ne_stuck_of_ne_stuck hApp)
      (fun X Y hXY => by
        change
          __eo_typeof_tuple_project (__eo_typeof idx) idx (__eo_typeof X) =
            __eo_typeof_tuple_project (__eo_typeof idx) idx (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (__eo_to_smt_tuple_project idx (__smtx_typeof (__eo_to_smt X))
                (__eo_to_smt X)) ≠
            SmtType.None
        have hATrans :=
          apply_uop1_arg_rule_has_smt_translation_of_rule
            UserOp1.tuple_project idx a hTrans
        have hXSmtTyEq :
            __smtx_typeof (__eo_to_smt X) =
              __smtx_typeof (__eo_to_smt a) :=
          smt_typeof_subst_arg_eq_of_type_eq
            (T := __smtx_typeof (__eo_to_smt a))
            hXTrans hATrans hXTyEq rfl
        have hNN :
            __smtx_typeof
                (__eo_to_smt_tuple_project idx (__smtx_typeof (__eo_to_smt a))
                  (__eo_to_smt a)) ≠
              SmtType.None := by
          have hRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hRaw
          exact hRaw
        rw [hXSmtTyEq,
          substitute_tuple_project_type_congr idx _ (__eo_to_smt X) (__eo_to_smt a)
            hXSmtTyEq]
        exact hNN)
      hARec hTy

end SubstitutePreservationSupport
