module

public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree
public import Cpc.Proofs.Rules.Quant_var_reordering
import all Cpc.Proofs.Rules.Quant_var_reordering

public section

/-!
Binder-list facts for selecting the eliminated variable: list difference
selects a member of the original environment, and erase removes precisely one
occurrence while preserving the reflected environment.
-/
open Eo SmtEval Smtm
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace EoVarEnv

theorem diff_rec_sublist :
    ∀ {a b : Term} {aVars bVars : List EoVarKey},
      EoVarEnv a aVars ->
        EoVarEnv b bVars ->
          ∃ vars',
            EoVarEnv (__eo_list_diff_rec a b) vars' ∧ vars'.Sublist aVars
  | _, _, _, _, nil, hB =>
      by
        cases hB <;>
          exact ⟨[], (by simpa [__eo_list_diff_rec] using EoVarEnv.nil), List.nil_sublist _⟩
  | _, b, _, _, cons (s := s) (T := T) (env := aTail) hTail, hB =>
      by
        let erased := __eo_list_erase_rec b (Term.Var (Term.String s) T)
        rcases
          erase_rec_var s T hB with
          ⟨erasedVars, hErased⟩
        have hErased' : EoVarEnv erased erasedVars := by
          simpa [erased] using hErased
        rcases diff_rec_sublist hTail hErased' with ⟨diffVars, hDiff, hSub⟩
        have hBNe := hB.ne_stuck
        have hErasedNe := hErased'.ne_stuck
        have hDiffNe := hDiff.ne_stuck
        by_cases hEq : erased = b
        · have hEqSymm : b = erased := hEq.symm
          exact
            ⟨(s, T) :: diffVars,
              by
                have hCond : __eo_eq erased b = Term.Boolean true :=
                  eo_eq_true_of_eq hEq hErasedNe
                have hPrep :
                    __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) =
                      Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T))
                        (__eo_list_diff_rec aTail erased) :=
                  eo_prepend_if_true_eq
                    (by intro h; cases h) (by intro h; cases h) hDiffNe
                have hUnfold :
                    __eo_list_diff_rec
                        (Term.Apply
                          (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T))
                          aTail)
                        b =
                      __eo_prepend_if (__eo_eq erased b)
                        Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) := by
                  cases hB <;> simp [__eo_list_diff_rec, erased]
                rw [hUnfold, hCond, hPrep]
                exact EoVarEnv.cons (s := s) (T := T) hDiff, List.Sublist.cons_cons _ hSub⟩
        · exact
            ⟨diffVars,
              by
                have hEqSymm : b ≠ erased := by
                  intro h
                  exact hEq h.symm
                have hCond : __eo_eq erased b = Term.Boolean false :=
                  eo_eq_false_of_ne hErasedNe hBNe hEq
                have hPrep :
                    __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) =
                      __eo_list_diff_rec aTail erased :=
                  eo_prepend_if_false_eq
                    (by intro h; cases h) (by intro h; cases h) hDiffNe
                have hUnfold :
                    __eo_list_diff_rec
                        (Term.Apply
                          (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T))
                          aTail)
                        b =
                      __eo_prepend_if (__eo_eq erased b)
                        Term.__eo_List_cons
                        (Term.Var (Term.String s) T)
                        (__eo_list_diff_rec aTail erased) := by
                  cases hB <;> simp [__eo_list_diff_rec, erased]
                rw [hUnfold, hCond, hPrep]
                exact hDiff, List.Sublist.cons _ hSub⟩

theorem diff_sublist {a b : Term} {av bv : List EoVarKey}
    (ha : EoVarEnv a av) (hb : EoVarEnv b bv) :
    ∃ vs, EoVarEnv (__eo_list_diff Term.__eo_List_cons a b) vs ∧ vs.Sublist av := by
  obtain ⟨vs,hv,hs⟩ := diff_rec_sublist ha hb
  refine ⟨vs, ?_, hs⟩
  simpa [__eo_list_diff, __eo_requires, ha.is_list, hb.is_list,
    native_ite, native_teq, native_not] using hv

theorem selected_mem {a b : Term} {av bv : List EoVarKey}
    (ha : EoVarEnv a av) (hb : EoVarEnv b bv)
    (hn : __eo_list_nth Term.__eo_List_cons
      (__eo_list_diff Term.__eo_List_cons a b) (Term.Numeral 0) ≠ Term.Stuck) :
    ∃ s T, (s,T) ∈ av ∧
      __eo_list_nth Term.__eo_List_cons (__eo_list_diff Term.__eo_List_cons a b)
        (Term.Numeral 0) = Term.Var (Term.String s) T := by
  obtain ⟨vs,he,hs⟩ := diff_sublist ha hb
  generalize hd : __eo_list_diff Term.__eo_List_cons a b = out at he hn ⊢
  have hl := he.is_list
  unfold __eo_list_nth at hn ⊢
  simp only [hl, __eo_requires, native_ite, native_teq, native_not,
    Bool.not_false, if_true] at hn ⊢
  cases he with
  | nil => exact False.elim (hn rfl)
  | @cons s T env vs ht =>
      exact ⟨s,T,hs.subset (List.Mem.head _), rfl⟩

theorem erase_rec_exact {env : Term} {vars : List EoVarKey}
    (h : EoVarEnv env vars) (s : native_String) (T : Term) :
    EoVarEnv (__eo_list_erase_rec env (Term.Var (Term.String s) T)) (vars.erase (s,T)) := by
  induction h with
  | nil => exact .nil
  | @cons sh Th tail vs hh ih =>
      by_cases hk : (sh,Th) = (s,T)
      · cases hk
        simpa [__eo_list_erase_rec, __eo_eq, __eo_ite, native_teq, native_ite] using hh
      · have ht : Term.Var (Term.String sh) Th ≠ Term.Var (Term.String s) T := by
          intro he
          cases he
          exact hk rfl
        have hrev : ¬ (s = sh ∧ T = Th) := by
          rintro ⟨rfl,rfl⟩; exact hk rfl
        have hn := ih.ne_stuck
        simpa [__eo_list_erase_rec, __eo_eq, __eo_ite, __eo_mk_apply,
          native_teq, native_ite, ht, hk, hrev, List.erase_cons, hn] using EoVarEnv.cons (s := sh) (T := Th) ih

theorem erase_exact {env : Term} {vars : List EoVarKey}
    (h : EoVarEnv env vars) (s : native_String) (T : Term) :
    EoVarEnv (__eo_list_erase Term.__eo_List_cons env (Term.Var (Term.String s) T))
      (vars.erase (s,T)) := by
  simpa [__eo_list_erase, __eo_requires, h.is_list, native_teq, native_ite, native_not]
    using erase_rec_exact h s T

end EoVarEnv
