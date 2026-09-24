module

public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev EoVarKey : Type := native_String × Term

def EoVarKey.toSmt (key : EoVarKey) : SmtVarKey :=
  (key.1, __eo_to_smt_type key.2)

/--
An EO variable environment that remembers the original EO type syntax.

`EoSmtVarEnv` is the right relation for SMT closedness, but it stores only the
translated SMT type.  The free-variable checker searches for exact EO variables,
so this relation keeps the EO type term around for the membership facts.
-/
inductive EoVarEnv : Term -> List EoVarKey -> Prop where
  | nil :
      EoVarEnv Term.__eo_List_nil []
  | cons {s : native_String} {T env : Term} {vars : List EoVarKey} :
      EoVarEnv env vars ->
        EoVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env)
          ((s, T) :: vars)

namespace EoVarEnv

theorem to_smt :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        EoSmtVarEnv env (vars.map EoVarKey.toSmt)
  | _, _, nil =>
      by
        exact EoSmtVarEnv.nil
  | _, _, cons hTail =>
      by
        simpa [EoVarKey.toSmt] using EoSmtVarEnv.cons (to_smt hTail)

theorem of_smt :
    ∀ {env : Term} {vars : List SmtVarKey},
      EoSmtVarEnv env vars ->
        ∃ eoVars,
          EoVarEnv env eoVars ∧ vars = eoVars.map EoVarKey.toSmt
  | _, _, EoSmtVarEnv.nil =>
      by
        exact ⟨[], EoVarEnv.nil, rfl⟩
  | _, _, EoSmtVarEnv.cons hTail =>
      by
        rename_i s T env vars
        rcases of_smt hTail with ⟨eoVars, hEo, hVars⟩
        exact
          ⟨(s, T) :: eoVars,
            EoVarEnv.cons (s := s) (T := T) hEo,
            by simp [EoVarKey.toSmt, hVars]⟩

theorem is_list
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  __eo_is_list Term.__eo_List_cons env = Term.Boolean true :=
by
  simpa using hEnv.to_smt.is_list

theorem cons_mk_apply
    {s : native_String} {T env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnv
    (__eo_mk_apply
      (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      env)
    ((s, T) :: vars) :=
by
  cases hEnv with
  | nil =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T) EoVarEnv.nil
  | cons hTail =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T)
          (EoVarEnv.cons hTail)

theorem ne_stuck
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  env ≠ Term.Stuck :=
by
  cases hEnv <;> intro h <;> cases h

theorem vars_eq_of_same_env
    {env : Term} {vars vars' : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    (hEnv' : EoVarEnv env vars') :
  vars = vars' :=
by
  induction hEnv generalizing vars' with
  | nil =>
      cases hEnv'
      rfl
  | cons hTail ih =>
      cases hEnv' with
      | cons hTail' =>
          simp [ih hTail']

private theorem eo_prepend_if_true_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean true) f x res =
    Term.Apply (Term.Apply f x) res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_prepend_if_false_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean false) f x res = res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_eq_true_of_eq
    {x y : Term}
    (hEq : x = y)
    (hX : x ≠ Term.Stuck) :
  __eo_eq x y = Term.Boolean true :=
by
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_false_of_ne
    {x y : Term}
    (hX : x ≠ Term.Stuck)
    (hY : y ≠ Term.Stuck)
    (hNe : x ≠ y) :
  __eo_eq x y = Term.Boolean false :=
by
  have hNeSymm : y ≠ x := by
    intro h
    exact hNe h.symm
  cases x <;> cases y <;>
    simp [__eo_eq, native_teq, hNe, hNeSymm] at hX hY ⊢
  all_goals
    exact False.elim (hNe rfl)

theorem erase_rec_var :
    ∀ {env : Term} {vars : List EoVarKey}
      (s : native_String) (T : Term),
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv
            (__eo_list_erase_rec env (Term.Var (Term.String s) T))
            vars'
  | _, _, _, _, nil =>
      by
        exact ⟨[], by simpa [__eo_list_erase_rec] using EoVarEnv.nil⟩
  | _, _, s, T, cons (s := s') (T := T') (env := envTail) hTail =>
      by
        by_cases hEq :
            Term.Var (Term.String s') T' =
              Term.Var (Term.String s) T
        · exact
            ⟨_, by
              simpa [__eo_list_erase_rec, __eo_eq, native_teq, hEq,
                __eo_ite, native_ite] using hTail⟩
        · have hEqSymm :
              Term.Var (Term.String s) T ≠
                Term.Var (Term.String s') T' := by
            intro h
            exact hEq h.symm
          rcases erase_rec_var s T hTail with ⟨tailVars, hTailErase⟩
          exact
            ⟨(s', T') :: tailVars,
              by
                simpa [__eo_list_erase_rec, __eo_eq, native_teq, hEq,
                  hEqSymm, __eo_ite, native_ite] using
                  cons_mk_apply (s := s') (T := T') hTailErase⟩

theorem erase_all_rec_var :
    ∀ {env : Term} {vars : List EoVarKey}
      (s : native_String) (T : Term),
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv
            (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))
            vars'
  | _, _, _, _, nil =>
      by
        exact
          ⟨[], by simpa [__eo_list_erase_all_rec] using EoVarEnv.nil⟩
  | _, _, s, T, cons (s := s') (T := T') (env := envTail) hTail =>
      by
        by_cases hEq :
            Term.Var (Term.String s) T =
              Term.Var (Term.String s') T'
        · cases hEq
          rcases erase_all_rec_var s T hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                  (Term.Var (Term.String s) T)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) =
                __eo_list_erase_all_rec envTail
                  (Term.Var (Term.String s) T) :=
            eo_prepend_if_false_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          exact
            ⟨tailVars,
              by
                simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                  __eo_not, native_not, __eo_prepend_if, hPrep] using
                  hTailErase⟩
        · have hEqSymm :
              Term.Var (Term.String s') T' ≠
                Term.Var (Term.String s) T := by
            intro h
            exact hEq h.symm
          rcases erase_all_rec_var s T hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                  (Term.Var (Term.String s') T')
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) =
                Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s') T'))
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String s) T)) :=
            eo_prepend_if_true_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          exact
            ⟨(s', T') :: tailVars,
              by
                simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                  hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                  hPrep] using
                  EoVarEnv.cons (s := s') (T := T') hTailErase⟩

theorem erase_all_rec_var_mem_of_mem_ne :
    ∀ {env : Term} {vars : List EoVarKey}
      {sErase : native_String} {TErase : Term}
      {s : native_String} {T : Term},
      EoVarEnv env vars ->
        (s, T) ∈ vars ->
          (s, T) ≠ (sErase, TErase) ->
            ∃ vars',
              EoVarEnv
                (__eo_list_erase_all_rec env
                  (Term.Var (Term.String sErase) TErase))
                vars' ∧
              (s, T) ∈ vars'
  | _, _, _, _, _, _, nil, hMem, _ =>
      by
        cases hMem
  | _, _, sErase, TErase, s, T,
      cons (s := sHead) (T := THead) (env := envTail) hTail,
      hMem, hNe =>
      by
        by_cases hEq :
            Term.Var (Term.String sErase) TErase =
              Term.Var (Term.String sHead) THead
        · cases hEq
          cases hMem with
          | head =>
              exfalso
              exact hNe rfl
          | tail _ hTailMem =>
              rcases
                erase_all_rec_var_mem_of_mem_ne hTail hTailMem hNe with
                ⟨tailVars, hTailErase, hTailMemOut⟩
              have hTailEraseNe := hTailErase.ne_stuck
              have hPrep :
                  __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                      (Term.Var (Term.String sErase) TErase)
                      (__eo_list_erase_all_rec envTail
                        (Term.Var (Term.String sErase) TErase)) =
                    __eo_list_erase_all_rec envTail
                      (Term.Var (Term.String sErase) TErase) :=
                eo_prepend_if_false_eq
                  (by intro h; cases h) (by intro h; cases h) hTailEraseNe
              exact
                ⟨tailVars,
                  by
                    simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                      __eo_not, native_not, __eo_prepend_if, hPrep] using
                      hTailErase,
                  hTailMemOut⟩
        · have hEqSymm :
              Term.Var (Term.String sHead) THead ≠
                Term.Var (Term.String sErase) TErase := by
            intro h
            exact hEq h.symm
          rcases erase_all_rec_var sErase TErase hTail with
            ⟨tailVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                  (Term.Var (Term.String sHead) THead)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) =
                Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String sHead) THead))
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) :=
            eo_prepend_if_true_eq
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          cases hMem with
          | head =>
              exact
                ⟨(s, T) :: tailVars,
                  by
                    simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                      hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                      hPrep] using
                      EoVarEnv.cons (s := s) (T := T) hTailErase,
                  List.Mem.head _⟩
          | tail _ hTailMem =>
              by_cases hKey :
                  (s, T) = (sErase, TErase)
              · exact False.elim (hNe hKey)
              · rcases
                  erase_all_rec_var_mem_of_mem_ne hTail hTailMem hKey with
                ⟨memVars, hMemErase, hMemOut⟩
                have hVarsEq :
                    tailVars = memVars :=
                  EoVarEnv.vars_eq_of_same_env hTailErase hMemErase
                subst tailVars
                exact
                  ⟨(sHead, THead) :: memVars,
                    by
                      simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
                        hEq, hEqSymm, __eo_not, native_not, __eo_prepend_if,
                        hPrep] using
                        EoVarEnv.cons (s := sHead) (T := THead) hMemErase,
                    List.Mem.tail _ hMemOut⟩

theorem setof_rec :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        ∃ vars',
          EoVarEnv (__eo_list_setof_rec env) vars'
  | _, _, nil =>
      by
        exact ⟨[], by simpa [__eo_list_setof_rec] using EoVarEnv.nil⟩
  | _, _, cons (s := s) (T := T) hTail =>
      by
        rcases setof_rec hTail with ⟨setVars, hSet⟩
        rcases
          erase_all_rec_var s T hSet with
          ⟨eraseVars, hErase⟩
        exact
          ⟨(s, T) :: eraseVars,
            by
              simpa [__eo_list_setof_rec] using
                cons_mk_apply (s := s) (T := T) hErase⟩

theorem setof_rec_mem_of_mem :
    ∀ {env : Term} {vars : List EoVarKey}
      {s : native_String} {T : Term},
      EoVarEnv env vars ->
        (s, T) ∈ vars ->
          ∃ vars',
            EoVarEnv (__eo_list_setof_rec env) vars' ∧
            (s, T) ∈ vars'
  | _, _, _, _, nil, hMem =>
      by
        cases hMem
  | _, _, s, T, cons (s := sHead) (T := THead) hTail, hMem =>
      by
        rcases setof_rec hTail with ⟨setVars, hSet⟩
        rcases
          erase_all_rec_var sHead THead hSet with
          ⟨eraseVars, hErase⟩
        cases hMem with
        | head =>
            exact
              ⟨(s, T) :: eraseVars,
                by
                  simpa [__eo_list_setof_rec] using
                    cons_mk_apply (s := s) (T := T) hErase,
                List.Mem.head _⟩
        | tail _ hTailMem =>
            by_cases hKey :
                (s, T) = (sHead, THead)
            · cases hKey
              exact
                ⟨(s, T) :: eraseVars,
                  by
                    simpa [__eo_list_setof_rec] using
                      cons_mk_apply (s := s) (T := T) hErase,
                  List.Mem.head _⟩
            · rcases setof_rec_mem_of_mem hTail hTailMem with
                ⟨memSetVars, hMemSet, hMemSetVars⟩
              have hSetEq :
                  setVars = memSetVars :=
                EoVarEnv.vars_eq_of_same_env hSet hMemSet
              subst setVars
              rcases
                erase_all_rec_var_mem_of_mem_ne hMemSet hMemSetVars
                  (by
                    intro hEq
                    exact hKey hEq) with
                ⟨memEraseVars, hMemErase, hMemEraseVars⟩
              have hEraseEq :
                  eraseVars = memEraseVars :=
                EoVarEnv.vars_eq_of_same_env hErase hMemErase
              subst eraseVars
              exact
                ⟨(sHead, THead) :: memEraseVars,
                  by
                    simpa [__eo_list_setof_rec] using
                      cons_mk_apply (s := sHead) (T := THead) hMemErase,
                  List.Mem.tail _ hMemEraseVars⟩

theorem setof
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∃ vars',
    EoVarEnv (__eo_list_setof Term.__eo_List_cons env) vars' :=
by
  have hList := hEnv.is_list
  rcases setof_rec hEnv with ⟨setVars, hSet⟩
  exact
    ⟨setVars,
      by
        simpa [__eo_list_setof, __eo_requires, hList, native_ite,
          native_teq, native_not] using hSet⟩

theorem setof_mem_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
  ∃ vars',
    EoVarEnv (__eo_list_setof Term.__eo_List_cons env) vars' ∧
    (s, T) ∈ vars' :=
by
  have hList := hEnv.is_list
  rcases setof_rec_mem_of_mem hEnv hMem with
    ⟨setVars, hSet, hSetMem⟩
  exact
    ⟨setVars,
      by
        simpa [__eo_list_setof, __eo_requires, hList, native_ite,
          native_teq, native_not] using hSet,
      hSetMem⟩

theorem diff_rec :
    ∀ {a b : Term} {aVars bVars : List EoVarKey},
      EoVarEnv a aVars ->
        EoVarEnv b bVars ->
          ∃ vars',
            EoVarEnv (__eo_list_diff_rec a b) vars'
  | _, _, _, _, nil, hB =>
      by
        cases hB <;>
          exact ⟨[], by simpa [__eo_list_diff_rec] using EoVarEnv.nil⟩
  | _, b, _, _, cons (s := s) (T := T) (env := aTail) hTail, hB =>
      by
        let erased := __eo_list_erase_rec b (Term.Var (Term.String s) T)
        rcases
          erase_rec_var s T hB with
          ⟨erasedVars, hErased⟩
        have hErased' : EoVarEnv erased erasedVars := by
          simpa [erased] using hErased
        rcases diff_rec hTail hErased' with ⟨diffVars, hDiff⟩
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
                exact EoVarEnv.cons (s := s) (T := T) hDiff⟩
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
                exact hDiff⟩

theorem diff
    {a b : Term} {aVars bVars : List EoVarKey}
    (hA : EoVarEnv a aVars)
    (hB : EoVarEnv b bVars) :
  ∃ vars',
    EoVarEnv (__eo_list_diff Term.__eo_List_cons a b) vars' :=
by
  have hAList := hA.is_list
  have hBList := hB.is_list
  rcases diff_rec hA hB with ⟨diffVars, hDiff⟩
  exact
    ⟨diffVars,
      by
        simpa [__eo_list_diff, __eo_requires, hAList, hBList,
          native_ite, native_teq, native_not] using hDiff⟩

theorem concat_rec :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat_rec vs env)
            (binderVars ++ vars)
  | _, _, _, _, nil, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec] using EoVarEnv.nil
        | cons hTail =>
            rename_i s' T' env' vars'
            simpa [__eo_list_concat_rec] using
              EoVarEnv.cons (s := s') (T := T') hTail
  | _, _, _, _, cons (s := s) (T := T) hTail, hEnv =>
      by
        cases hEnv with
        | nil =>
            have hTailConcat := concat_rec hTail EoVarEnv.nil
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat
        | cons hEnvTail =>
            rename_i s' T' env' vars'
            have hTailConcat :=
              concat_rec hTail
                (EoVarEnv.cons (s := s') (T := T') hEnvTail)
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat

theorem concat :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat Term.__eo_List_cons vs env)
            (binderVars ++ vars)
  | _, _, _, _, hVs, hEnv =>
      by
        have hVsList := hVs.is_list
        have hEnvList := hEnv.is_list
        simpa [__eo_list_concat, __eo_requires, hVsList, hEnvList,
          native_ite, native_teq, native_not]
          using concat_rec hVs hEnv

theorem find_rec_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∈ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean false :=
by
  induction hEnv with
  | nil =>
      intro s T n hMem hNonneg
      cases hMem
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, Int.not_lt_of_ge hNonneg]
        simp [__eo_list_find_rec, hFindEq, __eo_ite, __eo_is_neg,
          native_ite, native_teq, hNotLt]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailMem : (s, T) ∈ vars' := by
          cases hMem with
          | head =>
              exfalso
              exact hVarEq rfl
          | tail _ hTailMem =>
              exact hTailMem
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailMem hSuccNonneg

theorem find_rec_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∉ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean true :=
by
  induction hEnv with
  | nil =>
      intro s T n hNotMem hNonneg
      simp [__eo_list_find_rec, __eo_is_neg, native_zlt]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hNotMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · exfalso
        injection hVarEq with hName hTy
        injection hName with hs
        cases hs
        cases hTy
        exact hNotMem (List.Mem.head _)
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailNotMem : (s, T) ∉ vars' := by
          intro hMem
          exact hNotMem (List.Mem.tail _ hMem)
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailNotMem hSuccNonneg

theorem find_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean false :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq,
    native_not]
    using
      hEnv.find_rec_neg_false_of_mem hMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

theorem find_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hNotMem : (s, T) ∉ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean true :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq,
    native_not]
    using
      hEnv.find_rec_neg_true_of_not_mem hNotMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

end EoVarEnv

def EoVarEnvEquiv (xs ys : List EoVarKey) : Prop :=
  ∀ key, key ∈ xs ↔ key ∈ ys

theorem EoVarEnvEquiv.refl (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs :=
by
  intro key
  rfl

theorem EoVarEnvEquiv.reverse (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs.reverse :=
by
  intro key
  simp

theorem EoVarEnvEquiv.append
    {xs xs' ys ys' : List EoVarKey}
    (hxs : EoVarEnvEquiv xs xs')
    (hys : EoVarEnvEquiv ys ys') :
  EoVarEnvEquiv (xs ++ ys) (xs' ++ ys') :=
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

def EoVarEnvPerm (env : Term) (vars : List EoVarKey) : Prop :=
  ∃ exactVars, EoVarEnv env exactVars ∧ EoVarEnvEquiv exactVars vars

theorem EoVarEnvPerm.of_exact
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnvPerm env vars :=
by
  exact ⟨vars, hEnv, EoVarEnvEquiv.refl vars⟩

theorem EoVarEnvPerm.mem_of_exact_env_mem
    {env : Term} {exactVars vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    (hExact : EoVarEnv env exactVars)
    {key : EoVarKey}
    (hMem : key ∈ exactVars) :
  key ∈ vars :=
by
  rcases hEnv with ⟨envVars, hEnvVars, hEquiv⟩
  have hEq : exactVars = envVars :=
    EoVarEnv.vars_eq_of_same_env hExact hEnvVars
  subst exactVars
  exact (hEquiv key).1 hMem

theorem EoVarEnvPerm.ne_stuck
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars) :
  env ≠ Term.Stuck :=
by
  rcases hEnv with ⟨_, hExact, _⟩
  exact hExact.ne_stuck

theorem EoVarEnvPerm.mem_of_find_neg_false
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
  (s, T) ∈ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  by_cases hMem : (s, T) ∈ exactVars
  · exact (hEquiv (s, T)).1 hMem
  · have hFindTrue := hExact.find_neg_true_of_not_mem hMem
    rw [hFindTrue] at hFind
    cases hFind

theorem EoVarEnvPerm.not_mem_of_find_neg_true
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
  (s, T) ∉ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  intro hMem
  have hExactMem : (s, T) ∈ exactVars := (hEquiv (s, T)).2 hMem
  have hFindFalse := hExact.find_neg_false_of_mem hExactMem
  rw [hFind] at hFindFalse
  cases hFindFalse

theorem EoVarKey.mem_of_toSmt_mem_map_of_type_wf
    {vars : List EoVarKey} {s : native_String} {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hMem : (s, __eo_to_smt_type T) ∈ vars.map EoVarKey.toSmt) :
  (s, T) ∈ vars :=
by
  rcases List.mem_map.1 hMem with ⟨key, hKeyMem, hKeyEq⟩
  rcases key with ⟨s', T'⟩
  simp [EoVarKey.toSmt] at hKeyEq
  rcases hKeyEq with ⟨hName, hType⟩
  subst s'
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    have hT' :
        T' = Term.UOp UserOp.RegLan :=
      TranslationProofs.eo_to_smt_type_eq_reglan hType
    subst T'
    exact hKeyMem
  · have hValid : TranslationProofs.eo_type_valid T :=
      TranslationProofs.eo_type_valid_of_smt_wf T hWf
    have hValidRec : TranslationProofs.eo_type_valid_rec [] T := by
      cases T with
      | UOp op =>
          cases op
          case RegLan =>
            exact False.elim (hReg rfl)
          all_goals
            exact hValid
      | _ =>
          exact hValid
    have hT : T = T' :=
      TranslationProofs.eo_to_smt_type_eq_of_valid
        (T := T) (U := T') hValidRec hType.symm
    subst T'
    exact hKeyMem

theorem EoVarEnvPerm.toSmt_not_mem_of_find_neg_true
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
  (s, __eo_to_smt_type T) ∉ vars.map EoVarKey.toSmt :=
by
  have hNotMem : (s, T) ∉ vars :=
    EoVarEnvPerm.not_mem_of_find_neg_true hEnv hFind
  intro hMem
  exact hNotMem
    (EoVarKey.mem_of_toSmt_mem_map_of_type_wf hWf hMem)

theorem smtx_type_wf_of_var_has_smt_translation
    {s : native_String} {T : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Var (Term.String s) T)) :
  __smtx_type_wf (__eo_to_smt_type T) = true :=
by
  have hGuardNN :
      __smtx_typeof_guard_wf
          (__eo_to_smt_type T) (__eo_to_smt_type T) ≠
        SmtType.None := by
    have hNN :
        __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠
          SmtType.None := by
      simpa [eoHasSmtTranslation] using hTrans
    simpa [__smtx_typeof] using hNN
  exact
    smtx_typeof_guard_wf_wf_of_non_none
      (__eo_to_smt_type T) (__eo_to_smt_type T) hGuardNN

theorem EoVarEnvPerm.concat_rev
    {vs env : Term} {binderVars vars : List EoVarKey}
    (hVs : EoVarEnv vs binderVars)
    (hEnv : EoVarEnvPerm env vars) :
  EoVarEnvPerm
    (__eo_list_concat Term.__eo_List_cons vs env)
    (binderVars.reverse ++ vars) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  refine ⟨binderVars ++ exactVars, EoVarEnv.concat hVs hExact, ?_⟩
  exact EoVarEnvEquiv.append
    (EoVarEnvEquiv.reverse binderVars)
    hEquiv

theorem eo_var_env_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    eo_smt_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨smtVars, hSmtEnv⟩
  rcases EoVarEnv.of_smt hSmtEnv with
    ⟨eoVars, hEoEnv, _hVars⟩
  exact ⟨eoVars, hEoEnv⟩

theorem eo_var_env_of_list_branch_has_smt_translation
    {q v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · subst q
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans

theorem eo_var_env_of_forall_has_smt_translation
    {xs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  by_cases hCons :
      ∃ v vs,
        xs = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  · rcases hCons with ⟨v, vs, rfl⟩
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · exact
      false_of_forall_non_list_has_smt_translation
        (by
          intro v vs hEq
          exact hCons ⟨v, vs, hEq⟩)
        hTrans

theorem eo_var_env_of_exists_has_smt_translation
    {xs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  by_cases hCons :
      ∃ v vs,
        xs = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  · rcases hCons with ⟨v, vs, rfl⟩
    exact eo_var_env_of_uop_list_branch_has_smt_translation hTrans
  · exact
      false_of_exists_non_list_has_smt_translation
        (by
          intro v vs hEq
          exact hCons ⟨v, vs, hEq⟩)
        hTrans

theorem eo_var_env_of_quant_has_smt_translation
    {Q xs body : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Q xs) body)) :
  ∃ vars, EoVarEnv xs vars :=
by
  rcases hQ with hForall | hExists
  · subst Q
    exact eo_var_env_of_forall_has_smt_translation hTrans
  · subst Q
    exact eo_var_env_of_exists_has_smt_translation hTrans

/--
Models agree everywhere except possibly on the variables in `except` that are
not currently shadowed by `bound`.

This is the semantic relation matched to
`__contains_atomic_term_list_free_rec t except bound = false`: free variables in
`except` are the only variables on which the two models may differ, while
variables in `bound` are considered locally bound and therefore must agree after
the evaluator pushes matching witnesses on both sides.
-/
structure model_agrees_except_on_env
    (except bound : List SmtVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s T = native_model_var_lookup N s T

theorem model_agrees_except_on_env_refl
    (except bound : List SmtVarKey) (M : SmtModel) :
  model_agrees_except_on_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_env_symm
    {except bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_env_push_same
    {except bound : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except ((s, T) :: bound)
    (native_model_push M s T v) (native_model_push N s T v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    simp [native_model_var_lookup, native_model_push]
  · have hAllowedTail : (s', T') ∈ bound ∨ (s', T') ∉ except := by
      rcases hKeyAllowed with hBound | hNotExcept
      · cases hBound with
        | head =>
            exfalso
            exact hKey rfl
        | tail _ hTail =>
            exact Or.inl hTail
      · exact Or.inr hNotExcept
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowedTail

theorem model_agrees_except_on_env_shrink_bound
    {except bound bound' : List SmtVarKey} {M N : SmtModel}
    (hSub : ∀ key, key ∈ bound' -> key ∈ bound)
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound' M N :=
by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hBound' | hNotExcept
  · exact Or.inl (hSub (s, T) hBound')
  · exact Or.inr hNotExcept

theorem model_agrees_except_on_env_push_left_of_mem_except
    {except bound : List SmtVarKey} {M : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hMem : (s, T) ∈ except)
    (hNotBound : (s, T) ∉ bound) :
  model_agrees_except_on_env except bound
    (native_model_push M s T v) M :=
by
  refine ⟨model_agrees_on_globals_push M s T v, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    exfalso
    rcases hAllowed with hBound | hNotExcept
    · exact hNotBound hBound
    · exact hNotExcept hMem
  · simp [native_model_var_lookup, native_model_push, hKey]

theorem model_agrees_except_on_env_push_left
    {except bound : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hAgree : model_agrees_except_on_env except bound N M)
    (hMem : (s, T) ∈ except)
    (hNotBound : (s, T) ∉ bound) :
  model_agrees_except_on_env except bound
    (native_model_push N s T v) M :=
by
  refine
    ⟨model_agrees_on_globals_trans
      (model_agrees_on_globals_push N s T v) hAgree.globals, ?_⟩
  intro s' T' hAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    exfalso
    rcases hAllowed with hBound | hNotExcept
    · exact hNotBound hBound
    · exact hNotExcept hMem
  · simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowed

/--
Exact-EO-variable version of `model_agrees_except_on_env`.

The checker's free-variable test compares whole EO variables, including the EO
type syntax.  This relation preserves that exactness while still comparing SMT
model lookups at the translated type.
-/
structure model_agrees_except_on_eo_env
    (except bound : List EoVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

theorem model_agrees_except_on_eo_env_refl
    (except bound : List EoVarKey) (M : SmtModel) :
  model_agrees_except_on_eo_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_eo_env_symm
    {except bound : List EoVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_eo_env_push_same
    {except bound : List EoVarKey} {M N : SmtModel}
    {s : native_String} {T : Term} {v : SmtValue}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except ((s, T) :: bound)
    (native_model_push M s (__eo_to_smt_type T) v)
    (native_model_push N s (__eo_to_smt_type T) v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · simp [native_model_var_lookup, native_model_push, hKey]
  · have hAllowedTail : (s', T') ∈ bound ∨ (s', T') ∉ except := by
      rcases hKeyAllowed with hBound | hNotExcept
      · cases hBound with
        | head =>
            exfalso
            exact hKey rfl
        | tail _ hTail =>
            exact Or.inl hTail
      · exact Or.inr hNotExcept
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowedTail

private theorem eo_ite_false_eq_false_cases
    {c e : Term}
    (h : __eo_ite c (Term.Boolean false) e = Term.Boolean false) :
  c = Term.Boolean true ∨ e = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b
    · right
      simpa [__eo_ite, native_ite, native_teq] using h
    · left
      rfl

private theorem eo_ite_true_eq_false_cases
    {c e : Term}
    (h : __eo_ite c (Term.Boolean true) e = Term.Boolean false) :
  c = Term.Boolean false ∧ e = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b
    · constructor
      · rfl
      · simpa [__eo_ite, native_ite, native_teq] using h
    · cases h

/--
The variable case of `__contains_atomic_term_list_free_rec`.

For a variable, returning `false` means exactly the checker's local condition:
either the variable is absent from the exception list, or it is present in the
current bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_var_false_cases
    {name T except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec (Term.Var name T) except bound =
        Term.Boolean false) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons except (Term.Var name T)) =
      Term.Boolean true ∨
    __eo_is_neg
      (__eo_list_find Term.__eo_List_cons bound (Term.Var name T)) =
      Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact eo_ite_false_eq_false_cases hNoFree

theorem native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  native_model_var_lookup M s (__eo_to_smt_type T) =
    native_model_var_lookup N s (__eo_to_smt_type T) :=
by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hNotExcept | hBoundVar
  · have hNotMem :
        (s, T) ∉ exceptVars :=
      EoVarEnvPerm.not_mem_of_find_neg_true hExcept hNotExcept
    exact hAgree.vars_eq s T (Or.inr hNotMem)
  · have hMem :
        (s, T) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBound hBoundVar
    exact hAgree.vars_eq s T (Or.inl hMem)

theorem smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
    __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
  exact
    native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
      hExcept hBound hNoFree hAgree

theorem native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false_mapped
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  native_model_var_lookup M s (__eo_to_smt_type T) =
    native_model_var_lookup N s (__eo_to_smt_type T) :=
by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hNotExcept | hBoundVar
  · have hNotMem :
        (s, __eo_to_smt_type T) ∉ exceptVars.map EoVarKey.toSmt :=
      EoVarEnvPerm.toSmt_not_mem_of_find_neg_true
        hExcept hWf hNotExcept
    exact hAgree.vars_eq s (__eo_to_smt_type T) (Or.inr hNotMem)
  · have hMem :
        (s, T) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBound hBoundVar
    have hSmtMem :
        (s, __eo_to_smt_type T) ∈ boundVars.map EoVarKey.toSmt :=
      List.mem_map.2 ⟨(s, T), hMem, by simp [EoVarKey.toSmt]⟩
    exact hAgree.vars_eq s (__eo_to_smt_type T) (Or.inl hSmtMem)

theorem smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
    __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
  exact
    native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false_mapped
      hExcept hBound hWf hNoFree hAgree

/--
The quantifier-shaped/list-binder branch only asks the body about free
variables, with the binder list appended to the bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_list_branch_false_body
    {q x ys body except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            body)
          except bound =
        Term.Boolean false)
    :
  __contains_atomic_term_list_free_rec body except
      (__eo_list_concat Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bound) =
    Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact hNoFree

/--
The ordinary application branch checks both the head and the argument.

The side condition excludes the generated list-binder branch, which has higher
priority in `__contains_atomic_term_list_free_rec`.
-/
theorem contains_atomic_term_list_free_rec_apply_false_cases
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec f except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec a except bound =
      Term.Boolean false :=
by
  rcases hExcept with ⟨exactExcept, hExactExcept, _hExceptEquiv⟩
  rcases hBound with ⟨exactBound, hExactBound, _hBoundEquiv⟩
  cases hExactExcept <;> cases hExactBound <;> cases f <;>
    simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
    try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i q y
    cases y <;>
      simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
      try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i g ys
    cases g <;>
      simp only [__contains_atomic_term_list_free_rec] at hNoFree ⊢ <;>
      try exact eo_ite_true_eq_false_cases hNoFree
  all_goals
    rename_i x
    exfalso
    exact hNotList _ x _ rfl

/--
Evaluator congruence for the generic SMT application emitted by the fallback
`__eo_to_smt` application clause.
-/
theorem smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
    {f a : Term} {M N : SmtModel}
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hAgree : model_agrees_on_globals M N)
    (hFunc :
      __smtx_model_eval M (__eo_to_smt f) =
        __smtx_model_eval N (__eo_to_smt f))
    (hArg :
      __smtx_model_eval M (__eo_to_smt a) =
        __smtx_model_eval N (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  rw [hTranslate]
  exact
    smtx_model_eval_apply_eq_of_env
      (model_agrees_on_env_nil_of_globals hAgree) hFunc hArg

/--
One-step semantic theorem for the ordinary generic application branch.

The translation/type hypotheses are the usual generic-application side
conditions: the EO translator emitted `SmtTerm.Apply`, and that SMT application
has the standard `typeof_apply` type.  They let us recover SMT translations for
both recursive subterms from the translation of the whole application.
-/
theorem smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : eoHasSmtTranslation (Term.Apply f a))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hFuncEval :
      eoHasSmtTranslation f ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec f except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_eo_env exceptVars boundVars M' N' ->
                __smtx_model_eval M' (__eo_to_smt f) =
                  __smtx_model_eval N' (__eo_to_smt f))
    (hArgEval :
      eoHasSmtTranslation a ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec a except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_eo_env exceptVars boundVars M' N' ->
                __smtx_model_eval M' (__eo_to_smt a) =
                  __smtx_model_eval N' (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFuncTrans, hArgTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound hNotList hNoFree with
    ⟨hFuncNoFree, hArgNoFree⟩
  exact
    smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
      hTranslate hAgree.globals
      (hFuncEval hFuncTrans hBound hFuncNoFree hAgree)
      (hArgEval hArgTrans hBound hArgNoFree hAgree)

theorem smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {f a except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNotList :
      ∀ q x ys,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : eoHasSmtTranslation (Term.Apply f a))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply f a) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hFuncEval :
      eoHasSmtTranslation f ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec f except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt)
                (boundVars.map EoVarKey.toSmt) M' N' ->
                __smtx_model_eval M' (__eo_to_smt f) =
                  __smtx_model_eval N' (__eo_to_smt f))
    (hArgEval :
      eoHasSmtTranslation a ->
        EoVarEnvPerm bound boundVars ->
          __contains_atomic_term_list_free_rec a except bound =
            Term.Boolean false ->
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt)
                (boundVars.map EoVarKey.toSmt) M' N' ->
                __smtx_model_eval M' (__eo_to_smt a) =
                  __smtx_model_eval N' (__eo_to_smt a)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply f a)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFuncTrans, hArgTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound hNotList hNoFree with
    ⟨hFuncNoFree, hArgNoFree⟩
  exact
    smt_model_eval_eo_to_smt_apply_generic_eq_of_eval_eq
      hTranslate hAgree.globals
      (hFuncEval hFuncTrans hBound hFuncNoFree hAgree)
      (hArgEval hArgTrans hBound hArgNoFree hAgree)

theorem smtx_model_eval_ite_eq_of_eval_eq
    {M N : SmtModel} {c x y : SmtTerm}
    (hc :
      __smtx_model_eval M c = __smtx_model_eval N c)
    (hx :
      __smtx_model_eval M x = __smtx_model_eval N x)
    (hy :
      __smtx_model_eval M y = __smtx_model_eval N y) :
  __smtx_model_eval M (SmtTerm.ite c x y) =
    __smtx_model_eval N (SmtTerm.ite c x y) :=
by
  simp [__smtx_model_eval, hc, hx, hy]

theorem smtx_model_eval_apply_term_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    {f x : SmtTerm}
    (hf :
      __smtx_model_eval M f =
        __smtx_model_eval N f)
    (hx :
      __smtx_model_eval M x =
        __smtx_model_eval N x) :
  __smtx_model_eval M (SmtTerm.Apply f x) =
    __smtx_model_eval N (SmtTerm.Apply f x) :=
by
  by_cases hSel : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSel with ⟨s, d, i, j, rfl⟩
    simp [__smtx_model_eval, hx, smtx_model_eval_dt_sel_eq_of_globals hGlobals]
  · by_cases hTester : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTester with ⟨s, d, i, rfl⟩
      simp [__smtx_model_eval, hx]
    · have hSel' : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := fun s d i j h => hSel ⟨s, d, i, j, h⟩
      have hTester' : ∀ s d i, f ≠ SmtTerm.DtTester s d i := fun s d i h => hTester ⟨s, d, i, h⟩
      have hGen := generic_apply_eval_of_non_datatype_head (x := x) hSel' hTester'
      unfold generic_apply_eval at hGen
      rw [hGen M, hGen N, hf, hx]
      exact smtx_model_eval_apply_eq_of_globals hGlobals _ _

theorem smtx_model_eval_eo_to_smt_updater_rec_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (sel : SmtTerm) (n : native_Nat) (t u acc : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t)
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u)
    (hAcc :
      __smtx_model_eval M acc =
        __smtx_model_eval N acc) :
  __smtx_model_eval M (__eo_to_smt_updater_rec sel n t u acc) =
    __smtx_model_eval N (__eo_to_smt_updater_rec sel n t u acc) :=
by
  induction n generalizing acc with
  | zero =>
      cases sel <;>
        simp [__eo_to_smt_updater_rec, __smtx_model_eval, hAcc]
  | succ k ih =>
      cases sel <;>
        try simp [__eo_to_smt_updater_rec, __smtx_model_eval]
      case DtSel s d i j =>
        have hRec :
            __smtx_model_eval M
                (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc) =
              __smtx_model_eval N
                (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) k t u acc) :=
          ih acc hAcc
        have hArg :
            __smtx_model_eval M
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) =
              __smtx_model_eval N
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) := by
          cases hEq : native_nateq j k <;>
            simp [native_ite, hu, ht, __smtx_model_eval,
              smtx_model_eval_dt_sel_eq_of_globals hGlobals]
        exact
          smtx_model_eval_apply_term_eq_of_eval_eq hGlobals hRec hArg

theorem smtx_model_eval_eo_to_smt_updater_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (sel t u : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t)
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u) :
  __smtx_model_eval M (__eo_to_smt_updater sel t u) =
    __smtx_model_eval N (__eo_to_smt_updater sel t u) :=
by
  cases sel
  case DtSel s d i j =>
    cases hGuard :
        native_zlt (native_nat_to_int j)
          (native_nat_to_int
            (__smtx_dt_num_sels (__smtx_dd_lookup s d) i))
    · have hUpdater :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.None := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdater]
      simp [__smtx_model_eval]
    ·
      have hUpdater :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i))
              t := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdater]
      have hCond :
          __smtx_model_eval M
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t) =
            __smtx_model_eval N
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t) :=
        smtx_model_eval_apply_term_eq_of_eval_eq hGlobals
          (by simp [__smtx_model_eval]) ht
      have hThen :
          __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i)) =
            __smtx_model_eval N
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i)) :=
        smtx_model_eval_eo_to_smt_updater_rec_eq_of_eval_eq
          hGlobals (SmtTerm.DtSel s d i j)
          (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
          t u (SmtTerm.DtCons s d i) ht hu
          (by simp [__smtx_model_eval])
      exact smtx_model_eval_ite_eq_of_eval_eq hCond hThen ht
  all_goals
    simp [__eo_to_smt_updater, __smtx_model_eval]

/-- Outside the tuple-shaped case `__eo_to_smt_tuple_update` is `SmtTerm.None`,
which any two models evaluate the same way.  Discharging the fall-through cases
through this lemma keeps `__smtx_model_eval` from being unfolded once per
`SmtType`/`SmtTerm` constructor pair. -/
theorem smtx_model_eval_eo_to_smt_tuple_update_none_eq
    {M N : SmtModel} {T : SmtType} {idx t u : SmtTerm}
    (h : __eo_to_smt_tuple_update T idx t u = SmtTerm.None) :
  __smtx_model_eval M (__eo_to_smt_tuple_update T idx t u) =
    __smtx_model_eval N (__eo_to_smt_tuple_update T idx t u) :=
by
  rw [h]
  simp [__smtx_model_eval]

theorem smtx_model_eval_eo_to_smt_tuple_update_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (T : SmtType) (idx t u : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t)
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u) :
  __smtx_model_eval M (__eo_to_smt_tuple_update T idx t u) =
    __smtx_model_eval N (__eo_to_smt_tuple_update T idx t u) :=
by
  -- Split only as far as `__eo_to_smt_tuple_update` actually looks: the index
  -- is examined solely for a one-constructor `@Tuple` datatype body.
  cases T
  case Datatype s dd =>
    cases dd
    case cons s2 d rest =>
      cases rest
      case cons s3 d3 rest3 =>
          exact smtx_model_eval_eo_to_smt_tuple_update_none_eq rfl
      case nil =>
          cases idx
          case Numeral n =>
            cases hGuard :
                native_and
                  (native_and
                    (native_streq s (native_string_lit "@Tuple"))
                    (native_streq s2 (native_string_lit "@Tuple")))
                  (native_zleq 0 n)
            · simp [__eo_to_smt_tuple_update, hGuard, native_ite,
                __smtx_model_eval]
            ·
              have hTuple :
                  __eo_to_smt_tuple_update
                      (SmtType.Datatype s
                        (SmtDatatypeDecl.cons s2 d SmtDatatypeDecl.nil))
                      (SmtTerm.Numeral n) t u =
                    __eo_to_smt_updater
                      (SmtTerm.DtSel (native_string_lit "@Tuple")
                        (__eo_to_smt_tuple_decl d)
                        native_nat_zero (native_int_to_nat n)) t u := by
                simp [__eo_to_smt_tuple_update, hGuard, native_ite]
              rw [hTuple]
              exact
                smtx_model_eval_eo_to_smt_updater_eq_of_eval_eq hGlobals
                  (SmtTerm.DtSel (native_string_lit "@Tuple")
                    (__eo_to_smt_tuple_decl d) native_nat_zero
                    (native_int_to_nat n))
                  t u ht hu
          all_goals
            exact smtx_model_eval_eo_to_smt_tuple_update_none_eq rfl
    case nil =>
      exact smtx_model_eval_eo_to_smt_tuple_update_none_eq rfl
  all_goals
    exact smtx_model_eval_eo_to_smt_tuple_update_none_eq rfl

theorem contains_atomic_term_list_free_rec_apply_uop_false_arg
    {op : UserOp} {x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) x) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
    Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hArgNoFree⟩
  exact hArgNoFree

theorem contains_atomic_term_list_free_rec_apply_apply_uop_false_args
    {op : UserOp} {x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp op) x) y) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hXNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hYNoFree⟩
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hHeadNoFree
  exact ⟨hXNoFree, hYNoFree⟩

theorem contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
    {op : UserOp} {c x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hCNotList :
      ∀ v vs,
        c ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)
          except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec c except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hXNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hYNoFree⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound hCNotList hHeadNoFree with
    ⟨hCNoFree, hXNoFree⟩
  exact ⟨hCNoFree, hXNoFree, hYNoFree⟩

theorem smt_model_eval_apply_not_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp UserOp.not) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) :=
by
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hNoFree
  have hXTrans :
      eoHasSmtTranslation x :=
    not_arg_has_smt_translation_of_has_smt_translation hTrans
  change
    __smtx_model_eval M (SmtTerm.not (__eo_to_smt x)) =
      __smtx_model_eval N (SmtTerm.not (__eo_to_smt x))
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)

theorem smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hArgTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x) ->
        eoHasSmtTranslation x)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
        __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hNoFree
  exact
    hEval
      (ih hXLt hExcept hBound (hArgTrans hTrans) hXNoFree hAgree)

theorem smt_model_eval_eo_to_smt_distinct_pairs_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {s : SmtTerm} {xs except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXsLt : sizeOf xs < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None)
    (hNoFree :
      __contains_atomic_term_list_free_rec xs except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hS :
      __smtx_model_eval M s = __smtx_model_eval N s)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt_distinct_pairs s xs) =
    __smtx_model_eval N (__eo_to_smt_distinct_pairs s xs) :=
by
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change
              __smtx_model_eval M (SmtTerm.Boolean true) =
                __smtx_model_eval N (SmtTerm.Boolean true)
            simp [__smtx_model_eval]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                let headTy := __smtx_typeof (__eo_to_smt head)
                let tailTy := __eo_to_smt_typed_list_elem_type tail
                have hGuard : native_Teq headTy tailTy = true := by
                  by_cases hGuard : native_Teq headTy tailTy = true
                  · exact hGuard
                  · exfalso
                    exact hElemNN (by
                      simp [__eo_to_smt_typed_list_elem_type, headTy,
                        tailTy, native_ite, hGuard])
                have hHeadNN : headTy ≠ SmtType.None := by
                  change
                    (native_ite (native_Teq headTy tailTy) headTy
                        SmtType.None) ≠
                      SmtType.None at hElemNN
                  rw [hGuard] at hElemNN
                  exact hElemNN
                have hTailNN : tailTy ≠ SmtType.None := by
                  intro hTailNone
                  cases hHead : headTy <;>
                    simp [headTy, tailTy, hHead, hTailNone, native_Teq]
                      at hGuard hHeadNN
                have hHeadTrans : eoHasSmtTranslation head := by
                  unfold eoHasSmtTranslation
                  simpa [headTy] using hHeadNN
                rcases
                  contains_atomic_term_list_free_rec_apply_apply_uop_false_args
                    hExcept hBound
                    (term_not_eo_list_cons_of_has_smt_translation hHeadTrans)
                    hNoFree with
                  ⟨hHeadNoFree, hTailNoFree⟩
                have hHeadEval :
                    __smtx_model_eval M (__eo_to_smt head) =
                      __smtx_model_eval N (__eo_to_smt head) :=
                  ih (by simp at hXsLt ⊢; omega)
                    hExcept hBound hHeadTrans hHeadNoFree hAgree
                have hTailEval :
                    __smtx_model_eval M
                        (__eo_to_smt_distinct_pairs s tail) =
                      __smtx_model_eval N
                        (__eo_to_smt_distinct_pairs s tail) :=
                  smt_model_eval_eo_to_smt_distinct_pairs_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    root
                    (hXsLt := by simp at hXsLt ⊢; omega)
                    hExcept hBound
                    (by simpa [tailTy] using hTailNN)
                    hTailNoFree hAgree hS ih
                change
                  __smtx_model_eval M
                      (SmtTerm.and
                        (SmtTerm.not
                          (SmtTerm.eq s (__eo_to_smt head)))
                        (__eo_to_smt_distinct_pairs s tail)) =
                    __smtx_model_eval N
                      (SmtTerm.and
                        (SmtTerm.not
                          (SmtTerm.eq s (__eo_to_smt head)))
                        (__eo_to_smt_distinct_pairs s tail))
                exact
                  smtx_model_eval_and_eq_of_eval_eq
                    (smtx_model_eval_not_eq_of_eval_eq
                      (smtx_model_eval_eq_eq_of_eval_eq hS hHeadEval))
                    hTailEval
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
        exact False.elim
          (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))

theorem smt_model_eval_eo_to_smt_distinct_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {xs except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXsLt : sizeOf xs < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None)
    (hNoFree :
      __contains_atomic_term_list_free_rec xs except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt_distinct xs) =
    __smtx_model_eval N (__eo_to_smt_distinct xs) :=
by
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change
              __smtx_model_eval M (SmtTerm.Boolean true) =
                __smtx_model_eval N (SmtTerm.Boolean true)
            simp [__smtx_model_eval]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                let headTy := __smtx_typeof (__eo_to_smt head)
                let tailTy := __eo_to_smt_typed_list_elem_type tail
                have hGuard : native_Teq headTy tailTy = true := by
                  by_cases hGuard : native_Teq headTy tailTy = true
                  · exact hGuard
                  · exfalso
                    exact hElemNN (by
                      simp [__eo_to_smt_typed_list_elem_type, headTy,
                        tailTy, native_ite, hGuard])
                have hHeadNN : headTy ≠ SmtType.None := by
                  change
                    (native_ite (native_Teq headTy tailTy) headTy
                        SmtType.None) ≠
                      SmtType.None at hElemNN
                  rw [hGuard] at hElemNN
                  exact hElemNN
                have hTailNN : tailTy ≠ SmtType.None := by
                  intro hTailNone
                  cases hHead : headTy <;>
                    simp [headTy, tailTy, hHead, hTailNone, native_Teq]
                      at hGuard hHeadNN
                have hHeadTrans : eoHasSmtTranslation head := by
                  unfold eoHasSmtTranslation
                  simpa [headTy] using hHeadNN
                rcases
                  contains_atomic_term_list_free_rec_apply_apply_uop_false_args
                    hExcept hBound
                    (term_not_eo_list_cons_of_has_smt_translation hHeadTrans)
                    hNoFree with
                  ⟨hHeadNoFree, hTailNoFree⟩
                have hHeadEval :
                    __smtx_model_eval M (__eo_to_smt head) =
                      __smtx_model_eval N (__eo_to_smt head) :=
                  ih (by simp at hXsLt ⊢; omega)
                    hExcept hBound hHeadTrans hHeadNoFree hAgree
                have hPairsEval :
                    __smtx_model_eval M
                        (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                          tail) =
                      __smtx_model_eval N
                        (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                          tail) :=
                  smt_model_eval_eo_to_smt_distinct_pairs_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    root
                    (hXsLt := by simp at hXsLt ⊢; omega)
                    hExcept hBound
                    (by simpa [tailTy] using hTailNN)
                    hTailNoFree hAgree hHeadEval ih
                have hTailEval :
                    __smtx_model_eval M (__eo_to_smt_distinct tail) =
                      __smtx_model_eval N (__eo_to_smt_distinct tail) :=
                  smt_model_eval_eo_to_smt_distinct_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    root
                    (hXsLt := by simp at hXsLt ⊢; omega)
                    hExcept hBound
                    (by simpa [tailTy] using hTailNN)
                    hTailNoFree hAgree ih
                change
                  __smtx_model_eval M
                      (SmtTerm.and
                        (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                          tail)
                        (__eo_to_smt_distinct tail)) =
                    __smtx_model_eval N
                      (SmtTerm.and
                        (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                          tail)
                        (__eo_to_smt_distinct tail))
                exact
                  smtx_model_eval_and_eq_of_eval_eq
                    hPairsEval hTailEval
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
        exact False.elim
          (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))

theorem smt_model_eval_apply_distinct_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {xs except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXsLt : sizeOf xs < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.distinct) xs))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp UserOp.distinct) xs) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) :=
by
  have hXsNoFree :
      __contains_atomic_term_list_free_rec xs except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop_false_arg
      hExcept hBound hNoFree
  have hElemNN :
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None :=
    typed_list_elem_type_non_none_of_distinct_has_smt_translation hTrans
  have hDistinctEval :
      __smtx_model_eval M (__eo_to_smt_distinct xs) =
        __smtx_model_eval N (__eo_to_smt_distinct xs) :=
    smt_model_eval_eo_to_smt_distinct_eq_of_contains_atomic_term_list_free_rec_false_mapped
      root hXsLt hExcept hBound hElemNN hXsNoFree hAgree ih
  change
    __smtx_model_eval M
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) =
      __smtx_model_eval N
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs))
  by_cases hTeq :
      native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None = true
  · exfalso
    have hNone :
        __eo_to_smt_typed_list_elem_type xs = SmtType.None := by
      cases hTy : __eo_to_smt_typed_list_elem_type xs <;>
        simp [hTy, native_Teq] at hTeq ⊢
    exact hElemNN hNone
  · have hTeqFalse :
        native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None =
          false := by
      cases hTy :
          native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None <;>
        simp [hTy] at hTeq ⊢
    simpa [hTeqFalse, native_ite] using hDistinctEval

theorem smt_model_eval_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x)) :=
by
  cases op
  case not =>
    exact
      smt_model_eval_apply_not_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans hNoFree hAgree ih
  case distinct =>
    exact
      smt_model_eval_apply_distinct_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans hNoFree hAgree ih
  case _at_purify =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        purify_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case to_real =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        to_real_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case to_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        to_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case is_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        is_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case abs =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        abs_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case __eoo_neg_2 =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        uneg_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case int_pow2 =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        int_pow2_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case int_log2 =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        int_log2_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case int_ispow2 =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        int_ispow2_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case _at_int_div_by_zero =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        int_div_by_zero_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by
          intro hx
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hx, hAgree.globals.1,
            smtx_model_eval_apply_eq_of_globals hAgree.globals])
        ih
  case _at_mod_by_zero =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        mod_by_zero_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by
          intro hx
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hx, hAgree.globals.1,
            smtx_model_eval_apply_eq_of_globals hAgree.globals])
        ih
  case _at_div_by_zero =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by
          intro hx
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hx, hAgree.globals.1,
            smtx_model_eval_apply_eq_of_globals hAgree.globals])
        ih
  case _at_bvsize =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvsize_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by
          intro hx
          dsimp only [__eo_to_smt]
          cases h :
              native_zleq 0
                (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) <;>
            simp [native_ite, __smtx_model_eval])
        ih
  case bvnot =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvnot_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case bvneg =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvneg_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case bvnego =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvnego_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case bvredand =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvredand_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case bvredor =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        bvredor_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_len =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_len_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_rev =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_rev_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_to_lower =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_to_lower_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_to_upper =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_to_upper_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_to_code =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_to_code_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_from_code =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_from_code_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_is_digit =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_is_digit_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_to_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_to_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_from_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_from_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case _at_strings_stoi_non_digit =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case str_to_re =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        str_to_re_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case re_mult =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        re_mult_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case re_plus =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        re_plus_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case re_opt =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        re_opt_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case re_comp =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        re_comp_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case seq_unit =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        seq_unit_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case set_singleton =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        set_singleton_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case set_choose =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        set_choose_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case set_is_empty =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        set_is_empty_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case set_is_singleton =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        set_is_singleton_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case ubv_to_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        ubv_to_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case sbv_to_int =>
    exact
      smt_model_eval_apply_uop_unary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hXLt hExcept hBound hTrans
        sbv_to_int_arg_has_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by intro hx; dsimp only [__eo_to_smt]; simp [__smtx_model_eval, hx])
        ih
  case re_allchar =>
    exact false_of_apply_re_allchar hTrans
  case re_none =>
    exact false_of_apply_re_none hTrans
  case re_all =>
    exact false_of_apply_re_all hTrans
  case tuple_unit =>
    exact false_of_apply_tuple_unit hTrans
  all_goals
    exact false_of_apply_translate_apply_none hTrans rfl

theorem smt_model_eval_apply_apply_and_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :=
by
  rcases and_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_and_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_or_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :=
by
  rcases or_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_or_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_imp_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :=
by
  rcases imp_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_imp_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_xor_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :=
by
  rcases xor_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_xor_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_eq_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :=
by
  rcases eq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        (by decide) (by decide) hTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_eq_eq_of_eval_eq
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_uop_binary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hArgsTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp op) x) y) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) ->
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  rcases hArgsTrans hTrans with ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  exact
    hEval
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_strings_deq_diff_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)) :=
by
  rcases
    strings_deq_diff_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y))
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) :=
    ih hXLt hExcept hBound hXTrans hXNoFree hAgree
  have hYEval :
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) :=
    ih hYLt hExcept hBound hYTrans hYNoFree hAgree
  have hM :
      __smtx_model_eval M (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval_seq_diff (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
  have hN :
      __smtx_model_eval N (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval_seq_diff (__smtx_model_eval N (__eo_to_smt x))
          (__smtx_model_eval N (__eo_to_smt y)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hM, hN, hXEval, hYEval]

theorem smt_model_eval_eo_to_smt_set_insert_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {xs except bound : Term} {base : SmtTerm}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXsLt : sizeOf xs < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None)
    (hNoFree :
      __contains_atomic_term_list_free_rec xs except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBase :
      __smtx_model_eval M base = __smtx_model_eval N base)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt_set_insert xs base) =
    __smtx_model_eval N (__eo_to_smt_set_insert xs base) :=
by
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change
              __smtx_model_eval M
                  (native_ite
                    (native_Teq (__smtx_typeof base)
                      (SmtType.Set (__eo_to_smt_type tail)))
                    base SmtTerm.None) =
                __smtx_model_eval N
                  (native_ite
                    (native_Teq (__smtx_typeof base)
                      (SmtType.Set (__eo_to_smt_type tail)))
                    base SmtTerm.None)
            cases
                native_Teq (__smtx_typeof base)
                  (SmtType.Set (__eo_to_smt_type tail)) <;>
              simp [native_ite, __smtx_model_eval, hBase]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                let headTy := __smtx_typeof (__eo_to_smt head)
                let tailTy := __eo_to_smt_typed_list_elem_type tail
                have hGuard : native_Teq headTy tailTy = true := by
                  by_cases hGuard : native_Teq headTy tailTy = true
                  · exact hGuard
                  · exfalso
                    exact hElemNN (by
                      simp [__eo_to_smt_typed_list_elem_type, headTy,
                        tailTy, native_ite, hGuard])
                have hHeadNN : headTy ≠ SmtType.None := by
                  change
                    (native_ite (native_Teq headTy tailTy) headTy
                        SmtType.None) ≠
                      SmtType.None at hElemNN
                  rw [hGuard] at hElemNN
                  exact hElemNN
                have hTailNN : tailTy ≠ SmtType.None := by
                  intro hTailNone
                  cases hHead : headTy <;>
                    simp [headTy, tailTy, hHead, hTailNone, native_Teq]
                      at hGuard hHeadNN
                have hHeadTrans : eoHasSmtTranslation head := by
                  unfold eoHasSmtTranslation
                  simpa [headTy] using hHeadNN
                rcases
                  contains_atomic_term_list_free_rec_apply_apply_uop_false_args
                    hExcept hBound
                    (term_not_eo_list_cons_of_has_smt_translation hHeadTrans)
                    hNoFree with
                  ⟨hHeadNoFree, hTailNoFree⟩
                have hHeadEval :
                    __smtx_model_eval M (__eo_to_smt head) =
                      __smtx_model_eval N (__eo_to_smt head) :=
                  ih (by simp at hXsLt ⊢; omega)
                    hExcept hBound hHeadTrans hHeadNoFree hAgree
                have hTailEval :
                    __smtx_model_eval M
                        (__eo_to_smt_set_insert tail base) =
                      __smtx_model_eval N
                        (__eo_to_smt_set_insert tail base) :=
                  smt_model_eval_eo_to_smt_set_insert_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    root
                    (hXsLt := by simp at hXsLt ⊢; omega)
                    hExcept hBound
                    (by simpa [tailTy] using hTailNN)
                    hTailNoFree hAgree hBase ih
                change
                  __smtx_model_eval M
                      (SmtTerm.set_union
                        (SmtTerm.set_singleton (__eo_to_smt head))
                        (__eo_to_smt_set_insert tail base)) =
                    __smtx_model_eval N
                      (SmtTerm.set_union
                        (SmtTerm.set_singleton (__eo_to_smt head))
                        (__eo_to_smt_set_insert tail base))
                simp [__smtx_model_eval, hHeadEval, hTailEval]
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
        exact False.elim
          (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))

theorem smt_model_eval_apply_apply_set_insert_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {xs base except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXsLt : sizeOf xs < sizeOf root)
    (hBaseLt : sizeOf base < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
        base)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
        base)) :=
by
  rcases
    set_insert_base_has_smt_translation_and_typed_list_elem_type_non_none
      hTrans with
    ⟨hBaseTrans, hElemNN⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_uop_false_args
      hExcept hBound
      (typed_list_elem_type_non_none_not_eo_list_cons hElemNN)
      hNoFree with
    ⟨hXsNoFree, hBaseNoFree⟩
  have hBaseEval :
      __smtx_model_eval M (__eo_to_smt base) =
        __smtx_model_eval N (__eo_to_smt base) :=
    ih hBaseLt hExcept hBound hBaseTrans hBaseNoFree hAgree
  change
    __smtx_model_eval M
        (__eo_to_smt_set_insert xs (__eo_to_smt base)) =
      __smtx_model_eval N
        (__eo_to_smt_set_insert xs (__eo_to_smt base))
  exact
    smt_model_eval_eo_to_smt_set_insert_eq_of_contains_atomic_term_list_free_rec_false_mapped
      root hXsLt hExcept hBound hElemNN hXsNoFree hAgree hBaseEval ih

theorem smt_model_eval_apply_apply_apply_ite_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {c x y except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hCLt : sizeOf c < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :=
by
  rcases ite_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hCTrans, hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hCTrans)
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hCNoFree, hXNoFree, hYNoFree⟩
  change
    __smtx_model_eval M
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval N
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_ite_eq_of_eval_eq
      (ih hCLt hExcept hBound hCTrans hCNoFree hAgree)
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {c x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hCLt : sizeOf c < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y))
    (hArgsTrans :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y) ->
        eoHasSmtTranslation c ∧
          eoHasSmtTranslation x ∧
          eoHasSmtTranslation y)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt c) =
        __smtx_model_eval N (__eo_to_smt c) ->
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) =
        __smtx_model_eval N
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) :=
by
  rcases hArgsTrans hTrans with ⟨hCTrans, hXTrans, hYTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hCTrans)
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      hNoFree with
    ⟨hCNoFree, hXNoFree, hYNoFree⟩
  exact
    hEval
      (ih hCLt hExcept hBound hCTrans hCNoFree hAgree)
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)

theorem contains_atomic_term_list_free_rec_apply_apply_apply_apply_uop_false_args
    {op : UserOp} {w z y x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hWNotList :
      ∀ v vs,
        w ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hZNotList :
      ∀ v vs,
        z ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hYNotList :
      ∀ v vs,
        y ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)
          except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec w except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec z except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hYNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hXNoFree⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_uop_false_args
      hExcept hBound hWNotList hZNotList hHeadNoFree with
    ⟨hWNoFree, hZNoFree, hYNoFree⟩
  exact ⟨hWNoFree, hZNoFree, hYNoFree, hXNoFree⟩

theorem smt_model_eval_apply_apply_apply_apply_uop_quaternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {w z y x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hWLt : sizeOf w < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x))
    (hArgsTrans :
      eoHasSmtTranslation
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y)
            x) ->
        eoHasSmtTranslation w ∧
          eoHasSmtTranslation z ∧
          eoHasSmtTranslation y ∧
          eoHasSmtTranslation x)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hEval :
      __smtx_model_eval M (__eo_to_smt w) =
        __smtx_model_eval N (__eo_to_smt w) ->
      __smtx_model_eval M (__eo_to_smt z) =
        __smtx_model_eval N (__eo_to_smt z) ->
      __smtx_model_eval M (__eo_to_smt y) =
        __smtx_model_eval N (__eo_to_smt y) ->
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt x) ->
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y)
              x)) =
        __smtx_model_eval N
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y)
              x)))
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y) x)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) w) z) y)
          x)) :=
by
  rcases hArgsTrans hTrans with ⟨hWTrans, hZTrans, hYTrans, hXTrans⟩
  rcases
    contains_atomic_term_list_free_rec_apply_apply_apply_apply_uop_false_args
      hExcept hBound
      (term_not_eo_list_cons_of_has_smt_translation hWTrans)
      (term_not_eo_list_cons_of_has_smt_translation hZTrans)
      (term_not_eo_list_cons_of_has_smt_translation hYTrans)
      hNoFree with
    ⟨hWNoFree, hZNoFree, hYNoFree, hXNoFree⟩
  exact
    hEval
      (ih hWLt hExcept hBound hWTrans hWNoFree hAgree)
      (ih hZLt hExcept hBound hZTrans hZNoFree hAgree)
      (ih hYLt hExcept hBound hYTrans hYNoFree hAgree)
      (ih hXLt hExcept hBound hXTrans hXNoFree hAgree)

/--
Evaluator congruence for the SMT existential chain produced from an exact EO
binder list.

The body hypothesis is stated at the final bound stack
`binderVars.reverse ++ boundVars`, because SMT evaluation pushes the binders in
front of the current model one at a time.
-/
theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval N (__eo_to_smt_exists vs body) :=
by
  induction hEnv generalizing boundVars M N body with
  | nil =>
      exact hBody (by simpa using hAgree)
  | cons hTail ih =>
      rename_i s T vs tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body))
      exact
        smtx_model_eval_exists_eq_of_body_eval_eq
          (fun v =>
            ih
              (boundVars := (s, T) :: boundVars)
              (M := native_model_push M s (__eo_to_smt_type T) v)
              (N := native_model_push N s (__eo_to_smt_type T) v)
              (body := body)
              (model_agrees_except_on_eo_env_push_same hAgree)
              (by
                intro M' N' hAgreeTail
                apply hBody
                simpa [List.reverse_cons, List.append_assoc]
                  using hAgreeTail))

/--
Evaluator congruence for the SMT encoding of EO `forall`.

EO forall translates through `not (exists ... (not body))`, so this is just the
existential-chain congruence with two `not` congruence steps.
-/
theorem smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) =
    __smtx_model_eval N
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) :=
by
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
        hEnv hAgree
      (by
        intro M' N' hAgree'
        exact smtx_model_eval_not_eq_of_eval_eq (hBody hAgree')))

theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval N (__eo_to_smt_exists vs body) :=
by
  induction hEnv generalizing boundVars M N body with
  | nil =>
      exact hBody (by simpa using hAgree)
  | cons hTail ih =>
      rename_i s T vs tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body))
      exact
        smtx_model_eval_exists_eq_of_body_eval_eq
          (fun v =>
            ih
              (boundVars := (s, T) :: boundVars)
              (M := native_model_push M s (__eo_to_smt_type T) v)
              (N := native_model_push N s (__eo_to_smt_type T) v)
              (body := body)
              (by
                simpa [EoVarKey.toSmt] using
                  model_agrees_except_on_env_push_same hAgree)
              (by
                intro M' N' hAgreeTail
                apply hBody
                simpa [List.reverse_cons, List.append_assoc,
                  List.map_append, EoVarKey.toSmt] using hAgreeTail))

theorem smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq_mapped
    {vs : Term} {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body) :
  __smtx_model_eval M
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) =
    __smtx_model_eval N
      (SmtTerm.not (__eo_to_smt_exists vs (SmtTerm.not body))) :=
by
  exact
    smtx_model_eval_not_eq_of_eval_eq
      (smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
        hEnv hAgree
        (by
          intro M' N' hAgree'
          exact smtx_model_eval_not_eq_of_eval_eq (hBody hAgree')))

/--
Evaluator congruence for the nonempty quantifier-shaped EO branch.

The free-variable checker treats any `Apply (Apply q nonempty-list) body` as a
binder branch; the translation proof tells us that the head is actually
`forall` or `exists`.
-/
theorem smt_model_eval_uop_list_branch_eq_of_body_eval_eq
    {op : UserOp} {v vs body : Term}
    {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hEnv :
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hAgree : model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_eo_env exceptVars
          (binderVars.reverse ++ boundVars) M' N' ->
          __smtx_model_eval M' (__eo_to_smt body) =
            __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    change
      __smtx_model_eval M
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        __smtx_model_eval N
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body))))
    exact
      smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq
        hEnv hAgree hBody
  · subst op
    change
      __smtx_model_eval M
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        __smtx_model_eval N
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body))
    exact
      smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq
        hEnv hAgree hBody

theorem smt_model_eval_uop_list_branch_eq_of_body_eval_eq_mapped
    {op : UserOp} {v vs body : Term}
    {binderVars exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hEnv :
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt)
          ((binderVars.reverse ++ boundVars).map EoVarKey.toSmt)
          M' N' ->
          __smtx_model_eval M' (__eo_to_smt body) =
            __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    change
      __smtx_model_eval M
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        __smtx_model_eval N
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body))))
    exact
      smt_model_eval_eo_to_smt_forall_encoding_eq_of_body_eval_eq_mapped
        hEnv hAgree hBody
  · subst op
    change
      __smtx_model_eval M
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        __smtx_model_eval N
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body))
    exact
      smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_mapped
        hEnv hAgree hBody

private theorem eo_requires_true_false_eq_false
    {c : Term}
    (h :
      __eo_requires c (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false) :
  c = Term.Boolean true :=
by
  cases c <;> simp [__eo_requires, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢

/--
Fallback case for `__contains_atomic_term_list_free_rec`.

For non-recursive terms, the checker returns `false` by first proving that the
term is closed at the empty environment.  Under SMT translation, closed EO terms
evaluate the same in any two models that agree on globals.
-/
theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __eo_requires (__is_closed_rec t Term.__eo_List_nil)
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  have hClosedRec :
      __is_closed_rec t Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_true_false_eq_false hNoFree
  have hClosed :
      __eo_is_closed t = Term.Boolean true := by
    simpa [is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
      using hClosedRec
  exact smt_model_eval_eq_of_eo_closed t hClosed M N hAgree.globals

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback_mapped
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __eo_requires (__is_closed_rec t Term.__eo_List_nil)
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  have hClosedRec :
      __is_closed_rec t Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_true_false_eq_false hNoFree
  have hClosed :
      __eo_is_closed t = Term.Boolean true := by
    simpa [is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
      using hClosedRec
  exact smt_model_eval_eq_of_eo_closed t hClosed M N hAgree.globals

theorem contains_atomic_term_list_free_rec_fallback_eq_of_shape
    {t except bound : Term}
    (hExcept : except ≠ Term.Stuck)
    (hBound : bound ≠ Term.Stuck)
    (hNotStuck : t ≠ Term.Stuck)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNotVar : ∀ name T, t ≠ Term.Var name T)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false) :
  __eo_requires (__is_closed_rec t Term.__eo_List_nil)
      (Term.Boolean true) (Term.Boolean false) =
    Term.Boolean false :=
by
  cases t
  case Stuck =>
    exact False.elim (hNotStuck rfl)
  case Apply f a =>
    exact False.elim (hNotApply f a rfl)
  case Var name T =>
    exact False.elim (hNotVar name T rfl)
  all_goals
    cases except <;> cases bound <;>
      simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact hNoFree

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
    {t except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation t)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  cases t
  case Stuck =>
      simp [__contains_atomic_term_list_free_rec] at hNoFree
  case Apply f a =>
      exact False.elim (hNotApply f a rfl)
  case Var name T =>
      cases name
      case String s =>
          exact
            smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false_mapped
              hExcept hBound
              (smtx_type_wf_of_var_has_smt_translation hTrans)
              hNoFree hAgree
      all_goals
        exfalso
        unfold eoHasSmtTranslation at hTrans
        change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
        exact hTrans TranslationProofs.smtx_typeof_none
  all_goals
    have hReq :=
      contains_atomic_term_list_free_rec_fallback_eq_of_shape
        (EoVarEnvPerm.ne_stuck hExcept)
        (EoVarEnvPerm.ne_stuck hBound)
        (by intro h; cases h)
        hNotApply
        (by intro name T h; cases h)
        hNoFree
    exact
      smt_model_eval_eq_of_contains_atomic_term_list_free_rec_fallback_mapped
        (except := except) (bound := bound) hTrans hReq hAgree

/--
The obligations needed by the recursive semantic proof in the quantifier-shaped
`UOp` branch.

When the branch has an SMT translation and the free-variable check returns
`false`, the body is translation-safe, the binder list is an exact EO variable
environment, the bound stack extends by that binder list, and the body inherits
the `false` free-variable check under the extended bound stack.
-/
theorem body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
    {op : UserOp} {v vs body except bound : Term}
    {boundVars : List EoVarKey}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false) :
  eoHasSmtTranslation body ∧
    ∃ binderVars,
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars ∧
      EoVarEnvPerm
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
        (binderVars.reverse ++ boundVars) ∧
      __contains_atomic_term_list_free_rec body except
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
        Term.Boolean false :=
by
  have hBodyTrans :
      eoHasSmtTranslation body :=
    body_has_smt_translation_of_uop_list_branch_has_smt_translation
      hTrans
  rcases eo_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact
    ⟨hBodyTrans,
      ⟨binderVars, hBinderEnv,
        EoVarEnvPerm.concat_rev hBinderEnv hBound,
        contains_atomic_term_list_free_rec_list_branch_false_body
          hNoFree⟩⟩

theorem body_has_smt_translation_of_list_branch_has_smt_translation
    {q v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans
  · subst q
    exact
      body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans

/--
Raw generated-list-branch obligations.

This is the same package as the `UOp`-specific theorem above, but it matches
the actual first clause of `__contains_atomic_term_list_free_rec`, whose head is
an arbitrary term `q`.  SMT translation forces `q` to be a real quantifier.
-/
theorem body_obligations_of_contains_atomic_term_list_free_rec_list_branch
    {q v vs body except bound : Term}
    {boundVars : List EoVarKey}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false) :
  eoHasSmtTranslation body ∧
    ∃ binderVars,
      EoVarEnv
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) binderVars ∧
      EoVarEnvPerm
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
        (binderVars.reverse ++ boundVars) ∧
      __contains_atomic_term_list_free_rec body except
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
        Term.Boolean false :=
by
  have hBodyTrans :
      eoHasSmtTranslation body :=
    body_has_smt_translation_of_list_branch_has_smt_translation hTrans
  rcases eo_var_env_of_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact
    ⟨hBodyTrans,
      ⟨binderVars, hBinderEnv,
        EoVarEnvPerm.concat_rev hBinderEnv hBound,
        contains_atomic_term_list_free_rec_list_branch_false_body
          hNoFree⟩⟩

/--
One-step semantic theorem for the quantifier-shaped branch.

This is the hook needed by the main recursive proof: once the recursive
hypothesis can prove the body under the extended bound stack, this theorem
turns that into evaluation equality for the whole quantified term.
-/
theorem smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
    {op : UserOp} {v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_eo_env exceptVars bodyBoundVars M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
      hBound hTrans hNoFree with
    ⟨hBodyTrans, binderVars, hBinderEnv, hExtendedBound, hBodyNoFree⟩
  exact
    smt_model_eval_uop_list_branch_eq_of_body_eval_eq
      hBinderEnv hTrans hAgree
      (by
        intro M' N' hAgree'
        exact
          hBodyEval hBodyTrans hExtendedBound hBodyNoFree hAgree')

theorem smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {op : UserOp} {v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_env
              (exceptVars.map EoVarKey.toSmt)
              (bodyBoundVars.map EoVarKey.toSmt) M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    body_obligations_of_contains_atomic_term_list_free_rec_uop_list_branch
      hBound hTrans hNoFree with
    ⟨hBodyTrans, binderVars, hBinderEnv, hExtendedBound, hBodyNoFree⟩
  exact
    smt_model_eval_uop_list_branch_eq_of_body_eval_eq_mapped
      hBinderEnv hTrans hAgree
      (by
        intro M' N' hAgree'
        exact
          hBodyEval hBodyTrans hExtendedBound hBodyNoFree hAgree')

/--
One-step semantic theorem for the raw generated quantifier/list branch.

This is the branch hook with the exact shape generated by
`__contains_atomic_term_list_free_rec`.
-/
theorem smt_model_eval_list_branch_eq_of_contains_atomic_term_list_free_rec_false
    {q v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_eo_env exceptVars bodyBoundVars M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
        hBound hTrans hNoFree hAgree hBodyEval
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false
        hBound hTrans hNoFree hAgree hBodyEval

theorem smt_model_eval_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {q v vs body except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (hBodyEval :
      eoHasSmtTranslation body ->
        ∀ {bodyBoundVars : List EoVarKey},
          EoVarEnvPerm
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound)
            bodyBoundVars ->
          __contains_atomic_term_list_free_rec body except
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bound) =
            Term.Boolean false ->
          ∀ {M' N' : SmtModel},
            model_agrees_except_on_env
              (exceptVars.map EoVarKey.toSmt)
              (bodyBoundVars.map EoVarKey.toSmt) M' N' ->
              __smtx_model_eval M' (__eo_to_smt body) =
                __smtx_model_eval N' (__eo_to_smt body)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :=
by
  rcases
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hBound hTrans hNoFree hAgree hBodyEval


  · subst q
    exact
      smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hBound hTrans hNoFree hAgree hBodyEval

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_sel
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
        ∀ s d i j,
          __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
            SmtTerm.DtSel s d i j
  | native_nat_zero, acc, hAcc, s, d, i, j => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i j
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i, _j => by
      intro h
      cases h

private theorem eo_to_smt_tuple_prepend_rec_ne_dt_tester
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
        ∀ s d i,
          __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
            SmtTerm.DtTester s d i
  | native_nat_zero, acc, hAcc, s, d, i => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i => by
      intro h
      cases h

private theorem smt_model_eval_tuple_prepend_rec_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail acc : SmtTerm)
    (hTail : __smtx_model_eval M tail = __smtx_model_eval N tail)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hAcc : __smtx_model_eval M acc = __smtx_model_eval N acc) :
    ∀ k,
      __smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
        __smtx_model_eval N
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc)
  | native_nat_zero => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc
  | native_nat_succ k => by
      let recTerm :=
        __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc
      let argTerm :=
        SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD
          native_nat_zero k) tail
      have hRecEval :
          __smtx_model_eval M recTerm =
            __smtx_model_eval N recTerm := by
        simpa [recTerm] using
          smt_model_eval_tuple_prepend_rec_eq_of_eval_eq hGlobals
            tailDD tailD tail acc hTail hAccSel hAccTester hAcc k
      have hArgEval :
          __smtx_model_eval M argTerm =
            __smtx_model_eval N argTerm := by
        simp [argTerm, __smtx_model_eval, hTail,
          smtx_model_eval_dt_sel_eq_of_globals hGlobals]
      have hGen : generic_apply_eval recTerm argTerm :=
        generic_apply_eval_of_non_datatype_head
          (by
            intro s d i j h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_sel tailDD tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              eo_to_smt_tuple_prepend_rec_ne_dt_tester tailDD tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      unfold generic_apply_eval at hGen
      change
        __smtx_model_eval M (SmtTerm.Apply recTerm argTerm) =
          __smtx_model_eval N (SmtTerm.Apply recTerm argTerm)
      rw [hGen M, hGen N, hRecEval, hArgEval]
      exact smtx_model_eval_apply_eq_of_globals hGlobals _ _

private theorem smt_model_eval_tuple_prepend_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (head tail : SmtTerm) (headTy : SmtType)
    (hHead : __smtx_model_eval M head = __smtx_model_eval N head)
    (hTail : __smtx_model_eval M tail = __smtx_model_eval N tail) :
    __smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail) =
      __smtx_model_eval N (__eo_to_smt_tuple_prepend head headTy tail) := by
  unfold __eo_to_smt_tuple_prepend
  cases hTailTy : __smtx_typeof tail with
  | Datatype s dd =>
      cases dd with
      | nil =>
          simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
      | cons s2 d rest =>
          cases rest with
          | cons s3 d3 rest3 =>
              simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
          | nil =>
              cases d with
              | null =>
                  simp [__eo_to_smt_tuple_prepend_of_type,
                    __smtx_model_eval]
              | sum c drest =>
                  cases drest with
                  | sum c' rest' =>
                      simp [__eo_to_smt_tuple_prepend_of_type,
                        __smtx_model_eval]
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 :
                            s2 = native_string_lit "@Tuple"
                        · subst s2
                          let tailD :=
                            SmtDatatype.sum c SmtDatatype.null
                          let tailDD :=
                            __eo_to_smt_tuple_decl tailD
                          let fullD :=
                            SmtDatatype.sum
                              (SmtDatatypeCons.cons headTy c)
                              SmtDatatype.null
                          let fullDD :=
                            __eo_to_smt_tuple_decl fullD
                          let seed :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons
                                (native_string_lit "@Tuple") fullDD
                                native_nat_zero) head
                          cases hWf :
                              __smtx_type_wf
                                (SmtType.Datatype
                                  (native_string_lit "@Tuple") fullDD)
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_streq, native_and, hWf,
                              __smtx_model_eval]
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_streq, native_and, hWf]
                            exact
                              smt_model_eval_tuple_prepend_rec_eq_of_eval_eq
                                hGlobals tailDD tailD tail seed hTail
                                (by
                                  intro s d i j h
                                  simp [seed] at h)
                                (by
                                  intro s d i h
                                  simp [seed] at h)
                                (by
                                  simp [seed, __smtx_model_eval, hHead,
                                    smtx_model_eval_apply_eq_of_globals
                                      hGlobals])
                                (__smtx_dt_num_sels tailD
                                  native_nat_zero)
                        · simp [__eo_to_smt_tuple_prepend_of_type, hs2,
                            native_streq, native_and, native_ite,
                            __smtx_model_eval]
                      · simp [__eo_to_smt_tuple_prepend_of_type, hs,
                          native_streq, native_and, native_ite,
                          __smtx_model_eval]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]

private theorem apply_apply_uop_bv_binop_args_have_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y : Term}
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y := by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      hTranslate
      (fun hNN => bv_binop_args_have_smt_translation_of_non_none hTy hNN)
      hTrans

private theorem apply_apply_uop_bv_binop_ret_args_have_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y : Term}
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y := by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      hTranslate
      (fun hNN => bv_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      hTrans

theorem smt_model_eval_apply_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp op) x) y) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) :=
by
  cases op
  case «forall» =>
    by_cases hCons :
        ∃ v vs, x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    · rcases hCons with ⟨v, vs, hX⟩
      subst x
      exact
        smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hBound hTrans hNoFree hAgree
          (by
            intro hBodyTrans bodyBoundVars hBodyBound hBodyNoFree M' N' hAgree'
            exact ih hYLt hExcept hBodyBound hBodyTrans hBodyNoFree hAgree')
    · exact
        false_of_forall_non_list_has_smt_translation
          (by intro v vs hX; exact hCons ⟨v, vs, hX⟩) hTrans
  case «exists» =>
    by_cases hCons :
        ∃ v vs, x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    · rcases hCons with ⟨v, vs, hX⟩
      subst x
      exact
        smt_model_eval_uop_list_branch_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hBound hTrans hNoFree hAgree
          (by
            intro hBodyTrans bodyBoundVars hBodyBound hBodyNoFree M' N' hAgree'
            exact ih hYLt hExcept hBodyBound hBodyTrans hBodyNoFree hAgree')
    · exact
        false_of_exists_non_list_has_smt_translation
          (by intro v vs hX; exact hCons ⟨v, vs, hX⟩) hTrans
  all_goals
    first
    | exact
        smt_model_eval_apply_apply_strings_deq_diff_eq_of_contains_atomic_term_list_free_rec_false_mapped
          root hXLt hYLt hExcept hBound hTrans hNoFree hAgree ih
    | exact
        smt_model_eval_apply_apply_set_insert_eq_of_contains_atomic_term_list_free_rec_false_mapped
          root hXLt hYLt hExcept hBound hTrans hNoFree hAgree ih
    | exact
        smt_model_eval_apply_apply_uop_binary_eq_of_contains_atomic_term_list_free_rec_false_mapped
          root hXLt hYLt hExcept hBound hTrans
          (by
            intro h
            exact array_deq_diff_args_have_smt_translation_of_has_smt_translation h)
          hNoFree hAgree
          (by
            intro hx hy
            dsimp only [__eo_to_smt]
            simp only [__eo_to_smt_array_deq_diff]
            cases hXTy : __smtx_typeof (__eo_to_smt x) <;>
              cases hYTy : __smtx_typeof (__eo_to_smt y) <;>
              simp [__smtx_model_eval, __smtx_model_eval_map_diff,
                hx, hy])
          ih
    | exact
        smt_model_eval_apply_apply_uop_binary_eq_of_contains_atomic_term_list_free_rec_false_mapped
          root hXLt hYLt hExcept hBound hTrans
          (by
            intro h
            exact sets_deq_diff_args_have_smt_translation_of_has_smt_translation h)
          hNoFree hAgree
          (by
            intro hx hy
            dsimp only [__eo_to_smt]
            simp only [__eo_to_smt_sets_deq_diff]
            cases hXTy : __smtx_typeof (__eo_to_smt x) <;>
              cases hYTy : __smtx_typeof (__eo_to_smt y) <;>
              simp [__smtx_model_eval, __smtx_model_eval_map_diff,
                hx, hy])
          ih
    | exact
        smt_model_eval_apply_apply_uop_binary_eq_of_contains_atomic_term_list_free_rec_false_mapped
          root hXLt hYLt hExcept hBound hTrans
          (by
            intro h
            first
            | exact and_args_have_smt_translation_of_has_smt_translation h
            | exact or_args_have_smt_translation_of_has_smt_translation h
            | exact imp_args_have_smt_translation_of_has_smt_translation h
            | exact xor_args_have_smt_translation_of_has_smt_translation h
            | exact eq_args_have_smt_translation_of_has_smt_translation h
            | exact plus_args_have_smt_translation_of_has_smt_translation h
            | exact neg_args_have_smt_translation_of_has_smt_translation h
            | exact mult_args_have_smt_translation_of_has_smt_translation h
            | exact lt_args_have_smt_translation_of_has_smt_translation h
            | exact leq_args_have_smt_translation_of_has_smt_translation h
            | exact gt_args_have_smt_translation_of_has_smt_translation h
            | exact geq_args_have_smt_translation_of_has_smt_translation h
            | exact div_args_have_smt_translation_of_has_smt_translation h
            | exact mod_args_have_smt_translation_of_has_smt_translation h
            | exact divisible_args_have_smt_translation_of_has_smt_translation h
            | exact div_total_args_have_smt_translation_of_has_smt_translation h
            | exact mod_total_args_have_smt_translation_of_has_smt_translation h
            | exact select_args_have_smt_translation_of_has_smt_translation h
            | exact array_deq_diff_args_have_smt_translation_of_has_smt_translation h
            | exact strings_stoi_result_args_have_smt_translation_of_has_smt_translation h
            | exact strings_itos_result_args_have_smt_translation_of_has_smt_translation h
            | exact strings_num_occur_args_have_smt_translation_of_has_smt_translation h
            | exact strings_num_occur_re_args_have_smt_translation_of_has_smt_translation h
            | exact tuple_args_have_smt_translation_of_has_smt_translation h
            | exact sets_deq_diff_args_have_smt_translation_of_has_smt_translation h
            | exact qdiv_args_have_smt_translation_of_has_smt_translation h
            | exact qdiv_total_args_have_smt_translation_of_has_smt_translation h
            | exact bvultbv_args_have_smt_translation_of_has_smt_translation h
            | exact bvsltbv_args_have_smt_translation_of_has_smt_translation h
            | exact from_bools_args_have_smt_translation_of_has_smt_translation h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
                  (by rfl) bv_concat_args_have_smt_translation_of_non_none h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvnand) (smtOp := SmtTerm.bvnand)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvnor) (smtOp := SmtTerm.bvnor)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvxor) (smtOp := SmtTerm.bvxor)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvxnor) (smtOp := SmtTerm.bvxnor)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvcomp) (smtOp := SmtTerm.bvcomp)
                  (ret := SmtType.BitVec Nat.zero.succ)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvadd) (smtOp := SmtTerm.bvadd)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvmul) (smtOp := SmtTerm.bvmul)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvudiv) (smtOp := SmtTerm.bvudiv)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvurem) (smtOp := SmtTerm.bvurem)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvsub) (smtOp := SmtTerm.bvsub)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvsdiv) (smtOp := SmtTerm.bvsdiv)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvsrem) (smtOp := SmtTerm.bvsrem)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvsmod) (smtOp := SmtTerm.bvsmod)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvult) (smtOp := SmtTerm.bvult)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvule) (smtOp := SmtTerm.bvule)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvugt) (smtOp := SmtTerm.bvugt)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvuge) (smtOp := SmtTerm.bvuge)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvslt) (smtOp := SmtTerm.bvslt)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsle) (smtOp := SmtTerm.bvsle)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsgt) (smtOp := SmtTerm.bvsgt)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsge) (smtOp := SmtTerm.bvsge)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvshl) (smtOp := SmtTerm.bvshl)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvlshr) (smtOp := SmtTerm.bvlshr)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_args_have_smt_translation
                  (eoOp := UserOp.bvashr) (smtOp := SmtTerm.bvashr)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvuaddo) (smtOp := SmtTerm.bvuaddo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsaddo) (smtOp := SmtTerm.bvsaddo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvumulo) (smtOp := SmtTerm.bvumulo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsmulo) (smtOp := SmtTerm.bvsmulo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvusubo) (smtOp := SmtTerm.bvusubo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvssubo) (smtOp := SmtTerm.bvssubo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_bv_binop_ret_args_have_smt_translation
                  (eoOp := UserOp.bvsdivo) (smtOp := SmtTerm.bvsdivo)
                  (ret := SmtType.Bool)
                  (by rfl) (by rw [__smtx_typeof.eq_def]) h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_binop_args_have_smt_translation_of_non_none
                      (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y))
                      hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_binop_ret_args_have_smt_translation_of_non_none
                      (typeof_str_contains_eq (__eo_to_smt x) (__eo_to_smt y))
                      hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl) str_at_args_have_smt_translation_of_non_none h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_binop_ret_args_have_smt_translation_of_non_none
                      (typeof_str_prefixof_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_binop_ret_args_have_smt_translation_of_non_none
                      (typeof_str_suffixof_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_char_binop_args_have_smt_translation_of_non_none
                      (ret := SmtType.Bool)
                      (typeof_str_lt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_char_binop_args_have_smt_translation_of_non_none
                      (ret := SmtType.Bool)
                      (typeof_str_leq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_char_binop_args_have_smt_translation_of_non_none
                      (ret := SmtType.RegLan)
                      (typeof_re_range_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    reglan_binop_args_have_smt_translation_of_non_none
                      (typeof_re_concat_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    reglan_binop_args_have_smt_translation_of_non_none
                      (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    reglan_binop_args_have_smt_translation_of_non_none
                      (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    reglan_binop_args_have_smt_translation_of_non_none
                      (typeof_re_diff_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    seq_char_reglan_args_have_smt_translation_of_non_none
                      (ret := SmtType.Bool)
                      (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl) seq_nth_args_have_smt_translation_of_non_none h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    set_binop_args_have_smt_translation_of_non_none
                      (typeof_set_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    set_binop_args_have_smt_translation_of_non_none
                      (typeof_set_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    set_binop_args_have_smt_translation_of_non_none
                      (typeof_set_minus_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl) set_member_args_have_smt_translation_of_non_none h
            | exact
                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                  (by rfl)
                  (fun hNN =>
                    set_binop_ret_args_have_smt_translation_of_non_none
                      (ret := SmtType.Bool)
                      (typeof_set_subset_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
                  h)
          hNoFree hAgree
          (by
            intro hx hy
            dsimp only [__eo_to_smt]
            first
            | exact
                smt_model_eval_tuple_prepend_eq_of_eval_eq hAgree.globals
                  (__eo_to_smt x) (__eo_to_smt y)
                  (__smtx_typeof (__eo_to_smt x)) hx hy
            | simp [__smtx_model_eval, hx, hy, hAgree.globals.1,
              smtx_model_eval_apply_eq_of_globals hAgree.globals,
              smtx_seq_nth_eq_of_globals hAgree.globals])
          ih
    | exact
        smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hExcept hBound
          (by
            intro q v vs hEq
            cases hEq
            exact
              apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
                (by decide) (by decide) hTrans v vs rfl)
          (by rfl)
          (generic_apply_type_of_non_special_head_closed _ _
            (by
              intro s d i j hSel
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_sel
                  _ _ s d i j hSel)
            (by
              intro s d i hTester
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_tester
                  _ x s d i hTester))
          hTrans hNoFree hAgree
          (by
            intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
            exact
              smt_model_eval_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
                root hXLt hExcept hBound' hHeadTrans hHeadNoFree hAgree' ih)
          (by
            intro hYTrans hBound' hYNoFree M' N' hAgree'
            exact ih hYLt hExcept hBound' hYTrans hYNoFree hAgree')

theorem smt_model_eval_eq_of_eo_to_smt_nat_is_valid
    {idx : Term} {M N : SmtModel}
    (hValid : __eo_to_smt_nat_is_valid idx = true) :
  __smtx_model_eval M (__eo_to_smt idx) =
    __smtx_model_eval N (__eo_to_smt idx) :=
by
  cases idx <;> simp [__eo_to_smt_nat_is_valid] at hValid
  case Numeral n =>
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]

theorem smt_model_eval_eq_of_eo_to_smt_numeral
    {idx : Term} {M N : SmtModel} {i : native_Int}
    (hIdx : __eo_to_smt idx = SmtTerm.Numeral i) :
  __smtx_model_eval M (__eo_to_smt idx) =
    __smtx_model_eval N (__eo_to_smt idx) :=
by
  have hIdxTerm : idx = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral idx i hIdx
  subst idx
  change __smtx_model_eval M (SmtTerm.Numeral i) =
    __smtx_model_eval N (SmtTerm.Numeral i)
  rw [__smtx_model_eval.eq_2, __smtx_model_eval.eq_2]

theorem smt_model_eval_eq_of_eo_to_smt_eq_dt_sel
    {idx : Term} {M N : SmtModel}
    {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat}
    (hSel : __eo_to_smt idx = SmtTerm.DtSel s d i j) :
  __smtx_model_eval M (__eo_to_smt idx) =
    __smtx_model_eval N (__eo_to_smt idx) :=
by
  rw [hSel]
  simp [__smtx_model_eval]

theorem smt_model_eval_eq_of_eo_to_smt_eq_dt_cons
    {idx : Term} {M N : SmtModel}
    {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat}
    (hCons : __eo_to_smt idx = SmtTerm.DtCons s d i) :
  __smtx_model_eval M (__eo_to_smt idx) =
    __smtx_model_eval N (__eo_to_smt idx) :=
by
  rw [hCons]
  simp [__smtx_model_eval]

theorem contains_atomic_term_list_free_rec_apply_uop1_false_arg
    {op : UserOp1} {idx x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp1 op idx) x) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
    Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hArgNoFree⟩
  exact hArgNoFree

theorem contains_atomic_term_list_free_rec_apply_apply_uop1_false_args
    {op : UserOp1} {idx x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
          except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
      Term.Boolean false ∧
    __contains_atomic_term_list_free_rec y except bound =
      Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by
        intro q v vs hEq
        cases hEq
        exact hXNotList v vs rfl)
      hNoFree with
    ⟨hHeadNoFree, hYNoFree⟩
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hHeadNoFree with
    ⟨hOpNoFree, hXNoFree⟩
  exact ⟨hXNoFree, hYNoFree⟩

theorem contains_atomic_term_list_free_rec_apply_uop2_false_arg
    {op : UserOp2} {i j x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp2 op i j) x) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
    Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hArgNoFree⟩
  exact hArgNoFree

theorem contains_atomic_term_list_free_rec_apply_uop3_false_arg
    {op : UserOp3} {a b c x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp3 op a b c) x) except bound =
        Term.Boolean false) :
  __contains_atomic_term_list_free_rec x except bound =
    Term.Boolean false :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hArgNoFree⟩
  exact hArgNoFree

theorem smt_model_eval_apply_uop1_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp1} {idx x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp1 op idx) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) :=
by
  have hXNoFree :
      __contains_atomic_term_list_free_rec x except bound =
        Term.Boolean false :=
    contains_atomic_term_list_free_rec_apply_uop1_false_arg
      hExcept hBound hNoFree
  cases op
  case «repeat» =>
    rcases repeat_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case zero_extend =>
    rcases zero_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case sign_extend =>
    rcases sign_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case rotate_left =>
    rcases rotate_left_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case rotate_right =>
    rcases rotate_right_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case _at_bit =>
    rcases at_bit_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case re_exp =>
    rcases re_exp_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case is =>
    rcases is_index_cons_and_arg_has_smt_translation hTrans with
      ⟨⟨s, d, i, hCons⟩, hXTrans⟩
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    rw [hCons]
    simp only [__eo_to_smt_tester, __smtx_model_eval]
    simp [hXEval]
  case tuple_select =>
    rcases tuple_select_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    cases idx <;> simp [__eo_to_smt_nat_is_valid] at hIdxValid
    case Numeral n =>
      dsimp only [__eo_to_smt]
      cases hTy : __smtx_typeof (__eo_to_smt x)
      case Datatype s dd =>
        cases dd with
        | nil =>
            simp [__eo_to_smt_tuple_select, __smtx_model_eval]
        | cons s2 d rest =>
            cases rest with
            | cons s3 d3 rest3 =>
                simp [__eo_to_smt_tuple_select, __smtx_model_eval]
            | nil =>
                cases hGuard :
                    native_and
                      (native_and
                        (native_streq s (native_string_lit "@Tuple"))
                        (native_streq s2 (native_string_lit "@Tuple")))
                      (native_zleq 0 n)
                · simp [__eo_to_smt_tuple_select, hGuard, native_ite,
                    __smtx_model_eval]
                · simp [__eo_to_smt_tuple_select, hGuard, native_ite,
                    __smtx_model_eval, hXEval]
                  exact
                    smtx_model_eval_dt_sel_eq_of_globals hAgree.globals
                      (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl d) 0
                      (native_int_to_nat n)
                      (__smtx_model_eval N (__eo_to_smt x))
      all_goals
        simp [__eo_to_smt_tuple_select, __smtx_model_eval]
  case int_to_bv =>
    rcases int_to_bv_index_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIdxValid, hXTrans⟩
    have hIdxEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIdxValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIdxEval, hXEval]
  case seq_empty =>
    exact false_of_apply_seq_empty hTrans
  case set_empty =>
    exact false_of_apply_set_empty hTrans
  all_goals
    exact false_of_apply_uop1_translate_apply_none hTrans rfl

theorem smt_model_eval_apply_uop2_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp2} {i j x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp2 op i j) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp2 op i j) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp2 op i j) x)) :=
by
  revert hTrans hNoFree
  cases op <;> intro hTrans hNoFree
  case extract =>
    have hXNoFree :
        __contains_atomic_term_list_free_rec x except bound =
          Term.Boolean false :=
      contains_atomic_term_list_free_rec_apply_uop2_false_arg
        hExcept hBound hNoFree
    rcases extract_indices_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨⟨_iVal, hINum⟩, hJValid, hXTrans⟩
    have hIEval := smt_model_eval_eq_of_eo_to_smt_numeral
      (M := M) (N := N) hINum
    have hJEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hJValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIEval, hJEval, hXEval]
  case re_loop =>
    have hXNoFree :
        __contains_atomic_term_list_free_rec x except bound =
          Term.Boolean false :=
      contains_atomic_term_list_free_rec_apply_uop2_false_arg
        hExcept hBound hNoFree
    rcases re_loop_indices_nat_valid_and_arg_has_smt_translation hTrans with
      ⟨hIValid, hJValid, hXTrans⟩
    have hIEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hIValid
    have hJEval := smt_model_eval_eq_of_eo_to_smt_nat_is_valid
      (M := M) (N := N) hJValid
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    dsimp only [__eo_to_smt]
    simp only [__smtx_model_eval]
    simp [hIEval, hJEval, hXEval]
  case _at_quantifiers_skolemize =>
    have hXNoFree :
        __contains_atomic_term_list_free_rec x except bound =
          Term.Boolean false :=
      contains_atomic_term_list_free_rec_apply_uop2_false_arg
        hExcept hBound hNoFree
    exact
      smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hExcept hBound
        (by intro q v vs hEq; cases hEq)
        (by rfl)
        (quant_skolemize_apply_generic_type i j x)
        hTrans hNoFree hAgree
        (by
          intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
          exact
            smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
              hExcept hBound' hHeadTrans
              (by intro f a h; cases h)
              hHeadNoFree hAgree')
        (by
          intro hXTrans hBound' hXNoFree M' N' hAgree'
          exact ih hXLt hExcept hBound' hXTrans hXNoFree hAgree')
  case _at_const =>
    have hXNoFree :
        __contains_atomic_term_list_free_rec x except bound =
          Term.Boolean false :=
      contains_atomic_term_list_free_rec_apply_uop2_false_arg
        hExcept hBound hNoFree
    exact
      smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hExcept hBound
        (by intro q v vs hEq; cases hEq)
        (by rfl)
        (at_const_apply_generic_type i j x)
        hTrans hNoFree hAgree
        (by
          intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
          exact
            smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
              hExcept hBound' hHeadTrans
              (by intro f a h; cases h)
              hHeadNoFree hAgree')
        (by
          intro hXTrans hBound' hXNoFree M' N' hAgree'
          exact ih hXLt hExcept hBound' hXTrans hXNoFree hAgree')

theorem smt_model_eval_apply_uop3_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp3} {a b c x except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp3 op a b c) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp3 op a b c) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp3 op a b c) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp3 op a b c) x)) :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact false_of_apply_re_unfold_pos_component hTrans
  case _at_witness_string_length =>
    exact
      smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hExcept hBound
        (by intro q v vs hEq; cases hEq)
        (by rfl)
        (witness_string_length_apply_generic_type a b c x)
        hTrans hNoFree hAgree
        (by
          intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
          exact
            smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
              hExcept hBound' hHeadTrans
              (by intro f y h; cases h)
              hHeadNoFree hAgree')
        (by
          intro hXTrans hBound' hXNoFree M' N' hAgree'
          exact ih hXLt hExcept hBound' hXTrans hXNoFree hAgree')

theorem smt_model_eval_apply_dt_sel_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {s : native_String} {d : DatatypeDecl} {i j : native_Nat}
    {x except bound : Term} {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.DtSel s d i j) x))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.DtSel s d i j) x) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
    __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) :=
by
  rcases
    contains_atomic_term_list_free_rec_apply_false_cases
      hExcept hBound
      (by intro q v vs hEq; cases hEq)
      hNoFree with
    ⟨_hHeadNoFree, hXNoFree⟩
  have hXTrans :
      eoHasSmtTranslation x :=
    apply_dt_sel_arg_has_smt_translation_of_has_smt_translation hTrans
  have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
  dsimp only [__eo_to_smt]
  cases hReserved : __eo_to_smt_reserved_datatype_name s
  · simp [native_ite, __smtx_model_eval, hXEval,
      smtx_model_eval_dt_sel_eq_of_globals hAgree.globals]
  · exfalso
    change
        __smtx_typeof
            (SmtTerm.Apply
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
              (__eo_to_smt x)) ≠
          SmtType.None at hTrans
    rw [hReserved] at hTrans
    exact hTrans (by
      simpa [native_ite] using
        TranslationProofs.typeof_apply_none_eq (__eo_to_smt x))

theorem smt_model_eval_apply_apply_uop1_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp1} {idx x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)) :=
by
  by_cases hUpdate : op = UserOp1.update
  · subst op
    rcases update_index_sel_and_args_have_smt_translation hTrans with
      ⟨_hIdxSel, hXTrans, hYTrans⟩
    rcases
      contains_atomic_term_list_free_rec_apply_apply_uop1_false_args
        hExcept hBound
        (term_not_eo_list_cons_of_has_smt_translation hXTrans)
        hNoFree with
      ⟨hXNoFree, hYNoFree⟩
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    have hYEval := ih hYLt hExcept hBound hYTrans hYNoFree hAgree
    change
      __smtx_model_eval M
          (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
            (__eo_to_smt y)) =
        __smtx_model_eval N
          (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
            (__eo_to_smt y))
    exact
      smtx_model_eval_eo_to_smt_updater_eq_of_eval_eq
        hAgree.globals (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y)
        hXEval hYEval
  by_cases hTupleUpdate : op = UserOp1.tuple_update
  · subst op
    rcases tuple_update_index_nat_valid_and_args_have_smt_translation hTrans with
      ⟨_hIdxValid, hXTrans, hYTrans⟩
    rcases
      contains_atomic_term_list_free_rec_apply_apply_uop1_false_args
        hExcept hBound
        (term_not_eo_list_cons_of_has_smt_translation hXTrans)
        hNoFree with
      ⟨hXNoFree, hYNoFree⟩
    have hXEval := ih hXLt hExcept hBound hXTrans hXNoFree hAgree
    have hYEval := ih hYLt hExcept hBound hYTrans hYNoFree hAgree
    change
      __smtx_model_eval M
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
            (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_model_eval N
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
            (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y))
    exact
      smtx_model_eval_eo_to_smt_tuple_update_eq_of_eval_eq
        hAgree.globals (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
        (__eo_to_smt x) (__eo_to_smt y) hXEval hYEval
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y) := by
    cases op <;> try rfl
    · exact False.elim (hUpdate rfl)
    · exact False.elim (hTupleUpdate rfl)
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
            (__eo_to_smt y)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)))
          (__smtx_typeof (__eo_to_smt y)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_sel
            _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_tester
            _ _ s d i hTester)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, hYTrans⟩
  have hXTrans :
      eoHasSmtTranslation x :=
    apply_uop1_arg_has_smt_translation_of_has_smt_translation hHeadTrans
  exact
    smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
      hExcept hBound
      (by
        intro q v vs hEq
        have hXEq :
            x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
          injection hEq
        exact
          term_not_eo_list_cons_of_has_smt_translation hXTrans v vs hXEq)
      hTranslate hTy hTrans hNoFree hAgree
      (by
        intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
        exact
          smt_model_eval_apply_uop1_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
            root hXLt hExcept hBound' hHeadTrans hHeadNoFree hAgree' ih)
      (by
        intro hYTrans hBound' hYNoFree M' N' hAgree'
        exact ih hYLt hExcept hBound' hYTrans hYNoFree hAgree')

theorem smt_model_eval_apply_apply_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
    (root : Term)
    {op : UserOp} {c x y except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hCLt : sizeOf c < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)
          except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N)
    (ih :
      ∀ {t except' bound' : Term}
        {exceptVars' boundVars' : List EoVarKey}
        {M' N' : SmtModel},
        sizeOf t < sizeOf root ->
          EoVarEnvPerm except' exceptVars' ->
          EoVarEnvPerm bound' boundVars' ->
          eoHasSmtTranslation t ->
          __contains_atomic_term_list_free_rec t except' bound' =
            Term.Boolean false ->
          model_agrees_except_on_env
            (exceptVars'.map EoVarKey.toSmt)
            (boundVars'.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt t) =
            __smtx_model_eval N' (__eo_to_smt t)) :
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) =
    __smtx_model_eval N
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) c) x) y)) :=
by
  cases op
  case ite =>
    exact
      smt_model_eval_apply_apply_apply_ite_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans hNoFree hAgree ih
  case store =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl) store_args_have_smt_translation_of_non_none h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case bvite =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        bvite_args_have_smt_translation_of_has_smt_translation
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_substr =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl) str_substr_args_have_smt_translation_of_non_none h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_replace =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl)
              (fun hNN =>
                seq_triop_args_have_smt_translation_of_non_none
                  (typeof_str_replace_eq (__eo_to_smt c) (__eo_to_smt x)
                    (__eo_to_smt y))
                  hNN)
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_indexof =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl) str_indexof_args_have_smt_translation_of_non_none h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_update =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl) str_update_args_have_smt_translation_of_non_none h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_replace_all =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl)
              (fun hNN =>
                seq_triop_args_have_smt_translation_of_non_none
                  (typeof_str_replace_all_eq (__eo_to_smt c)
                    (__eo_to_smt x) (__eo_to_smt y))
                  hNN)
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_replace_re =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl)
              (fun hNN =>
                str_replace_re_args_have_smt_translation_of_non_none
                  (typeof_str_replace_re_eq (__eo_to_smt c)
                    (__eo_to_smt x) (__eo_to_smt y))
                  hNN)
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_replace_re_all =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl)
              (fun hNN =>
                str_replace_re_args_have_smt_translation_of_non_none
                  (typeof_str_replace_re_all_eq (__eo_to_smt c)
                    (__eo_to_smt x) (__eo_to_smt y))
                  hNN)
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case str_indexof_re =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
              (by rfl) str_indexof_re_args_have_smt_translation_of_non_none h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case _at_strings_occur_index =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            strings_occur_index_args_have_smt_translation_of_has_smt_translation
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case _at_strings_occur_index_re =>
    exact
      smt_model_eval_apply_apply_apply_uop_ternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
        root hCLt hXLt hYLt hExcept hBound hTrans
        (by
          intro h
          exact
            strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
              h)
        hNoFree hAgree
        (by
          intro hc hx hy
          dsimp only [__eo_to_smt]
          simp [__smtx_model_eval, hc, hx, hy])
        ih
  case «forall» =>
    exact false_of_apply_apply_apply_forall_has_smt_translation hTrans
  case «exists» =>
    exact false_of_apply_apply_apply_exists_has_smt_translation hTrans
  all_goals
    exact
      smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
        hExcept hBound
        (by
          intro q v vs hEq
          cases hEq
          exact
            false_of_apply_apply_apply_uop_middle_raw_list_has_smt_translation
              hTrans)
        (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j hSel
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j hSel)
          (by
            intro s d i hTester
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i hTester))
        hTrans hNoFree hAgree
        (by
          intro hHeadTrans hBound' hHeadNoFree M' N' hAgree'
          exact
            smt_model_eval_apply_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
              root hCLt hXLt hExcept hBound' hHeadTrans hHeadNoFree
              hAgree' ih)
        (by
          intro hYTrans hBound' hYNoFree M' N' hAgree'
          exact ih hYLt hExcept hBound' hYTrans hYNoFree hAgree')

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
    (n : Nat) {t except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hLt : sizeOf t < n)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u except' bound' : Term}
            {exceptVars' boundVars' : List EoVarKey}
            {M' N' : SmtModel},
            sizeOf u < sizeOf t ->
              EoVarEnvPerm except' exceptVars' ->
              EoVarEnvPerm bound' boundVars' ->
              eoHasSmtTranslation u ->
              __contains_atomic_term_list_free_rec u except' bound' =
                Term.Boolean false ->
              model_agrees_except_on_env
                (exceptVars'.map EoVarKey.toSmt)
                (boundVars'.map EoVarKey.toSmt) M' N' ->
              __smtx_model_eval M' (__eo_to_smt u) =
                __smtx_model_eval N' (__eo_to_smt u) :=
        fun {u except' bound'} {exceptVars' boundVars'} {M' N'} hULt
            hExcept' hBound' hTrans' hNoFree' hAgree' =>
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
            n (t := u) (except := except') (bound := bound')
            (exceptVars := exceptVars') (boundVars := boundVars')
            (M := M') (N := N') (by omega)
            hExcept' hBound' hTrans' hNoFree' hAgree'
      cases t
      case Apply f x =>
        cases f
        case UOp op =>
          exact
            smt_model_eval_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
              (Term.Apply (Term.UOp op) x) (by
                simp <;> omega)
              hExcept hBound hTrans hNoFree hAgree hRec
        case UOp1 op idx =>
          exact
            smt_model_eval_apply_uop1_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
              (Term.Apply (Term.UOp1 op idx) x) (by
                simp <;> omega)
              hExcept hBound hTrans hNoFree hAgree hRec
        case UOp2 op i j =>
          exact
            smt_model_eval_apply_uop2_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
              (Term.Apply (Term.UOp2 op i j) x) (by
                simp <;> omega)
              hExcept hBound hTrans hNoFree hAgree hRec
        case UOp3 op a b c =>
          exact
            smt_model_eval_apply_uop3_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
              (Term.Apply (Term.UOp3 op a b c) x) (by
                simp <;> omega)
              hExcept hBound hTrans hNoFree hAgree hRec
        case DtSel s d i j =>
          exact
            smt_model_eval_apply_dt_sel_eq_of_contains_atomic_term_list_free_rec_false_mapped
              (Term.Apply (Term.DtSel s d i j) x) (by
                simp <;> omega)
              hExcept hBound hTrans hNoFree hAgree hRec
        case Apply g y =>
          cases g
          case UOp op =>
            exact
              smt_model_eval_apply_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
                (Term.Apply (Term.Apply (Term.UOp op) y) x)
                (by
                  simp <;> omega)
                (by
                  simp <;> omega)
                hExcept hBound hTrans hNoFree hAgree hRec
          case UOp1 op idx =>
            exact
              smt_model_eval_apply_apply_uop1_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
                (Term.Apply (Term.Apply (Term.UOp1 op idx) y) x)
                (by
                  simp <;> omega)
                (by
                  simp <;> omega)
                hExcept hBound hTrans hNoFree hAgree hRec
          case Apply h z =>
            cases h
            case UOp op =>
              exact
                smt_model_eval_apply_apply_apply_uop_any_eq_of_contains_atomic_term_list_free_rec_false_mapped
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.UOp op) z) y) x)
                  (by
                    simp <;> omega)
                  (by
                    simp <;> omega)
                  (by
                    simp <;> omega)
                  hExcept hBound hTrans hNoFree hAgree hRec
            case Apply f4 w =>
              cases f4
              case UOp op4 =>
                cases op4
                case _at_strings_replace_all_result =>
                  exact
                    smt_model_eval_apply_apply_apply_apply_uop_quaternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply
                              (Term.UOp UserOp._at_strings_replace_all_result)
                              w)
                            z)
                          y)
                        x)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      hExcept hBound hTrans
                      (by
                        intro h
                        exact
                          strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
                            h)
                      hNoFree hAgree
                      (by
                        intro hw hz hy hx
                        dsimp only [__eo_to_smt]
                        simp [__smtx_model_eval, hw, hz, hy, hx])
                      hRec
                case _at_strings_replace_re_all_result =>
                  exact
                    smt_model_eval_apply_apply_apply_apply_uop_quaternary_eq_of_contains_atomic_term_list_free_rec_false_mapped
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply
                              (Term.UOp UserOp._at_strings_replace_re_all_result)
                              w)
                            z)
                          y)
                        x)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      (by
                        simp <;> omega)
                      hExcept hBound hTrans
                      (by
                        intro h
                        exact
                          strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
                            h)
                      hNoFree hAgree
                      (by
                        intro hw hz hy hx
                        dsimp only [__eo_to_smt]
                        simp [__smtx_model_eval, hw, hz, hy, hx])
                      hRec
                all_goals
                      exact
                        smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
                          hExcept hBound
                          (by
                            intro q v vs hEq
                            cases hEq
                            rcases
                              is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                                hTrans with hForall | hExists
                            · cases hForall
                            · cases hExists)
                          (by rfl)
                          (generic_apply_type_of_non_special_head_closed _ _
                            (by
                              intro s d i j hSel
                              exact
                                TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                  _ _ s d i j hSel)
                            (by
                              intro s d i hTester
                              exact
                                TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                  _ _ s d i hTester))
                          hTrans hNoFree hAgree
                          (by
                            intro hFTrans hBound' hFNoFree M' N' hAgree'
                            exact hRec (by
                              simp <;> omega) hExcept hBound'
                              hFTrans hFNoFree hAgree')
                          (by
                            intro hXTrans hBound' hXNoFree M' N' hAgree'
                            exact hRec (by
                              simp <;> omega) hExcept hBound'
                              hXTrans hXNoFree hAgree')
              all_goals
                    exact
                      smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
                        hExcept hBound
                        (by
                          intro q v vs hEq
                          cases hEq
                          rcases
                            is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                              hTrans with hForall | hExists
                          · cases hForall
                          · cases hExists)
                        (by rfl)
                        (generic_apply_type_of_non_special_head_closed _ _
                          (by
                            intro s d i j hSel
                            exact
                              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                                _ _ s d i j hSel)
                          (by
                            intro s d i hTester
                            exact
                              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                                _ _ s d i hTester))
                        hTrans hNoFree hAgree
                        (by
                          intro hFTrans hBound' hFNoFree M' N' hAgree'
                          exact hRec (by
                            simp <;> omega) hExcept hBound'
                            hFTrans hFNoFree hAgree')
                        (by
                          intro hXTrans hBound' hXNoFree M' N' hAgree'
                          exact hRec (by
                            simp <;> omega) hExcept hBound'
                            hXTrans hXNoFree hAgree')
            all_goals
              exact
                smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
                  hExcept hBound
                  (by
                    intro q v vs hEq
                    cases hEq
                    rcases
                      is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                        hTrans with hForall | hExists
                    · cases hForall
                    · cases hExists)
                  (by rfl)
                  (generic_apply_type_of_non_special_head_closed _ _
                    (by
                      intro s d i j hSel
                      exact
                        TranslationProofs.eo_to_smt_apply_ne_dt_sel
                          _ _ s d i j hSel)
                    (by
                      intro s d i hTester
                      exact
                        TranslationProofs.eo_to_smt_apply_ne_dt_tester
                          _ _ s d i hTester))
                  hTrans hNoFree hAgree
                  (by
                    intro hFTrans hBound' hFNoFree M' N' hAgree'
                    exact hRec (by
                      simp <;> omega) hExcept hBound'
                      hFTrans hFNoFree hAgree')
                  (by
                    intro hXTrans hBound' hXNoFree M' N' hAgree'
                    exact hRec (by
                      simp <;> omega) hExcept hBound'
                      hXTrans hXNoFree hAgree')
          all_goals
            exact
              smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
                hExcept hBound
                (by
                  intro q v vs hEq
                  cases hEq
                  rcases
                    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                      hTrans with hForall | hExists
                  · cases hForall
                  · cases hExists)
                (by rfl)
                (generic_apply_type_of_non_special_head_closed _ _
                  (by
                    intro s d i j hSel
                    exact
                      TranslationProofs.eo_to_smt_apply_ne_dt_sel
                        _ _ s d i j hSel)
                  (by
                    intro s d i hTester
                    exact
                      TranslationProofs.eo_to_smt_apply_ne_dt_tester
                        _ _ s d i hTester))
                hTrans hNoFree hAgree
                (by
                  intro hFTrans hBound' hFNoFree M' N' hAgree'
                  exact hRec (by
                    simp <;> omega) hExcept hBound'
                    hFTrans hFNoFree hAgree')
                (by
                  intro hXTrans hBound' hXNoFree M' N' hAgree'
                  exact hRec (by
                    simp <;> omega) hExcept hBound'
                    hXTrans hXNoFree hAgree')
        all_goals
          exact
            smt_model_eval_apply_generic_eq_of_contains_atomic_term_list_free_rec_false_mapped
              hExcept hBound
              (by intro q v vs hEq; cases hEq)
              (by rfl)
              (generic_apply_type_of_non_special_head_closed _ _
                (by
                  intro s d i j hSel
                  rcases
                    TranslationProofs.eo_to_smt_eq_dt_sel_cases
                      _ s d i j hSel with hSelTerm | hPurify
                  · rcases hSelTerm with ⟨d0, hd, hTerm, hReserved⟩
                    cases hTerm
                  · rcases hPurify with ⟨z, hTerm, hz⟩
                    cases hTerm)
                (by
                  intro s d i hTester
                  exact
                    TranslationProofs.eo_to_smt_ne_dt_tester
                      _ s d i hTester))
              hTrans hNoFree hAgree
              (by
                intro hFTrans hBound' hFNoFree M' N' hAgree'
                exact hRec (by
                  simp <;> omega) hExcept hBound'
                  hFTrans hFNoFree hAgree')
              (by
                intro hXTrans hBound' hXNoFree M' N' hAgree'
                exact hRec (by
                  simp <;> omega) hExcept hBound'
                  hXTrans hXNoFree hAgree')
      all_goals
        exact
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_non_apply_false_mapped
            hExcept hBound hTrans
            (by intro f a hApply; cases hApply)
            hNoFree hAgree
termination_by n
decreasing_by
  all_goals omega

theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {t except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hTrans : eoHasSmtTranslation t)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) (boundVars.map EoVarKey.toSmt)
        M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  exact
    smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
      (sizeOf t + 1) (by omega)
      hExcept hBound hTrans hNoFree hAgree
