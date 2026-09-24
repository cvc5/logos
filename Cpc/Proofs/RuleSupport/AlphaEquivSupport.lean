module

public import Cpc.Proofs.RuleSupport.SkolemizeSupport
public import Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
import all Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Alpha-equivalence support

The alpha-equivalence checker uses the same simultaneous-substitution engine as
`instantiate`, with `isRename = true`.  All non-binder recursion is shared with
the substitution proof.  This file supplies the genuinely rename-specific
pieces: reflection of the source/target variable lists, paired model pushes at
quantifiers, and the top-level coincidence argument.
-/

namespace AlphaEquivRule

/-- Exact pointwise reflection of the two lists accepted by
`__is_renaming_rec`.  Each pair has one common EO type. -/
inductive RenamingLists : Term -> Term -> List (EoVarKey × EoVarKey) -> Prop
  | nil : RenamingLists Term.__eo_List_nil Term.__eo_List_nil []
  | cons {s t : native_String} {T xs ys : Term}
      {pairs : List (EoVarKey × EoVarKey)} :
      RenamingLists xs ys pairs ->
      RenamingLists
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) xs)
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String t) T)) ys)
        ((((s, T) : EoVarKey), ((t, T) : EoVarKey)) :: pairs)

def sourceKeys (pairs : List (EoVarKey × EoVarKey)) : List EoVarKey :=
  pairs.map Prod.fst

def targetKeys (pairs : List (EoVarKey × EoVarKey)) : List EoVarKey :=
  pairs.map Prod.snd

theorem RenamingLists.envs
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs) :
    EoVarEnv vs (sourceKeys pairs) ∧ EoVarEnv ts (targetKeys pairs) := by
  induction h with
  | nil => exact ⟨EoVarEnv.nil, EoVarEnv.nil⟩
  | cons _ ih =>
      exact ⟨EoVarEnv.cons ih.1, EoVarEnv.cons ih.2⟩

theorem RenamingLists.actuals
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs)
    (hTsTrans : EoListAllHaveSmtTranslation ts) :
    SubstActualsHaveSmtTypes vs ts := by
  induction h with
  | nil => exact SubstActualsHaveSmtTypes.nil Term.__eo_List_nil
  | @cons s t T xs ys pairs hTail ih =>
      rcases hTsTrans with ⟨hHeadTrans, hTailTrans⟩
      have hWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        smtx_type_wf_of_var_has_smt_translation hHeadTrans
      have hTy :
          __smtx_typeof (__eo_to_smt (Term.Var (Term.String t) T)) =
            __eo_to_smt_type T := by
        exact TranslationProofs.eo_to_smt_typeof_matches_translation
          (Term.Var (Term.String t) T) hHeadTrans
      exact SubstActualsHaveSmtTypes.cons hWf hHeadTrans hTy (ih hTailTrans)

theorem RenamingLists.distinct
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs)
    (hVsSet : __eo_list_setof Term.__eo_List_cons vs = vs)
    (hTsSet : __eo_list_setof Term.__eo_List_cons ts = ts) :
    SkolemizeRule.DistinctList (sourceKeys pairs) ∧
      SkolemizeRule.DistinctList (targetKeys pairs) := by
  exact ⟨SkolemizeRule.distinct_of_setof_guard h.envs.1 hVsSet,
    SkolemizeRule.distinct_of_setof_guard h.envs.2 hTsSet⟩

/-- An association lookup in reflected renaming lists returns the target
variable paired with the queried source variable. -/
theorem RenamingLists.assoc_eq_of_mem
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs)
    (hDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    {source target : EoVarKey}
    (hMem : (source, target) ∈ pairs) :
    __assoc_nil_nth Term.__eo_List_cons ts
        (__eo_list_find Term.__eo_List_cons vs
          (Term.Var (Term.String source.1) source.2)) =
      Term.Var (Term.String target.1) target.2 := by
  induction h generalizing source target with
  | nil => simp at hMem
  | @cons s t T xs ys pairs hTail ih =>
      have hDistinct' :
          SkolemizeRule.DistinctList (((s, T) : EoVarKey) :: sourceKeys pairs) := by
        simpa [sourceKeys] using hDistinct
      have hMem' :
          (source, target) =
              (((s, T) : EoVarKey), ((t, T) : EoVarKey)) ∨
            (source, target) ∈ pairs := by
        simpa using hMem
      cases hDistinct' with
      | cons hHeadNot hTailDistinct =>
          rcases hMem' with hHead | hTailMem
          · have hPairEq :
                (source, target) =
                  (((s, T) : EoVarKey), ((t, T) : EoVarKey)) := hHead
            injection hPairEq with hSource hTarget
            subst source
            subst target
            have hConsList :=
              (EoVarEnv.cons (s := s) (T := T) hTail.envs.1).is_list
            simp [__eo_list_find, __eo_requires, hConsList,
              __eo_list_find_rec, __assoc_nil_nth, __eo_ite, __eo_eq,
              native_ite, native_teq, native_not, SmtEval.native_not]
          · have hSourceMem : source ∈ sourceKeys pairs := by
              exact List.mem_map.2 ⟨(source, target), hTailMem, rfl⟩
            have hSourceNe : ((s, T) : EoVarKey) ≠ source := by
              intro hEq
              exact hHeadNot (hEq ▸ hSourceMem)
            have hVarNe :
                Term.Var (Term.String s) T ≠
                  Term.Var (Term.String source.1) source.2 := by
              intro hEq
              apply hSourceNe
              cases source with
              | mk sourceName sourceTy =>
                  simp only at hEq ⊢
                  injection hEq with hName hTy
                  injection hName with hName
                  exact Prod.ext hName hTy
            rw [assoc_nil_nth_cons_find_tail_eq
              hTail.envs.1 s T (Term.Var (Term.String t) T)
              hVarNe hSourceMem]
            exact ih hTailDistinct hTailMem

theorem RenamingLists.target_of_find
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs)
    (hDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons vs
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
    ∃ target : EoVarKey,
      (((s, T) : EoVarKey), target) ∈ pairs ∧
        __assoc_nil_nth Term.__eo_List_cons ts
            (__eo_list_find Term.__eo_List_cons vs
              (Term.Var (Term.String s) T)) =
          Term.Var (Term.String target.1) target.2 := by
  have hSourceMem : ((s, T) : EoVarKey) ∈ sourceKeys pairs :=
    EoVarEnvPerm.mem_of_find_neg_false
      (EoVarEnvPerm.of_exact h.envs.1) hFind
  rcases List.mem_map.1 hSourceMem with ⟨pair, hPairMem, hPairSource⟩
  rcases pair with ⟨source, target⟩
  change source = (s, T) at hPairSource
  subst source
  exact ⟨target, hPairMem, h.assoc_eq_of_mem hDistinct hPairMem⟩

theorem RenamingLists.types_eq_of_mem
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists vs ts pairs)
    {source target : EoVarKey}
    (hMem : (source, target) ∈ pairs) :
    source.2 = target.2 := by
  induction h with
  | nil => simp at hMem
  | @cons s t T xs ys pairs hTail ih =>
      have hMem' :
          (source, target) =
              (((s, T) : EoVarKey), ((t, T) : EoVarKey)) ∨
            (source, target) ∈ pairs := by
        simpa using hMem
      rcases hMem' with hHead | hTail
      · injection hHead with hSource hTarget
        subst source
        subst target
        rfl
      · exact ih hTail

theorem RenamingLists.target_cons_of_source_cons
    {sourceHead sourceTail target : Term}
    {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists
      (Term.Apply (Term.Apply Term.__eo_List_cons sourceHead) sourceTail)
      target pairs) :
    ∃ targetHead targetTail,
      target = Term.Apply (Term.Apply Term.__eo_List_cons
        targetHead) targetTail := by
  cases h with
  | cons hTail => exact ⟨_, _, rfl⟩

theorem RenamingLists.target_types_wf
    {source target : Term} {pairs : List (EoVarKey × EoVarKey)}
    (h : RenamingLists source target pairs)
    (hSourceWf :
      ∀ key, key ∈ sourceKeys pairs →
        __smtx_type_wf (__eo_to_smt_type key.2) = true) :
    ∀ key, key ∈ targetKeys pairs →
      __smtx_type_wf (__eo_to_smt_type key.2) = true := by
  induction h with
  | nil =>
      intro key hMem
      simp [targetKeys] at hMem
  | @cons s t T xs ys pairs hTail ih =>
      intro key hMem
      have hMem' : key = ((t, T) : EoVarKey) ∨
          key ∈ targetKeys pairs := by
        simpa [targetKeys] using hMem
      rcases hMem' with rfl | hTailMem
      · exact hSourceWf (s, T) (by simp [sourceKeys])
      · apply ih
        · intro sourceKey hSourceMem
          exact hSourceWf sourceKey (by
            simp only [sourceKeys, List.map_cons, List.mem_cons]
            exact Or.inr hSourceMem)
        · exact hTailMem

private theorem map_injective_on_of_distinct
    {A B : Type} (f : A → B) {l : List A}
    (hDistinct : SkolemizeRule.DistinctList (l.map f))
    {a b : A} (ha : a ∈ l) (hb : b ∈ l) (hEq : f a = f b) :
    a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      have hDistinct' :
          SkolemizeRule.DistinctList (f x :: xs.map f) := by
        simpa using hDistinct
      cases hDistinct' with
      | cons hHeadNot hTailDistinct =>
          have ha' : a = x ∨ a ∈ xs := by simpa using ha
          have hb' : b = x ∨ b ∈ xs := by simpa using hb
          rcases ha' with haHead | haTail
          · rcases hb' with hbHead | hbTail
            · exact haHead.trans hbHead.symm
            · exfalso
              have hFxFb : f x = f b := by simpa [haHead] using hEq
              exact hHeadNot (hFxFb ▸ List.mem_map.2 ⟨b, hbTail, rfl⟩)
          · rcases hb' with hbHead | hbTail
            · exfalso
              have hFaFx : f a = f x := by simpa [hbHead] using hEq
              exact hHeadNot (hFaFx ▸ List.mem_map.2 ⟨a, haTail, rfl⟩)
            · exact ih hTailDistinct haTail hbTail

private theorem eoVarKey_eq_of_toSmt_eq_of_type_wf
    (p q : EoVarKey)
    (hWf : __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hEq : EoVarKey.toSmt p = EoVarKey.toSmt q) :
    p = q := by
  rcases p with ⟨s, T⟩
  rcases q with ⟨s', T'⟩
  simp [EoVarKey.toSmt] at hEq
  rcases hEq with ⟨hName, hType⟩
  subst s'
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    have hT' : T' = Term.UOp UserOp.RegLan :=
      TranslationProofs.eo_to_smt_type_eq_reglan hType.symm
    subst T'
    rfl
  · have hValid : TranslationProofs.eo_type_valid T :=
      TranslationProofs.eo_type_valid_of_smt_wf T hWf
    have hValidRec : TranslationProofs.eo_type_valid_rec [] T := by
      cases T with
      | UOp op =>
          cases op
          case RegLan => exact False.elim (hReg rfl)
          all_goals exact hValid
      | _ => simpa [TranslationProofs.eo_type_valid,
            TranslationProofs.eo_type_valid_rec] using hValid
    have hTT' : T = T' :=
      TranslationProofs.eo_to_smt_type_eq_of_valid
        (T := T) (U := T') hValidRec hType
    subst T'
    rfl

private theorem var_lookup_push_self
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    native_model_var_lookup (native_model_push M s T v) s T = v := by
  simp [native_model_var_lookup, native_model_push]

private theorem var_lookup_push_ne
    {s' : native_String} {T' : SmtType}
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hNe : ((s', T') : SmtVarKey) ≠ (s, T)) :
    native_model_var_lookup (native_model_push M s T v) s' T' =
      native_model_var_lookup M s' T' := by
  have hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
        { isVar := true, name := s, ty := T } := by
    intro h
    injection h with _ hName hTy
    exact hNe (by rw [hName, hTy])
  simp [native_model_var_lookup, native_model_push, hKey]

private theorem model_agrees_on_globals_push_diff
    {M N : SmtModel} {s t : native_String} {T : SmtType} {v : SmtValue}
    (h : model_agrees_on_globals M N) :
    model_agrees_on_globals
      (native_model_push M t T v) (native_model_push N s T v) := by
  refine ⟨?_, ?_⟩
  · intro name ty
    simpa [native_model_lookup, model_key, native_model_push]
      using h.1 name ty
  · intro fid A B
    simpa [model_fun_lookup, model_key, native_model_push]
      using h.2 fid A B

/-- Model relation used by uniform renaming.  `N` interprets each source key as
the value of its associated target term in `M`; outside both lists the models
agree. -/
structure AlphaRel (M N : SmtModel) (vs ts : Term) : Prop where
  globals : model_agrees_on_globals M N
  agree :
    ∀ (s : native_String) (T : Term),
      __smtx_type_wf (__eo_to_smt_type T) = true →
      __eo_is_neg (__eo_list_find Term.__eo_List_cons vs
        (Term.Var (Term.String s) T)) = Term.Boolean true →
      __eo_is_neg (__eo_list_find Term.__eo_List_cons ts
        (Term.Var (Term.String s) T)) = Term.Boolean true →
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)
  mapped :
    ∀ (s : native_String) (T : Term),
      __smtx_type_wf (__eo_to_smt_type T) = true →
      __eo_is_neg (__eo_list_find Term.__eo_List_cons vs
        (Term.Var (Term.String s) T)) = Term.Boolean false →
      native_model_var_lookup N s (__eo_to_smt_type T) =
        __smtx_model_eval M
          (__eo_to_smt
            (__assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons vs
                (Term.Var (Term.String s) T))))

theorem alphaRel_of_substFalseRel
    {M N : SmtModel} {vs ts : Term}
    (h : SubstituteSupport.SubstFalseRel
      M N vs ts Term.__eo_List_nil) :
    AlphaRel M N vs ts := by
  refine ⟨h.globals, ?_, ?_⟩
  · intro s T _hWf hSource _hTarget
    exact h.agree s T (Or.inr hSource)
  · intro s T _hWf hMapped
    have hFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
              (Term.Var (Term.String s) T)) =
          Term.Boolean true :=
      EoVarEnv.nil.find_neg_true_of_not_mem (by simp)
    exact h.mapped s T hFree hMapped

/-- Pushing the same canonical witness under a paired target/source binder
preserves the renaming relation.  Source and target distinctness ensure the two
pushes do not change any other association. -/
theorem alphaRel_push_mapped
    {M N : SmtModel} {vs ts : Term}
    {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTargetDistinct : SkolemizeRule.DistinctList (targetKeys pairs))
    (hRel : AlphaRel M N vs ts)
    (s t : native_String) (T : Term) (v : SmtValue)
    (hPair :
      ((((s, T) : EoVarKey), ((t, T) : EoVarKey)) : EoVarKey × EoVarKey) ∈
        pairs) :
    AlphaRel
      (native_model_push M t (__eo_to_smt_type T) v)
      (native_model_push N s (__eo_to_smt_type T) v)
      vs ts := by
  have hSourceMem : ((s, T) : EoVarKey) ∈ sourceKeys pairs :=
    List.mem_map.2 ⟨_, hPair, rfl⟩
  have hTargetMem : ((t, T) : EoVarKey) ∈ targetKeys pairs :=
    List.mem_map.2 ⟨_, hPair, rfl⟩
  have hSourceFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons vs
            (Term.Var (Term.String s) T)) =
        Term.Boolean false :=
    hLists.envs.1.find_neg_false_of_mem hSourceMem
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons ts
          (__eo_list_find Term.__eo_List_cons vs
            (Term.Var (Term.String s) T)) =
        Term.Var (Term.String t) T :=
    hLists.assoc_eq_of_mem hSourceDistinct hPair
  refine ⟨model_agrees_on_globals_push_diff hRel.globals, ?_, ?_⟩
  · intro s' T' hWf hSourceFree hTargetFree
    have hSourceNe :
        ((s', __eo_to_smt_type T') : SmtVarKey) ≠
          (s, __eo_to_smt_type T) := by
      intro hEq
      have hEoEq : ((s', T') : EoVarKey) = (s, T) :=
        eoVarKey_eq_of_toSmt_eq_of_type_wf (s', T') (s, T) hWf hEq
      rcases hEoEq with ⟨rfl, rfl⟩
      rw [hSourceFind] at hSourceFree
      cases hSourceFree
    have hTargetNe :
        ((s', __eo_to_smt_type T') : SmtVarKey) ≠
          (t, __eo_to_smt_type T) := by
      intro hEq
      have hEoEq : ((s', T') : EoVarKey) = (t, T) :=
        eoVarKey_eq_of_toSmt_eq_of_type_wf (s', T') (t, T) hWf hEq
      rcases hEoEq with ⟨rfl, rfl⟩
      have hTargetFind :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons ts
                (Term.Var (Term.String t) T)) =
            Term.Boolean false :=
        hLists.envs.2.find_neg_false_of_mem hTargetMem
      rw [hTargetFind] at hTargetFree
      cases hTargetFree
    rw [var_lookup_push_ne M t (__eo_to_smt_type T) v hTargetNe,
      var_lookup_push_ne N s (__eo_to_smt_type T) v hSourceNe]
    exact hRel.agree s' T' hWf hSourceFree hTargetFree
  · intro s' T' hWf hMapped
    by_cases hSourceEq : ((s', T') : EoVarKey) = (s, T)
    · rcases hSourceEq with ⟨rfl, rfl⟩
      rw [var_lookup_push_self, hAssoc, SubstituteSupport.eval_eo_var,
        var_lookup_push_self]
    · have hSourceNe :
          ((s', __eo_to_smt_type T') : SmtVarKey) ≠
            (s, __eo_to_smt_type T) := by
        intro hEq
        exact hSourceEq
          (eoVarKey_eq_of_toSmt_eq_of_type_wf (s', T') (s, T) hWf hEq)
      rw [var_lookup_push_ne N s (__eo_to_smt_type T) v hSourceNe,
        hRel.mapped s' T' hWf hMapped]
      rcases hLists.target_of_find hSourceDistinct hMapped with
        ⟨target, hTargetPair, hTargetAssoc⟩
      have hTargetType : T' = target.2 :=
        hLists.types_eq_of_mem hTargetPair
      have hTargetWf :
          __smtx_type_wf (__eo_to_smt_type target.2) = true := by
        simpa [← hTargetType] using hWf
      have hTargetEoNe : target ≠ ((t, T) : EoVarKey) := by
        intro hEq
        have hPairsEq :
            (((s', T') : EoVarKey), target) =
              (((s, T) : EoVarKey), ((t, T) : EoVarKey)) :=
          map_injective_on_of_distinct Prod.snd hTargetDistinct
            hTargetPair hPair (by simpa using hEq)
        injection hPairsEq with hSources _
        exact hSourceEq hSources
      have hTargetNe :
          ((target.1, __eo_to_smt_type target.2) : SmtVarKey) ≠
            (t, __eo_to_smt_type T) := by
        intro hEq
        exact hTargetEoNe
          (eoVarKey_eq_of_toSmt_eq_of_type_wf
            target (t, T) hTargetWf hEq)
      rw [hTargetAssoc,
        SubstituteSupport.eval_eo_var M target.1 target.2,
        SubstituteSupport.eval_eo_var
          (native_model_push M t (__eo_to_smt_type T) v)
          target.1 target.2,
        var_lookup_push_ne M t (__eo_to_smt_type T) v hTargetNe]

/-- An unmapped binder is retained.  If it is absent from the target list as
well (the quantifier capture guard), pushing it on both sides preserves
`AlphaRel`. -/
theorem alphaRel_push_unmapped
    {M N : SmtModel} {vs ts : Term}
    {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hRel : AlphaRel M N vs ts)
    (s : native_String) (T : Term) (v : SmtValue)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hSourceFree :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons vs
            (Term.Var (Term.String s) T)) =
        Term.Boolean true)
    (hTargetFree :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons ts
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
    AlphaRel
      (native_model_push M s (__eo_to_smt_type T) v)
      (native_model_push N s (__eo_to_smt_type T) v)
      vs ts := by
  refine ⟨model_agrees_on_globals_push₂ hRel.globals, ?_, ?_⟩
  · intro s' T' hWf' hSourceFree' hTargetFree'
    by_cases hEoEq : ((s', T') : EoVarKey) = (s, T)
    · rcases hEoEq with ⟨rfl, rfl⟩
      rw [var_lookup_push_self, var_lookup_push_self]
    · have hSmtNe :
          ((s', __eo_to_smt_type T') : SmtVarKey) ≠
            (s, __eo_to_smt_type T) := by
        intro hEq
        exact hEoEq
          (eoVarKey_eq_of_toSmt_eq_of_type_wf (s', T') (s, T) hWf' hEq)
      rw [var_lookup_push_ne M s (__eo_to_smt_type T) v hSmtNe,
        var_lookup_push_ne N s (__eo_to_smt_type T) v hSmtNe]
      exact hRel.agree s' T' hWf' hSourceFree' hTargetFree'
  · intro s' T' hWf' hMapped
    have hSourceNe :
        ((s', __eo_to_smt_type T') : SmtVarKey) ≠
          (s, __eo_to_smt_type T) := by
      intro hEq
      have hEoEq : ((s', T') : EoVarKey) = (s, T) :=
        eoVarKey_eq_of_toSmt_eq_of_type_wf (s', T') (s, T) hWf' hEq
      rcases hEoEq with ⟨rfl, rfl⟩
      rw [hSourceFree] at hMapped
      cases hMapped
    rw [var_lookup_push_ne N s (__eo_to_smt_type T) v hSourceNe,
      hRel.mapped s' T' hWf' hMapped]
    rcases hLists.target_of_find hSourceDistinct hMapped with
      ⟨target, hTargetPair, hTargetAssoc⟩
    have hTargetType : T' = target.2 :=
      hLists.types_eq_of_mem hTargetPair
    have hTargetWf :
        __smtx_type_wf (__eo_to_smt_type target.2) = true := by
      simpa [← hTargetType] using hWf'
    have hTargetNe :
        ((target.1, __eo_to_smt_type target.2) : SmtVarKey) ≠
          (s, __eo_to_smt_type T) := by
      intro hEq
      have hEoEq : target = (s, T) :=
        eoVarKey_eq_of_toSmt_eq_of_type_wf target (s, T) hTargetWf hEq
      rcases hEoEq with ⟨rfl, rfl⟩
      have hTargetMem : ((s, T) : EoVarKey) ∈ targetKeys pairs :=
        List.mem_map.2 ⟨_, hTargetPair, rfl⟩
      have hTargetFindFalse :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons ts
                (Term.Var (Term.String s) T)) =
            Term.Boolean false :=
        hLists.envs.2.find_neg_false_of_mem hTargetMem
      rw [hTargetFindFalse] at hTargetFree
      cases hTargetFree
    rw [hTargetAssoc,
      SubstituteSupport.eval_eo_var M target.1 target.2,
      SubstituteSupport.eval_eo_var
        (native_model_push M s (__eo_to_smt_type T) v)
        target.1 target.2,
      var_lookup_push_ne M s (__eo_to_smt_type T) v hTargetNe]

private theorem contains_target_env_cons_false
    {s : native_String} {T tail except : Term}
    {tailVars exceptVars : List EoVarKey}
    (hTailEnv : EoVarEnv tail tailVars)
    (hExceptEnv : EoVarEnv except exceptVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) tail)
          except Term.__eo_List_nil = Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons except
          (Term.Var (Term.String s) T)) = Term.Boolean true ∧
      __contains_atomic_term_list_free_rec tail except Term.__eo_List_nil =
        Term.Boolean false := by
  have hExceptPerm := EoVarEnvPerm.of_exact hExceptEnv
  have hNilPerm := EoVarEnvPerm.of_exact EoVarEnv.nil
  have hOuter :=
    contains_atomic_term_list_free_rec_apply_false_cases
      hExceptPerm hNilPerm
      (f := Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      (a := tail)
      (by
        intro q x ys hEq
        injection hEq with _ hArg
        cases hArg)
      hNoFree
  have hInner :=
    contains_atomic_term_list_free_rec_apply_false_cases
      hExceptPerm hNilPerm
      (f := Term.__eo_List_cons)
      (a := Term.Var (Term.String s) T)
      (by intro q x ys hEq; cases hEq)
      hOuter.1
  rcases contains_atomic_term_list_free_rec_var_false_cases hInner.2 with
    hTargetFree | hBound
  · exact ⟨hTargetFree, hOuter.2⟩
  · have hNilFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
              (Term.Var (Term.String s) T)) =
          Term.Boolean true :=
      EoVarEnv.nil.find_neg_true_of_not_mem (by simp)
    rw [hNilFree] at hBound
    cases hBound

theorem contains_var_env_false_disjoint
    {terms except : Term} {termVars exceptVars : List EoVarKey}
    (hTerms : EoVarEnv terms termVars)
    (hExcept : EoVarEnv except exceptVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec terms except Term.__eo_List_nil =
        Term.Boolean false) :
    ∀ key, key ∈ termVars → key ∉ exceptVars := by
  induction hTerms with
  | nil => intro key hMem; cases hMem
  | @cons s T tail vars hTail ih =>
      rcases contains_target_env_cons_false hTail hExcept hNoFree with
        ⟨hHeadFree, hTailFree⟩
      have hHeadNot : ((s, T) : EoVarKey) ∉ exceptVars :=
        EoVarEnvPerm.not_mem_of_find_neg_true
          (EoVarEnvPerm.of_exact hExcept) hHeadFree
      intro key hMem
      have hMem' : key = (s, T) ∨ key ∈ vars := by simpa using hMem
      rcases hMem' with hHead | hTailMem
      · simpa [hHead] using hHeadNot
      · exact ih hTailFree key hTailMem

private theorem eo_mk_apply_eq
    {f a : Term} (hf : f ≠ Term.Stuck) (ha : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hf ha ⊢

/-- Pointwise relation between an original binder environment and the binder
environment obtained by true-mode substitution. -/
inductive BinderRenaming
    (vs ts : Term) (pairs : List (EoVarKey × EoVarKey)) :
    Term → Term → List (EoVarKey × EoVarKey) → Prop
  | nil : BinderRenaming vs ts pairs Term.__eo_List_nil Term.__eo_List_nil []
  | mapped {s t : native_String} {T sourceTail targetTail : Term}
      {binderPairs : List (EoVarKey × EoVarKey)} :
      ((((s, T) : EoVarKey), ((t, T) : EoVarKey)) : EoVarKey × EoVarKey) ∈
          pairs →
      BinderRenaming vs ts pairs sourceTail targetTail binderPairs →
      BinderRenaming vs ts pairs
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) sourceTail)
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String t) T)) targetTail)
        (((((s, T) : EoVarKey), ((t, T) : EoVarKey))) :: binderPairs)
  | unmapped {s : native_String} {T sourceTail targetTail : Term}
      {binderPairs : List (EoVarKey × EoVarKey)} :
      ((s, T) : EoVarKey) ∉ sourceKeys pairs →
      ((s, T) : EoVarKey) ∉ targetKeys pairs →
      BinderRenaming vs ts pairs sourceTail targetTail binderPairs →
      BinderRenaming vs ts pairs
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) sourceTail)
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) targetTail)
        (((((s, T) : EoVarKey), ((s, T) : EoVarKey))) :: binderPairs)

theorem BinderRenaming.envs
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    {source target : Term} {binderPairs : List (EoVarKey × EoVarKey)}
    (h : BinderRenaming vs ts pairs source target binderPairs) :
    EoVarEnv source (binderPairs.map Prod.fst) ∧
      EoVarEnv target (binderPairs.map Prod.snd) := by
  induction h with
  | nil => exact ⟨EoVarEnv.nil, EoVarEnv.nil⟩
  | mapped _ _ ih => exact ⟨EoVarEnv.cons ih.1, EoVarEnv.cons ih.2⟩
  | unmapped _ _ _ ih => exact ⟨EoVarEnv.cons ih.1, EoVarEnv.cons ih.2⟩

theorem BinderRenaming.target_cons_of_source_cons
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    {sourceHead sourceTail target : Term}
    {binderPairs : List (EoVarKey × EoVarKey)}
    (h : BinderRenaming vs ts pairs
      (Term.Apply (Term.Apply Term.__eo_List_cons
        sourceHead) sourceTail)
      target binderPairs) :
    ∃ targetHead targetTail,
      target = Term.Apply (Term.Apply Term.__eo_List_cons
        targetHead) targetTail := by
  cases h with
  | mapped hPair hTail => exact ⟨_, _, rfl⟩
  | unmapped hSourceNot hTargetNot hTail => exact ⟨_, _, rfl⟩

/-- Substituting a variable environment in rename mode computes the pointwise
`BinderRenaming` environment. -/
theorem binderRenaming_of_substitute
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTsTrans : EoListAllHaveSmtTranslation ts)
    {source : Term} {sourceVars : List EoVarKey}
    (hSourceEnv : EoVarEnv source sourceVars)
    (hDisjoint :
      ∀ key, key ∈ sourceVars → key ∉ targetKeys pairs) :
    ∃ target binderPairs,
      BinderRenaming vs ts pairs source target binderPairs ∧
        __substitute_simul_rec (Term.Boolean true) source vs ts
            Term.__eo_List_nil = target := by
  have hvs : vs ≠ Term.Stuck := hLists.envs.1.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    eoListAllHaveSmtTranslation_ne_stuck hTsTrans
  have hnil : Term.__eo_List_nil ≠ Term.Stuck := by decide
  have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
  induction hSourceEnv with
  | nil =>
      refine ⟨Term.__eo_List_nil, [], BinderRenaming.nil, ?_⟩
      simp [__substitute_simul_rec, __is_closed_rec, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
  | @cons s T sourceTail sourceVars hTailEnv ih =>
      have hHeadTargetNot : ((s, T) : EoVarKey) ∉ targetKeys pairs :=
        hDisjoint (s, T) (List.Mem.head _)
      have hTailDisjoint :
          ∀ key, key ∈ sourceVars → key ∉ targetKeys pairs := by
        intro key hMem
        exact hDisjoint key (List.Mem.tail _ hMem)
      rcases ih hTailDisjoint with
        ⟨targetTail, binderPairs, hTailRename, hTailSub⟩
      have hTargetTailNe : targetTail ≠ Term.Stuck :=
        hTailRename.envs.2.ne_stuck
      have hConsSub :
          __substitute_simul_rec (Term.Boolean true) Term.__eo_List_cons
              vs ts Term.__eo_List_nil = Term.__eo_List_cons := by
        rw [SubstituteSupport.substitute_simul_rec_atom
          (Term.Boolean true) Term.__eo_List_cons vs ts Term.__eo_List_nil
          hisr hvs hts hnil
          (by intro f a h; cases h)
          (by intro name ty h; cases h)
          (by intro h; cases h)]
        simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
          native_not, SmtEval.native_not]
      by_cases hSourceMem : ((s, T) : EoVarKey) ∈ sourceKeys pairs
      · have hSourceFind :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons vs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false :=
          hLists.envs.1.find_neg_false_of_mem hSourceMem
        rcases hLists.target_of_find hSourceDistinct hSourceFind with
          ⟨targetKey, hPair, hAssoc⟩
        have hTypeEq : T = targetKey.2 :=
          hLists.types_eq_of_mem hPair
        rcases targetKey with ⟨t, targetT⟩
        simp only at hTypeEq
        subst targetT
        have hHeadSub :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Var (Term.String s) T) vs ts Term.__eo_List_nil =
              Term.Var (Term.String t) T := by
          rw [SubstituteSupport.substitute_simul_rec_var_mapped
            (Term.Boolean true) (Term.String s) T vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (EoVarEnv.nil.find_neg_true_of_not_mem (by simp))
            hSourceFind,
            hAssoc]
        let target :=
          Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String t) T)) targetTail
        have hInner :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                vs ts Term.__eo_List_nil =
              Term.Apply Term.__eo_List_cons (Term.Var (Term.String t) T) := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true) Term.__eo_List_cons
            (Term.Var (Term.String s) T) vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (by intro q v tail hEq; cases hEq), hConsSub, hHeadSub]
          rfl
        have hWhole :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                  sourceTail)
                vs ts Term.__eo_List_nil = target := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true)
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            sourceTail vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (by
              intro q v tail hEq
              injection hEq with _ hArg
              cases hArg), hInner, hTailSub]
          exact eo_mk_apply_eq (by intro h; cases h) hTargetTailNe
        exact ⟨target, _, BinderRenaming.mapped hPair hTailRename, hWhole⟩
      · have hSourceFind :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons vs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true :=
          hLists.envs.1.find_neg_true_of_not_mem hSourceMem
        have hTargetNotMem : ((s, T) : EoVarKey) ∉ targetKeys pairs :=
          hHeadTargetNot
        have hHeadSub :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Var (Term.String s) T) vs ts Term.__eo_List_nil =
              Term.Var (Term.String s) T :=
          SubstituteSupport.substitute_simul_rec_var_unmapped
            (Term.Boolean true) (Term.String s) T vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (EoVarEnv.nil.find_neg_true_of_not_mem (by simp)) hSourceFind
        let target :=
          Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) targetTail
        have hInner :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                vs ts Term.__eo_List_nil =
              Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T) := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true) Term.__eo_List_cons
            (Term.Var (Term.String s) T) vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (by intro q v tail hEq; cases hEq), hConsSub, hHeadSub]
          rfl
        have hWhole :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                  sourceTail)
                vs ts Term.__eo_List_nil = target := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true)
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            sourceTail vs ts Term.__eo_List_nil
            hisr hvs hts hnil
            (by
              intro q v tail hEq
              injection hEq with _ hArg
              cases hArg), hInner, hTailSub]
          exact eo_mk_apply_eq (by intro h; cases h) hTargetTailNe
        exact ⟨target, _,
          BinderRenaming.unmapped hSourceMem hTargetNotMem hTailRename, hWhole⟩

/-- True-mode substitution maps a variable environment to another variable
environment with the same pointwise EO types.  Unlike `BinderRenaming`, this
typing relation also permits variables protected by a nonempty local-bound
environment; those variables are retained. -/
theorem renamingLists_of_substitute_var_env
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTsTrans : EoListAllHaveSmtTranslation ts)
    {source bvs : Term} {sourceVars bvsVars : List EoVarKey}
    (hSourceEnv : EoVarEnv source sourceVars)
    (hBvsEnv : EoVarEnv bvs bvsVars) :
    ∃ target binderPairs,
      RenamingLists source target binderPairs ∧
        __substitute_simul_rec (Term.Boolean true) source vs ts bvs = target := by
  have hvs : vs ≠ Term.Stuck := hLists.envs.1.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    eoListAllHaveSmtTranslation_ne_stuck hTsTrans
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
  induction hSourceEnv with
  | nil =>
      refine ⟨Term.__eo_List_nil, [], RenamingLists.nil, ?_⟩
      rw [SubstituteSupport.substitute_simul_rec_atom
        (Term.Boolean true) Term.__eo_List_nil vs ts bvs
        hisr hvs hts hbvs
        (by intro f a h; cases h)
        (by intro name ty h; cases h)
        (by intro h; cases h)]
      simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | @cons s T sourceTail sourceVars hTailEnv ih =>
      rcases ih with ⟨targetTail, binderPairs, hTailRename, hTailSub⟩
      have hTargetTailNe : targetTail ≠ Term.Stuck :=
        hTailRename.envs.2.ne_stuck
      have hConsSub :
          __substitute_simul_rec (Term.Boolean true) Term.__eo_List_cons
              vs ts bvs = Term.__eo_List_cons := by
        rw [SubstituteSupport.substitute_simul_rec_atom
          (Term.Boolean true) Term.__eo_List_cons vs ts bvs
          hisr hvs hts hbvs
          (by intro f a h; cases h)
          (by intro name ty h; cases h)
          (by intro h; cases h)]
        simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
          native_not, SmtEval.native_not]
      have hAssemble (t : native_String)
          (hHeadSub :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Var (Term.String s) T) vs ts bvs =
              Term.Var (Term.String t) T) :
          ∃ target,
            RenamingLists
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) sourceTail)
              target
              (((((s, T) : EoVarKey), ((t, T) : EoVarKey))) :: binderPairs) ∧
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) sourceTail)
                vs ts bvs = target := by
        let target :=
          Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String t) T)) targetTail
        have hInner :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T))
                vs ts bvs =
              Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String t) T) := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true) Term.__eo_List_cons
            (Term.Var (Term.String s) T) vs ts bvs
            hisr hvs hts hbvs
            (by intro q v tail hEq; cases hEq), hConsSub, hHeadSub]
          rfl
        have hWhole :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) sourceTail)
                vs ts bvs = target := by
          rw [SubstituteSupport.substitute_simul_rec_apply
            (Term.Boolean true)
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            sourceTail vs ts bvs hisr hvs hts hbvs
            (by
              intro q v tail hEq
              injection hEq with _ hArg
              cases hArg), hInner, hTailSub]
          exact eo_mk_apply_eq (by intro h; cases h) hTargetTailNe
        exact ⟨target, RenamingLists.cons hTailRename, hWhole⟩
      by_cases hBoundMem : ((s, T) : EoVarKey) ∈ bvsVars
      · have hBoundFind :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean false :=
          hBvsEnv.find_neg_false_of_mem hBoundMem
        have hHeadSub :
            __substitute_simul_rec (Term.Boolean true)
                (Term.Var (Term.String s) T) vs ts bvs =
              Term.Var (Term.String s) T :=
          SubstituteSupport.substitute_simul_rec_var_bound
            (Term.Boolean true) (Term.String s) T vs ts bvs
            hisr hvs hts hbvs hBoundFind
        rcases hAssemble s hHeadSub with ⟨target, hRename, hSub⟩
        exact ⟨target, _, hRename, hSub⟩
      · have hFreeFind :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons bvs
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true :=
          hBvsEnv.find_neg_true_of_not_mem hBoundMem
        by_cases hSourceMem : ((s, T) : EoVarKey) ∈ sourceKeys pairs
        · have hSourceFind :
              __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons vs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean false :=
            hLists.envs.1.find_neg_false_of_mem hSourceMem
          rcases hLists.target_of_find hSourceDistinct hSourceFind with
            ⟨targetKey, hPair, hAssoc⟩
          have hTypeEq : T = targetKey.2 :=
            hLists.types_eq_of_mem hPair
          rcases targetKey with ⟨t, targetT⟩
          simp only at hTypeEq
          subst targetT
          have hHeadSub :
              __substitute_simul_rec (Term.Boolean true)
                  (Term.Var (Term.String s) T) vs ts bvs =
                Term.Var (Term.String t) T := by
            rw [SubstituteSupport.substitute_simul_rec_var_mapped
              (Term.Boolean true) (Term.String s) T vs ts bvs
              hisr hvs hts hbvs hFreeFind hSourceFind,
              hAssoc]
          rcases hAssemble t hHeadSub with ⟨target, hRename, hSub⟩
          exact ⟨target, _, hRename, hSub⟩
        · have hSourceFind :
              __eo_is_neg
                  (__eo_list_find Term.__eo_List_cons vs
                    (Term.Var (Term.String s) T)) =
                Term.Boolean true :=
            hLists.envs.1.find_neg_true_of_not_mem hSourceMem
          have hHeadSub :
              __substitute_simul_rec (Term.Boolean true)
                  (Term.Var (Term.String s) T) vs ts bvs =
                Term.Var (Term.String s) T :=
            SubstituteSupport.substitute_simul_rec_var_unmapped
              (Term.Boolean true) (Term.String s) T vs ts bvs
              hisr hvs hts hbvs hFreeFind hSourceFind
          rcases hAssemble s hHeadSub with ⟨target, hRename, hSub⟩
          exact ⟨target, _, hRename, hSub⟩

/-- Binder handler used to specialize the shared substitution-preservation
engine to uniform renaming. -/
theorem alpha_binder_preserves
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (q v tail a bvs : Term)
    {vsVars bvsVars : List EoVarKey}
    (hVsEnv : EoVarEnvPerm vs vsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)) a))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes vs ts)
    (hTy : __eo_typeof
      (SubstitutePreservationSupport.substResult true
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)) a)
        vs ts bvs) ≠ Term.Stuck)
    (hRec : SubstitutePreservationSupport.SubstitutionPreservationRec true
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)) a)
      vs ts) :
    SubstitutePreservationSupport.SubstitutionPreservationResult true
      (Term.Apply (Term.Apply q
        (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)) a)
      vs ts bvs := by
  let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) tail
  let binderSub :=
    __substitute_simul_rec (Term.Boolean true) binder vs ts bvs
  let bodySub :=
    __substitute_simul_rec (Term.Boolean true) a vs ts bvs
  have hvs : vs ≠ Term.Stuck := hVsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstNe :
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q binder) a) vs ts bvs ≠
        Term.Stuck := by
    intro hStuck
    apply hTy
    change
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean true)
            (Term.Apply (Term.Apply q binder) a) vs ts bvs) =
        Term.Stuck
    rw [hStuck]
    rfl
  have hSubstMk :
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q binder) a) vs ts bvs =
        __eo_mk_apply (Term.Apply q binderSub) bodySub := by
    simpa [binder, binderSub, bodySub] using
      substitute_simul_true_quant_eq_of_ne_stuck
        q v tail a vs ts bvs hvs hts hbvs
        (by simpa [binder] using hSubstNe)
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.Apply q binderSub) bodySub) ≠
        Term.Stuck := by
    rw [← hSubstMk]
    simpa [SubstitutePreservationSupport.substResult, binder] using hTy
  have hMk :
      __eo_mk_apply (Term.Apply q binderSub) bodySub =
        Term.Apply (Term.Apply q binderSub) bodySub :=
    eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
      q binderSub bodySub hTyMk
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q binder) a) vs ts bvs =
        Term.Apply (Term.Apply q binderSub) bodySub := by
    rw [hSubstMk, hMk]
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply q binderSub) bodySub) ≠
        Term.Stuck := by
    rwa [hMk] at hTyMk
  have hOrigTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply q binder) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
      binder] using hFTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hOrigTrans
  rcases eo_var_env_of_list_branch_has_smt_translation hOrigTrans with
    ⟨binderVars, hBinderEnv⟩
  rcases hBvsEnv with ⟨bvsExactVars, hBvsExact, hBvsEquiv⟩
  have hBvsPerm : EoVarEnvPerm bvs bvsVars :=
    ⟨bvsExactVars, hBvsExact, hBvsEquiv⟩
  rcases renamingLists_of_substitute_var_env
      hLists hSourceDistinct hTs hBinderEnv hBvsExact with
    ⟨renamedBinder, binderPairs, hBinderRename, hBinderSubRaw⟩
  have hBinderSubEq : binderSub = renamedBinder := by
    simpa [binderSub, binder] using hBinderSubRaw
  have hBinderSubEnv :
      EoVarEnv binderSub (targetKeys binderPairs) := by
    rw [hBinderSubEq]
    exact hBinderRename.envs.2
  have hBodyBool : __eo_typeof bodySub = Term.Bool :=
    eo_typeof_body_bool_of_quant_type_ne_stuck
      hQ hBinderSubEnv hTyApply
  have hBodyTy : __eo_typeof bodySub ≠ Term.Stuck := by
    rw [hBodyBool]
    intro h
    cases h
  have hBodyTrans : RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
      body_has_smt_translation_of_list_branch_has_smt_translation hOrigTrans
  have hBodyBoth :=
    hRec
      (G := a) (bvs' := bvs)
      (by
        simp
        omega)
      hVsEnv hBvsPerm hBodyTrans hTs hActuals
      (by
        simpa [SubstitutePreservationSupport.substResult, bodySub] using
          hBodyTy)
  have hBodyType : __eo_typeof bodySub = __eo_typeof a := by
    simpa [SubstitutePreservationSupport.substResult, bodySub] using
      hBodyBoth.1
  have hBodySubTrans : RuleProofs.eo_has_smt_translation bodySub := by
    simpa [SubstitutePreservationSupport.substResult, bodySub] using
      hBodyBoth.2
  have hSourceKeysEq : sourceKeys binderPairs = binderVars :=
    EoVarEnv.vars_eq_of_same_env hBinderRename.envs.1 hBinderEnv
  have hBinderSubWf :
      ∀ key, key ∈ targetKeys binderPairs →
        __smtx_type_wf (__eo_to_smt_type key.2) = true :=
    hBinderRename.target_types_wf (by
      intro key hMem
      apply quant_binder_types_wf_of_has_smt_translation
        hQ hOrigTrans hBinderEnv key.1 key.2
      rw [← hSourceKeysEq]
      exact hMem)
  rcases hBinderRename.target_cons_of_source_cons with
    ⟨targetHead, targetTail, hRenamedShape⟩
  have hBinderSubNonNil : binderSub ≠ Term.__eo_List_nil := by
    rw [hBinderSubEq, hRenamedShape]
    intro h
    cases h
  have hOrigBodyBool : __eo_typeof a = Term.Bool := by
    rw [← hBodyType]
    exact hBodyBool
  have hOrigTyBool :
      __eo_typeof (Term.Apply (Term.Apply q binder) a) = Term.Bool := by
    rcases hQ with rfl | rfl
    all_goals
      change __eo_typeof_forall (__eo_typeof binder) (__eo_typeof a) =
        Term.Bool
      rw [eo_typeof_eo_var_env_eq_list hBinderEnv, hOrigBodyBool]
      rfl
  have hSubTyBool :
      __eo_typeof (Term.Apply (Term.Apply q binderSub) bodySub) =
        Term.Bool := by
    rcases hQ with rfl | rfl
    all_goals
      change
        __eo_typeof_forall (__eo_typeof binderSub) (__eo_typeof bodySub) =
          Term.Bool
      rw [eo_typeof_eo_var_env_eq_list hBinderSubEnv, hBodyBool]
      rfl
  refine ⟨?_, ?_⟩
  · simp [SubstitutePreservationSupport.substResult, binder,
      hSubstEq, hSubTyBool, hOrigTyBool]
  · rw [show
        SubstitutePreservationSupport.substResult true
            (Term.Apply (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)) a)
            vs ts bvs =
          Term.Apply (Term.Apply q binderSub) bodySub by
        simpa [SubstitutePreservationSupport.substResult, binder] using
          hSubstEq]
    exact eo_has_smt_translation_quant_of_body_translation_and_type
      q binderSub bodySub hQ hBinderSubEnv hBinderSubNonNil
      (by
        intro s T hMem
        exact hBinderSubWf (s, T) hMem)
      hBodySubTrans hTyApply

/-- Type and SMT-translation preservation for uniform renaming.  All
non-binder cases are discharged by the shared substitution engine. -/
theorem alpha_preserves_type_and_translation
    (F vs ts bvs : Term)
    {pairs : List (EoVarKey × EoVarKey)}
    {vsVars bvsVars : List EoVarKey}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hVsEnv : EoVarEnvPerm vs vsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes vs ts)
    (hTy : __eo_typeof
      (SubstitutePreservationSupport.substResult true F vs ts bvs) ≠
        Term.Stuck) :
    SubstitutePreservationSupport.SubstitutionPreservationResult true
      F vs ts bvs :=
  SubstitutePreservationSupport.substitute_simul_preserves_type_and_translation_with_binder_lt
    (sizeOf F + 1) F vs ts bvs
    (fun q v tail a bvs =>
      alpha_binder_preserves hLists hSourceDistinct q v tail a bvs)
    (by omega) hVsEnv hBvsEnv hFTrans hTs hActuals hTy

/-- Different-name existential congruence.  Alpha conversion pushes the same
witness under the target name on the left and the source name on the right. -/
theorem native_eval_texists_eq_of_renamed_body
    {M N : SmtModel} {s t : native_String} {T : SmtType}
    {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T →
      __smtx_value_canonical v = true →
      __smtx_model_eval (native_model_push M t T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    (native_eval_exists M t T bodyM : SmtValue) =
      (native_eval_exists N s T bodyN : SmtValue) := by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M t T v) bodyM =
          SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) bodyN =
          SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · rintro ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v hTy hCanon] using hEval⟩
    · rintro ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v hTy hCanon] using hEval⟩
  by_cases hM' : PM
  · have hN' : PN := hIff.mp hM'
    simp [hM', hN']
  · have hN' : ¬ PN := fun h => hM' (hIff.mpr h)
    simp [hM', hN']

/-- Evaluation congruence for a whole pair of renamed binder lists. -/
theorem alpha_eval_eo_to_smt_exists
    {vs ts : Term} {pairs : List (EoVarKey × EoVarKey)}
    {source target : Term} {binderPairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTargetDistinct : SkolemizeRule.DistinctList (targetKeys pairs))
    (hBinders : BinderRenaming vs ts pairs source target binderPairs)
    {M N : SmtModel} {bodyM bodyN : SmtTerm}
    (hM : model_wf M) (hN : model_wf N)
    (hRel : AlphaRel M N vs ts)
    (hBinderWf :
      ∀ key, key ∈ binderPairs.map Prod.fst →
        __smtx_type_wf (__eo_to_smt_type key.2) = true)
    (hBase :
      ∀ {M' N' : SmtModel},
        model_wf M' →
        model_wf N' →
        AlphaRel M' N' vs ts →
        __smtx_model_eval M' bodyM = __smtx_model_eval N' bodyN) :
    __smtx_model_eval M (__eo_to_smt_exists target bodyM) =
      __smtx_model_eval N (__eo_to_smt_exists source bodyN) := by
  induction hBinders generalizing M N with
  | nil =>
      simpa [__eo_to_smt_exists] using hBase hM hN hRel
  | @mapped s t T sourceTail targetTail binderPairs hPair hTail ih =>
      have hHeadWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hBinderWf (s, T) (List.Mem.head _)
      change
        __smtx_model_eval M
            (SmtTerm.exists t (__eo_to_smt_type T)
              (__eo_to_smt_exists targetTail bodyM)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists sourceTail bodyN))
      simpa [__smtx_model_eval] using
        native_eval_texists_eq_of_renamed_body
          (fun v hValTy hValCanon => by
            have hM' :
                model_wf
                  (native_model_push M t (__eo_to_smt_type T) v) :=
              model_total_typed_push hM t (__eo_to_smt_type T) v
                hHeadWf hValTy
                (by simpa [value_canonical] using hValCanon)
            have hN' :
                model_wf
                  (native_model_push N s (__eo_to_smt_type T) v) :=
              model_total_typed_push hN s (__eo_to_smt_type T) v
                hHeadWf hValTy
                (by simpa [value_canonical] using hValCanon)
            exact ih hM' hN'
              (alphaRel_push_mapped hLists hSourceDistinct hTargetDistinct
                hRel s t T v hPair)
              (fun key hMem => hBinderWf key (List.Mem.tail _ hMem)))
  | @unmapped s T sourceTail targetTail binderPairs
      hSourceNot hTargetNot hTail ih =>
      have hHeadWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hBinderWf (s, T) (List.Mem.head _)
      have hSourceFree :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons vs
                (Term.Var (Term.String s) T)) =
            Term.Boolean true :=
        hLists.envs.1.find_neg_true_of_not_mem hSourceNot
      have hTargetFree :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons ts
                (Term.Var (Term.String s) T)) =
            Term.Boolean true :=
        hLists.envs.2.find_neg_true_of_not_mem hTargetNot
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists targetTail bodyM)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists sourceTail bodyN))
      simpa [__smtx_model_eval] using
        native_eval_texists_eq_of_renamed_body
          (fun v hValTy hValCanon => by
            have hM' :
                model_wf
                  (native_model_push M s (__eo_to_smt_type T) v) :=
              model_total_typed_push hM s (__eo_to_smt_type T) v
                hHeadWf hValTy
                (by simpa [value_canonical] using hValCanon)
            have hN' :
                model_wf
                  (native_model_push N s (__eo_to_smt_type T) v) :=
              model_total_typed_push hN s (__eo_to_smt_type T) v
                hHeadWf hValTy
                (by simpa [value_canonical] using hValCanon)
            exact ih hM' hN'
              (alphaRel_push_unmapped hLists hSourceDistinct hRel
                s T v hHeadWf hSourceFree hTargetFree)
              (fun key hMem => hBinderWf key (List.Mem.tail _ hMem)))

private theorem target_find_true_of_no_free
    {s : native_String} {T target bound : Term}
    {targetVars boundVars : List EoVarKey}
    (hTargetEnv : EoVarEnvPerm target targetVars)
    (hBoundEnv : EoVarEnvPerm bound boundVars)
    (hBoundDisjoint :
      ∀ key, key ∈ boundVars → key ∉ targetVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) target bound =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons target
          (Term.Var (Term.String s) T)) =
      Term.Boolean true := by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hTargetFree | hBound
  · exact hTargetFree
  · have hBoundMem : ((s, T) : EoVarKey) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBoundEnv hBound
    have hTargetNot : ((s, T) : EoVarKey) ∉ targetVars :=
      hBoundDisjoint (s, T) hBoundMem
    exact EoVarEnvPerm.find_neg_true_of_not_mem hTargetEnv hTargetNot

/-- A false free-occurrence check is hereditary along the ordinary
application paths exposed by the shared substitution dispatcher. -/
private theorem contains_false_of_isNonbinderSubterm
    {b root except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hSubterm : InstantiateRule.IsNonbinderSubterm b root)
    (hNoFree :
      __contains_atomic_term_list_free_rec root except bound =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec b except bound =
      Term.Boolean false := by
  let rec go (root : Term)
      (hSubterm : InstantiateRule.IsNonbinderSubterm b root)
      (hNoFree :
        __contains_atomic_term_list_free_rec root except bound =
          Term.Boolean false) :
      __contains_atomic_term_list_free_rec b except bound =
        Term.Boolean false := by
    cases root with
    | Apply f a =>
        simp only [InstantiateRule.IsNonbinderSubterm] at hSubterm
        rcases hSubterm with rfl | ⟨hNotBinder, hInF | hInA⟩
        · exact hNoFree
        · have hParts :=
            contains_atomic_term_list_free_rec_apply_false_cases
              hExcept hBound
              (fun q v tail hEq => hNotBinder ⟨q, v, tail, hEq⟩)
              hNoFree
          exact go f hInF hParts.1
        · have hParts :=
            contains_atomic_term_list_free_rec_apply_false_cases
              hExcept hBound
              (fun q v tail hEq => hNotBinder ⟨q, v, tail, hEq⟩)
              hNoFree
          exact go a hInA hParts.2
    | _ =>
        simp only [InstantiateRule.IsNonbinderSubterm] at hSubterm
        subst b
        exact hNoFree
  termination_by sizeOf root
  exact go root hSubterm hNoFree

/-- Size-recursive semantic core for true-mode simultaneous renaming.  The
non-binder application dispatcher is shared with substitution; only variables
and quantifier binder pushes are alpha-specific. -/
theorem alpha_eval_gen_lt
    (n : Nat) (F vs ts bound : Term)
    {pairs : List (EoVarKey × EoVarKey)}
    {boundVars : List EoVarKey} {M N : SmtModel}
    (hLt : sizeOf F < n)
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTargetDistinct : SkolemizeRule.DistinctList (targetKeys pairs))
    (hBoundEnv : EoVarEnvPerm bound boundVars)
    (hBoundDisjoint :
      ∀ key, key ∈ boundVars → key ∉ targetKeys pairs)
    (hTsTrans : EoListAllHaveSmtTranslation ts)
    (hFTrans : eoHasSmtTranslation F)
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean true) F vs ts
          Term.__eo_List_nil))
    (hNoSource :
      __contains_atomic_term_list_free_rec F vs bound = Term.Boolean false)
    (hNoTarget :
      __contains_atomic_term_list_free_rec F ts bound = Term.Boolean false)
    (hM : model_wf M) (hN : model_wf N)
    (hRel : AlphaRel M N vs ts) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean true) F vs ts
            Term.__eo_List_nil)) =
      __smtx_model_eval N (__eo_to_smt F) := by
  have hvs : vs ≠ Term.Stuck := hLists.envs.1.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    eoListAllHaveSmtTranslation_ne_stuck hTsTrans
  have hnil : Term.__eo_List_nil ≠ Term.Stuck := by decide
  have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {G bound' : Term} {boundVars' : List EoVarKey}
            {M' N' : SmtModel},
            sizeOf G < sizeOf F →
            EoVarEnvPerm bound' boundVars' →
            (∀ key, key ∈ boundVars' → key ∉ targetKeys pairs) →
            eoHasSmtTranslation G →
            eoHasSmtTranslation
              (__substitute_simul_rec (Term.Boolean true) G vs ts
                Term.__eo_List_nil) →
            __contains_atomic_term_list_free_rec G vs bound' =
              Term.Boolean false →
            __contains_atomic_term_list_free_rec G ts bound' =
              Term.Boolean false →
            model_wf M' →
            model_wf N' →
            AlphaRel M' N' vs ts →
            __smtx_model_eval M'
                (__eo_to_smt
                  (__substitute_simul_rec (Term.Boolean true) G vs ts
                    Term.__eo_List_nil)) =
              __smtx_model_eval N' (__eo_to_smt G) :=
        fun {G bound' boundVars' M' N'} hGLt hBoundEnv' hDisjoint'
            hGTrans hGSubstTrans hGNoSource hGNoTarget hM' hN' hRel' =>
          alpha_eval_gen_lt n G vs ts bound'
            (by omega) hLists hSourceDistinct hTargetDistinct
            hBoundEnv' hDisjoint' hTsTrans hGTrans hGSubstTrans
            hGNoSource hGNoTarget hM' hN' hRel'
      cases F
      case Apply f a =>
        by_cases hBinder :
            ∃ q v tail,
              f = Term.Apply q
                (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)
        · rcases hBinder with ⟨q, v, tail, rfl⟩
          let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) tail
          let binderSub :=
            __substitute_simul_rec (Term.Boolean true) binder vs ts
              Term.__eo_List_nil
          let bodySub :=
            __substitute_simul_rec (Term.Boolean true) a vs ts
              Term.__eo_List_nil
          have hOrigTrans :
              eoHasSmtTranslation (Term.Apply (Term.Apply q binder) a) := by
            simpa [binder] using hFTrans
          have hQ : q = Term.UOp UserOp.forall ∨
              q = Term.UOp UserOp.exists :=
            is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
              hOrigTrans
          rcases eo_var_env_of_list_branch_has_smt_translation hOrigTrans with
            ⟨binderVars, hBinderEnv⟩
          have hSubstNe :
              __substitute_simul_rec (Term.Boolean true)
                  (Term.Apply (Term.Apply q binder) a) vs ts
                    Term.__eo_List_nil ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
          have hRaw :
              __substitute_simul_rec (Term.Boolean true)
                  (Term.Apply (Term.Apply q binder) a) vs ts
                    Term.__eo_List_nil =
                __eo_requires
                  (__contains_atomic_term_list_free_rec ts binder
                    Term.__eo_List_nil)
                  (Term.Boolean false)
                  (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) := by
            simpa [binder, binderSub, bodySub] using
              SubstituteSupport.substTrue_quant q v tail a vs ts
                Term.__eo_List_nil hvs hts hnil
          have hReqNe :
              __eo_requires
                  (__contains_atomic_term_list_free_rec ts binder
                    Term.__eo_List_nil)
                  (Term.Boolean false)
                  (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) ≠
                Term.Stuck := by
            rw [← hRaw]
            exact hSubstNe
          have hCapture :
              __contains_atomic_term_list_free_rec ts binder
                  Term.__eo_List_nil = Term.Boolean false :=
            instantiate_eo_requires_arg_eq_of_ne_stuck hReqNe
          have hReqResult :
              __eo_requires
                  (__contains_atomic_term_list_free_rec ts binder
                    Term.__eo_List_nil)
                  (Term.Boolean false)
                  (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) =
                __eo_mk_apply (__eo_mk_apply q binderSub) bodySub :=
            instantiate_eo_requires_result_eq_of_ne_stuck hReqNe
          have hOuterNe :
              __eo_mk_apply (__eo_mk_apply q binderSub) bodySub ≠
                Term.Stuck := by
            rw [← hReqResult, ← hRaw]
            exact hSubstNe
          have hInnerNe : __eo_mk_apply q binderSub ≠ Term.Stuck :=
            instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
          have hBodySubNe : bodySub ≠ Term.Stuck :=
            instantiate_eo_mk_apply_arg_ne_stuck_of_ne_stuck hOuterNe
          have hInnerEq : __eo_mk_apply q binderSub = Term.Apply q binderSub :=
            instantiate_eo_mk_apply_eq_apply_of_ne_stuck q binderSub hInnerNe
          have hOuterEq :
              __eo_mk_apply (Term.Apply q binderSub) bodySub =
                Term.Apply (Term.Apply q binderSub) bodySub :=
            instantiate_eo_mk_apply_eq_apply_of_ne_stuck
              (Term.Apply q binderSub) bodySub (by simpa [hInnerEq] using hOuterNe)
          have hSubstEq :
              __substitute_simul_rec (Term.Boolean true)
                  (Term.Apply (Term.Apply q binder) a) vs ts
                    Term.__eo_List_nil =
                Term.Apply (Term.Apply q binderSub) bodySub := by
            rw [hRaw, hReqResult, hInnerEq, hOuterEq]
          have hSubstQuantTrans :
              eoHasSmtTranslation
                (Term.Apply (Term.Apply q binderSub) bodySub) := by
            rw [← hSubstEq]
            simpa [binder] using hSubstTrans
          have hBodyTrans : eoHasSmtTranslation a :=
            body_has_smt_translation_of_list_branch_has_smt_translation
              hOrigTrans
          have hTargetOutsideBinder :
              ∀ key, key ∈ targetKeys pairs → key ∉ binderVars :=
            contains_var_env_false_disjoint hLists.envs.2 hBinderEnv hCapture
          have hBinderOutsideTarget :
              ∀ key, key ∈ binderVars → key ∉ targetKeys pairs := by
            intro key hBinderMem hTargetMem
            exact hTargetOutsideBinder key hTargetMem hBinderMem
          rcases binderRenaming_of_substitute hLists hSourceDistinct hTsTrans
              hBinderEnv hBinderOutsideTarget with
            ⟨renamedBinder, binderPairs, hBinderRename, hBinderSubEq⟩
          have hBinderEq : binderSub = renamedBinder := by
            simpa [binderSub] using hBinderSubEq
          rcases hBinderRename.target_cons_of_source_cons with
            ⟨targetName, targetTail, hRenamedShape⟩
          have hBodySubTrans : eoHasSmtTranslation bodySub := by
            rw [hBinderEq, hRenamedShape] at hSubstQuantTrans
            exact body_has_smt_translation_of_list_branch_has_smt_translation
              hSubstQuantTrans
          have hBinderPairVarsEq : binderPairs.map Prod.fst = binderVars :=
            EoVarEnv.vars_eq_of_same_env hBinderRename.envs.1 hBinderEnv
          have hBinderWf :
              ∀ key, key ∈ binderPairs.map Prod.fst →
                __smtx_type_wf (__eo_to_smt_type key.2) = true := by
            intro key hMem
            rw [hBinderPairVarsEq] at hMem
            exact quant_binder_types_wf_of_has_smt_translation
              hQ hOrigTrans hBinderEnv key.1 key.2 hMem
          let fullBound :=
            __eo_list_concat Term.__eo_List_cons binder bound
          have hFullBoundEnv :
              EoVarEnvPerm fullBound (binderVars.reverse ++ boundVars) := by
            simpa [fullBound, binder] using
              EoVarEnvPerm.concat_rev hBinderEnv hBoundEnv
          have hFullDisjoint :
              ∀ key, key ∈ binderVars.reverse ++ boundVars →
                key ∉ targetKeys pairs := by
            intro key hMem
            rcases List.mem_append.1 hMem with hBinderMem | hOldMem
            · exact hBinderOutsideTarget key (by simpa using hBinderMem)
            · exact hBoundDisjoint key hOldMem
          have hBodyNoSource :
              __contains_atomic_term_list_free_rec a vs fullBound =
                Term.Boolean false := by
            simpa [fullBound, binder] using
              contains_atomic_term_list_free_rec_list_branch_false_body hNoSource
          have hBodyNoTarget :
              __contains_atomic_term_list_free_rec a ts fullBound =
                Term.Boolean false := by
            simpa [fullBound, binder] using
              contains_atomic_term_list_free_rec_list_branch_false_body hNoTarget
          rw [hRenamedShape] at hBinderRename
          rw [hSubstEq, hBinderEq, hRenamedShape]
          rcases hQ with hForall | hExists
          · subst q
            change
              __smtx_model_eval M
                  (SmtTerm.not
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons targetName)
                        targetTail)
                      (SmtTerm.not (__eo_to_smt bodySub)))) =
                __smtx_model_eval N
                  (SmtTerm.not
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)
                      (SmtTerm.not (__eo_to_smt a))))
            have hExistsEq :=
              alpha_eval_eo_to_smt_exists hLists hSourceDistinct
                hTargetDistinct hBinderRename hM hN hRel hBinderWf
                (fun {M' N'} hM' hN' hRel' => by
                  have hBodyEq := hRec
                    (G := a) (bound' := fullBound)
                    (by simp; omega) hFullBoundEnv hFullDisjoint
                    hBodyTrans hBodySubTrans hBodyNoSource hBodyNoTarget
                    hM' hN' hRel'
                  have hBodyEq' :
                      __smtx_model_eval M' (__eo_to_smt bodySub) =
                        __smtx_model_eval N' (__eo_to_smt a) := by
                    simpa [bodySub] using hBodyEq
                  show
                    __smtx_model_eval M'
                        (SmtTerm.not (__eo_to_smt bodySub)) =
                      __smtx_model_eval N'
                        (SmtTerm.not (__eo_to_smt a))
                  simp only [__smtx_model_eval]
                  rw [hBodyEq'])
            simp [__smtx_model_eval, hExistsEq]
          · subst q
            change
              __smtx_model_eval M
                  (__eo_to_smt_exists
                    (Term.Apply (Term.Apply Term.__eo_List_cons targetName)
                      targetTail)
                    (__eo_to_smt bodySub)) =
                __smtx_model_eval N
                  (__eo_to_smt_exists
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) tail)
                    (__eo_to_smt a))
            exact alpha_eval_eo_to_smt_exists hLists hSourceDistinct
              hTargetDistinct hBinderRename hM hN hRel hBinderWf
              (fun {M' N'} hM' hN' hRel' =>
                hRec (G := a) (bound' := fullBound)
                  (by simp; omega) hFullBoundEnv hFullDisjoint
                  hBodyTrans hBodySubTrans hBodyNoSource hBodyNoTarget
                  hM' hN' hRel')
        · have hRecArg :
              ∀ {G : Term},
                InstantiateRule.IsNonbinderSubterm G (Term.Apply f a) →
                sizeOf G < sizeOf (Term.Apply f a) →
                eoHasSmtTranslation G →
                eoHasSmtTranslation
                  (__substitute_simul_rec (Term.Boolean true) G vs ts
                    Term.__eo_List_nil) →
                __smtx_model_eval M
                    (__eo_to_smt
                      (__substitute_simul_rec (Term.Boolean true) G vs ts
                        Term.__eo_List_nil)) =
                  __smtx_model_eval N (__eo_to_smt G) := by
            intro G hGSubterm hGLt hGTrans hGSubstTrans
            have hGNoSource := contains_false_of_isNonbinderSubterm
              (EoVarEnvPerm.of_exact hLists.envs.1) hBoundEnv
              hGSubterm hNoSource
            have hGNoTarget := contains_false_of_isNonbinderSubterm
              (EoVarEnvPerm.of_exact hLists.envs.2) hBoundEnv
              hGSubterm hNoTarget
            exact hRec hGLt hBoundEnv hBoundDisjoint hGTrans hGSubstTrans
              hGNoSource hGNoTarget hM hN hRel
          exact InstantiateRule.substitute_simul_eval_nonbinder
            f a vs ts Term.__eo_List_nil
            (EoVarEnvPerm.of_exact hLists.envs.1)
            (EoVarEnvPerm.of_exact EoVarEnv.nil) hTsTrans hBinder
            hFTrans hSubstTrans hM hN hRel.globals hRecArg
      case Var name T =>
        by_cases hString : ∃ s, name = Term.String s
        · rcases hString with ⟨s, rfl⟩
          have hWf := smtx_type_wf_of_var_has_smt_translation hFTrans
          by_cases hSourceMem : ((s, T) : EoVarKey) ∈ sourceKeys pairs
          · have hMapped := hLists.envs.1.find_neg_false_of_mem hSourceMem
            rw [SubstituteSupport.substitute_simul_rec_var_mapped
              (Term.Boolean true) (Term.String s) T vs ts
              Term.__eo_List_nil hisr hvs hts hnil
              (EoVarEnv.nil.find_neg_true_of_not_mem (by simp)) hMapped,
              SubstituteSupport.eval_eo_var]
            exact (hRel.mapped s T hWf hMapped).symm
          · have hSourceFree :=
              hLists.envs.1.find_neg_true_of_not_mem hSourceMem
            have hTargetFree := target_find_true_of_no_free
              (EoVarEnvPerm.of_exact hLists.envs.2) hBoundEnv
              hBoundDisjoint hNoTarget
            rw [SubstituteSupport.substitute_simul_rec_var_unmapped
              (Term.Boolean true) (Term.String s) T vs ts
              Term.__eo_List_nil hisr hvs hts hnil
              (EoVarEnv.nil.find_neg_true_of_not_mem (by simp)) hSourceFree,
              SubstituteSupport.eval_eo_var,
              SubstituteSupport.eval_eo_var]
            exact hRel.agree s T hWf hSourceFree hTargetFree
        · exact false_of_non_string_var_has_smt_translation
            (fun s hEq => hString ⟨s, hEq⟩) hFTrans
      case Stuck =>
        exact False.elim
          (RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck
            hFTrans rfl)
      all_goals
        exact SubstituteSupport.substitute_simul_eval_atom
          (isRename := true) M N _ vs ts Term.__eo_List_nil
          hvs hts hnil
          (by intro f a h; cases h)
          (by intro s T h; cases h)
          (by intro h; cases h)
          hFTrans hSubstTrans hRel.globals

/-- At top level, true-mode renaming preserves evaluation in the ambient
model.  The alpha relation compares against `pushSubstModel`; the source
no-free guard then collapses that model back to the ambient one. -/
theorem alpha_renaming_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (F vs ts : Term)
    {pairs : List (EoVarKey × EoVarKey)}
    (hLists : RenamingLists vs ts pairs)
    (hSourceDistinct : SkolemizeRule.DistinctList (sourceKeys pairs))
    (hTargetDistinct : SkolemizeRule.DistinctList (targetKeys pairs))
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes vs ts)
    (hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean true) F vs ts
        Term.__eo_List_nil))
    (hNoSource :
      __contains_atomic_term_list_free_rec F vs Term.__eo_List_nil =
        Term.Boolean false)
    (hNoTarget :
      __contains_atomic_term_list_free_rec F ts Term.__eo_List_nil =
        Term.Boolean false) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean true) F vs ts
            Term.__eo_List_nil)) =
      __smtx_model_eval M (__eo_to_smt F) := by
  let N := InstantiateRule.pushSubstModel M vs ts
  have hN : model_wf N := by
    simpa [N] using
      InstantiateRule.pushSubstModel_total_typed_of_smt_typed_actuals
        M hM hActuals
  have hRel : AlphaRel M N vs ts := by
    apply alphaRel_of_substFalseRel
    simpa [N] using
      InstantiateRule.substFalseRel_pushSubstModel M hM hActuals
  have hAlpha :
      __smtx_model_eval M
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean true) F vs ts
              Term.__eo_List_nil)) =
        __smtx_model_eval N (__eo_to_smt F) := by
    apply alpha_eval_gen_lt
      (sizeOf F + 1) F vs ts Term.__eo_List_nil
      (by omega) hLists hSourceDistinct hTargetDistinct
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      (by
        intro key hMem
        simp at hMem)
      hTs
      (by
        simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
          hFTrans)
      (by
        simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
          hSubstTrans)
      hNoSource hNoTarget hM hN hRel
  have hCoincidence :
      __smtx_model_eval N (__eo_to_smt F) =
        __smtx_model_eval M (__eo_to_smt F) := by
    apply smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
      (EoVarEnvPerm.of_exact hLists.envs.1)
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      (by
        simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
          hFTrans)
      hNoSource
    simpa [N] using
      InstantiateRule.pushSubstModel_agrees_except M ts hLists.envs.1
  exact hAlpha.trans hCoincidence

private theorem string_name_of_var_translation
    {name T : Term}
    (hTrans : eoHasSmtTranslation (Term.Var name T)) :
    ∃ s : native_String, name = Term.String s := by
  by_cases hName : ∃ s : native_String, name = Term.String s
  · exact hName
  · exact false_of_non_string_var_has_smt_translation
      (fun s hEq => hName ⟨s, hEq⟩) hTrans

/-- Reflection of `__is_renaming_rec = true`, using the command-translation
hypotheses to rule out non-string variable names. -/
theorem renamingLists_of_is_renaming_rec
    (vs ts : Term)
    (hVsTrans : EoListAllHaveSmtTranslation vs)
    (hTsTrans : EoListAllHaveSmtTranslation ts)
    (hGuard : __is_renaming_rec vs ts = Term.Boolean true) :
    ∃ pairs, RenamingLists vs ts pairs := by
  induction vs, ts using __is_renaming_rec.induct with
  | case1 =>
      exact ⟨[], RenamingLists.nil⟩
  | case2 s1 T xs s2 T2 ys ih =>
      rcases hVsTrans with ⟨hVTrans, hXsTrans⟩
      rcases hTsTrans with ⟨hWTrans, hYsTrans⟩
      have hReqNe :
          __eo_requires (__eo_eq T T2) (Term.Boolean true)
              (__is_renaming_rec xs ys) ≠ Term.Stuck := by
        change
          __is_renaming_rec
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var s1 T)) xs)
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var s2 T2)) ys) ≠
            Term.Stuck
        rw [hGuard]
        decide
      have hTypesGuard : __eo_eq T T2 = Term.Boolean true :=
        instantiate_eo_requires_arg_eq_of_ne_stuck hReqNe
      have hTypes : T = T2 :=
        (support_eq_of_eo_eq_true T T2 hTypesGuard).symm
      have hTailGuard : __is_renaming_rec xs ys = Term.Boolean true := by
        rw [← instantiate_eo_requires_result_eq_of_ne_stuck hReqNe]
        exact hGuard
      rcases string_name_of_var_translation hVTrans with ⟨s, rfl⟩
      rcases string_name_of_var_translation hWTrans with ⟨t, ht⟩
      subst T2
      subst s2
      rcases ih hXsTrans hYsTrans hTailGuard with ⟨pairs, hPairs⟩
      exact ⟨_, RenamingLists.cons hPairs⟩
  | case3 vs ts _ _ =>
      simp [__is_renaming_rec] at hGuard

/-- A successful alpha-equivalence checker invocation exposes every guard and
collapses to the equality between the original and renamed terms. -/
theorem prog_alpha_equiv_shape
    (t vs ts : Term)
    (hNe : __eo_prog_alpha_equiv t vs ts ≠ Term.Stuck) :
    __eo_list_setof Term.__eo_List_cons vs = vs ∧
      __eo_list_setof Term.__eo_List_cons ts = ts ∧
      __is_renaming_rec vs ts = Term.Boolean true ∧
      __contains_atomic_term_list_free_rec t vs Term.__eo_List_nil =
        Term.Boolean false ∧
      __contains_atomic_term_list_free_rec t ts Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_alpha_equiv t vs ts =
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
          (__substitute_simul_rec (Term.Boolean true) t vs ts
            Term.__eo_List_nil) := by
  have ht : t ≠ Term.Stuck := by
    intro h
    subst t
    exact hNe rfl
  have hvs : vs ≠ Term.Stuck := by
    intro h
    subst vs
    exact hNe (by cases t <;> rfl)
  have hts : ts ≠ Term.Stuck := by
    intro h
    subst ts
    exact hNe (by cases t <;> cases vs <;> rfl)
  let outerGuard :=
    __eo_and
      (__eo_and
        (__eo_and (__is_var_list vs)
          (__eo_eq (__eo_list_setof Term.__eo_List_cons vs) vs))
        (__eo_and (__is_var_list ts)
          (__eo_eq (__eo_list_setof Term.__eo_List_cons ts) ts)))
      (__is_renaming_rec vs ts)
  let result :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
      (__substitute_simul_rec (Term.Boolean true) t vs ts
        Term.__eo_List_nil)
  let targetReq :=
    __eo_requires
      (__contains_atomic_term_list_free_rec t ts Term.__eo_List_nil)
      (Term.Boolean false) result
  let sourceReq :=
    __eo_requires
      (__contains_atomic_term_list_free_rec t vs Term.__eo_List_nil)
      (Term.Boolean false) targetReq
  have hProgDef :
      __eo_prog_alpha_equiv t vs ts =
        __eo_requires outerGuard (Term.Boolean true) sourceReq := by
    simp [__eo_prog_alpha_equiv, outerGuard, sourceReq,
      targetReq, result]
  have hOuterNe :
      __eo_requires outerGuard (Term.Boolean true) sourceReq ≠
        Term.Stuck := by
    rw [← hProgDef]
    exact hNe
  have hOuterGuard : outerGuard = Term.Boolean true :=
    instantiate_eo_requires_arg_eq_of_ne_stuck hOuterNe
  have hOuterResult :
      __eo_requires outerGuard (Term.Boolean true) sourceReq = sourceReq :=
    instantiate_eo_requires_result_eq_of_ne_stuck hOuterNe
  rcases SubstitutePreservationSupport.eo_and_boolean_true_split
      (by simpa [outerGuard] using hOuterGuard) with
    ⟨hListsGuard, hRenameGuard⟩
  rcases SubstitutePreservationSupport.eo_and_boolean_true_split
      hListsGuard with ⟨hVsGuard, hTsGuard⟩
  rcases SubstitutePreservationSupport.eo_and_boolean_true_split
      hVsGuard with ⟨_hVsList, hVsSetGuard⟩
  rcases SubstitutePreservationSupport.eo_and_boolean_true_split
      hTsGuard with ⟨_hTsList, hTsSetGuard⟩
  have hVsSet : __eo_list_setof Term.__eo_List_cons vs = vs :=
    (support_eq_of_eo_eq_true _ _ hVsSetGuard).symm
  have hTsSet : __eo_list_setof Term.__eo_List_cons ts = ts :=
    (support_eq_of_eo_eq_true _ _ hTsSetGuard).symm
  have hSourceNe : sourceReq ≠ Term.Stuck := by
    rw [← hOuterResult]
    exact hOuterNe
  have hNoSource :
      __contains_atomic_term_list_free_rec t vs Term.__eo_List_nil =
        Term.Boolean false :=
    instantiate_eo_requires_arg_eq_of_ne_stuck hSourceNe
  have hSourceResult : sourceReq = targetReq :=
    instantiate_eo_requires_result_eq_of_ne_stuck hSourceNe
  have hTargetNe : targetReq ≠ Term.Stuck := by
    rw [← hSourceResult]
    exact hSourceNe
  have hNoTarget :
      __contains_atomic_term_list_free_rec t ts Term.__eo_List_nil =
        Term.Boolean false :=
    instantiate_eo_requires_arg_eq_of_ne_stuck hTargetNe
  have hTargetResult : targetReq = result :=
    instantiate_eo_requires_result_eq_of_ne_stuck hTargetNe
  refine ⟨hVsSet, hTsSet, hRenameGuard, hNoSource, hNoTarget, ?_⟩
  simpa [result] using
    hProgDef.trans (hOuterResult.trans (hSourceResult.trans hTargetResult))

end AlphaEquivRule
