module

public import Cpc.Proofs.Closed.Substitute
import all Cpc.Proofs.Closed.Substitute
public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.Translation.Full
import all Cpc.Proofs.Translation.Full
public import Cpc.Proofs.Translation.Inversions
import all Cpc.Proofs.Translation.Inversions

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstituteSupport

local macro "consTerm" v:ident vs:ident : term =>
  `(Term.Apply (Term.Apply Term.__eo_List_cons $v) $vs)

/-- A mapped-substitution entry has the same EO type as the variable it replaces. -/
def SubstEntryPreservesTypes (xs ss : Term) : Prop :=
  ∀ (s : native_String) (T : Term),
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
      __eo_typeof
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))) = T

/-- SMT type equality against a well-formed binder type recovers exact EO type equality. -/
theorem eo_typeof_eq_of_smt_type_eq
    (actual T : Term)
    (hActual : RuleProofs.eo_has_smt_translation actual)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hSmt :
      __smtx_typeof (__eo_to_smt actual) = __eo_to_smt_type T) :
    __eo_typeof actual = T := by
  have hActual' : eoHasSmtTranslation actual := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hActual
  have hMatch :
      __smtx_typeof (__eo_to_smt actual) =
        __eo_to_smt_type (__eo_typeof actual) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation actual hActual'
  have hEq :
      __eo_to_smt_type T = __eo_to_smt_type (__eo_typeof actual) :=
    hSmt.symm.trans hMatch
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    exact TranslationProofs.eo_to_smt_type_eq_reglan hEq.symm
  · have hValid :
        TranslationProofs.eo_type_valid_rec [] T := by
      have hTop : TranslationProofs.eo_type_valid T :=
        TranslationProofs.eo_type_valid_of_smt_wf T hWf
      cases T <;> simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec] using hTop
    exact (TranslationProofs.eo_to_smt_type_eq_of_valid hValid hEq).symm

/-- A term whose SMT image has type `None` cannot satisfy the SMT-translation predicate. -/
theorem no_translation_of_smt_type_none {t : Term} :
    __smtx_typeof (__eo_to_smt t) = SmtType.None ->
    RuleProofs.eo_has_smt_translation t ->
    False := by
  intro hTy hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  exact hTrans hTy

/-- A variable whose name is not an EO string cannot have an SMT translation. -/
theorem false_of_non_string_var_has_smt_translation
    {name S : Term} {P : Prop}
    (hName : ∀ s, name ≠ Term.String s)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Var name S)) :
    P := by
  exfalso
  apply hTrans
  cases name <;>
    try
      (change __smtx_typeof SmtTerm.None = SmtType.None
       exact TranslationProofs.smtx_typeof_none)
  case String s =>
    exact False.elim (hName s rfl)

theorem eo_requires_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_to_smt_type_eq_of_top_valid
    {T U : Term}
    (hValid : TranslationProofs.eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  cases T
  case UOp op =>
    cases op
    case RegLan =>
      have hUReg : __eo_to_smt_type U = SmtType.RegLan := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (TranslationProofs.eo_to_smt_type_eq_reglan hUReg).symm
    all_goals
      exact
        TranslationProofs.eo_to_smt_type_eq_of_valid
          (by simpa [TranslationProofs.eo_type_valid] using hValid) hEq
  all_goals
    exact
      TranslationProofs.eo_to_smt_type_eq_of_valid
        (by simpa [TranslationProofs.eo_type_valid] using hValid) hEq

theorem term_ne_stuck_of_typeof_ne_stuck {t : Term}
    (hTy : __eo_typeof t ≠ Term.Stuck) :
    t ≠ Term.Stuck := by
  intro h
  subst t
  exact hTy rfl

theorem eo_mk_apply_eq_apply_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hTerm : __eo_mk_apply f x ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_ne_stuck hTy
  cases f <;> cases x <;> simp [__eo_mk_apply] at hTerm ⊢

theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      f ≠ Term.Stuck := by
  intro h hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := eo_mk_apply_fun_ne_stuck_of_ne_stuck h
  have hx := eo_mk_apply_arg_ne_stuck_of_ne_stuck h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem eo_mk_apply_ne_stuck_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x ≠ Term.Stuck := by
  intro hStuck
  apply hTy
  rw [hStuck]
  rfl

theorem eo_typeof_apply_arg_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
      X ≠ Term.Stuck := by
  intro h hX
  subst X
  cases F <;> simp [__eo_typeof_apply] at h

theorem eo_typeof_apply_head_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
      F ≠ Term.Stuck := by
  intro h hF
  subst F
  cases X <;> simp [__eo_typeof_apply] at h

/-- A translated EO term list is never `Stuck`. -/
theorem eoListAllHaveSmtTranslation_ne_stuck {ts : Term}
    (hTs : EoListAllHaveSmtTranslation ts) :
    ts ≠ Term.Stuck := by
  intro h
  subst ts
  cases hTs

theorem eo_typeof_apply_eq_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  exact TranslationProofs.eo_typeof_apply_eq_of_non_none_translation
    f x hTransF

theorem eo_typeof_eo_var_env_eq_list
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) :
    __eo_typeof xs = Term.__eo_List := by
  induction hEnv with
  | nil => rfl
  | cons hTail ih =>
      exact TranslationProofs.eo_typeof_list_cons_var _ _ _ ih

theorem eo_typeof_forall_body_bool_of_ne_stuck {T U : Term}
    (hT : T = Term.__eo_List)
    (hTy : __eo_typeof_forall T U ≠ Term.Stuck) :
    U = Term.Bool := by
  subst T
  cases U <;> try rfl
  all_goals
    exfalso
    apply hTy
    simp [__eo_typeof_forall]

theorem eo_typeof_body_bool_of_quant_type_ne_stuck
    {q xs body : Term} {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    __eo_typeof body = Term.Bool := by
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy

theorem eo_typeof_apply_eq_of_head_arg_type_eq
    (f f' x x' : Term)
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hF'Trans : RuleProofs.eo_has_smt_translation f')
    (hFType : __eo_typeof f' = __eo_typeof f)
    (hXType : __eo_typeof x' = __eo_typeof x) :
    __eo_typeof (Term.Apply f' x') =
      __eo_typeof (Term.Apply f x) := by
  rw [eo_typeof_apply_eq_of_has_smt_translation f' x' hF'Trans,
    eo_typeof_apply_eq_of_has_smt_translation f x hFTrans,
    hFType, hXType]

theorem apply_generic_args_have_smt_translation_of_has_smt_translation
    (f a : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a)) :
    RuleProofs.eo_has_smt_translation f ∧
      RuleProofs.eo_has_smt_translation a := by
  have hTrans' : eoHasSmtTranslation (Term.Apply f a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans'
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFTrans, hATrans⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hFTrans
  · simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hATrans

theorem var_apply_generic_smt_type (name T a : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a)) =
      __smtx_typeof_apply
        (__smtx_typeof (__eo_to_smt (Term.Var name T)))
        (__smtx_typeof (__eo_to_smt a)) := by
  cases name <;> try
    (change
      __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof SmtTerm.None)
          (__smtx_typeof (__eo_to_smt a))
     rw [__smtx_typeof.eq_def])
  case String s =>
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
          (__smtx_typeof (__eo_to_smt a))
    rw [__smtx_typeof.eq_def]

theorem eo_to_smt_apply_apply_uop_generic_of_not_smt_binop
    {op : UserOp} {x y : Term}
    (hAnd : op ≠ UserOp.and)
    (hOr : op ≠ UserOp.or)
    (hImp : op ≠ UserOp.imp)
    (hXor : op ≠ UserOp.xor)
    (hEq : op ≠ UserOp.eq)
    (hPlus : op ≠ UserOp.plus)
    (hNeg : op ≠ UserOp.neg)
    (hMult : op ≠ UserOp.mult)
    (hLt : op ≠ UserOp.lt)
    (hLeq : op ≠ UserOp.leq)
    (hGt : op ≠ UserOp.gt)
    (hGeq : op ≠ UserOp.geq)
    (hDiv : op ≠ UserOp.div)
    (hMod : op ≠ UserOp.mod)
    (hSelect : op ≠ UserOp.select)
    (hDivisible : op ≠ UserOp.divisible)
    (hDivTotal : op ≠ UserOp.div_total)
    (hModTotal : op ≠ UserOp.mod_total)
    (hQdivTotal : op ≠ UserOp.qdiv_total)
    (hQdiv : op ≠ UserOp.qdiv)
    (hConcat : op ≠ UserOp.concat)
    (hBvand : op ≠ UserOp.bvand)
    (hBvor : op ≠ UserOp.bvor)
    (hBvnand : op ≠ UserOp.bvnand)
    (hBvnor : op ≠ UserOp.bvnor)
    (hBvxor : op ≠ UserOp.bvxor)
    (hBvxnor : op ≠ UserOp.bvxnor)
    (hBvcomp : op ≠ UserOp.bvcomp)
    (hBvadd : op ≠ UserOp.bvadd)
    (hBvmul : op ≠ UserOp.bvmul)
    (hBvudiv : op ≠ UserOp.bvudiv)
    (hBvurem : op ≠ UserOp.bvurem)
    (hBvsub : op ≠ UserOp.bvsub)
    (hBvsdiv : op ≠ UserOp.bvsdiv)
    (hBvsrem : op ≠ UserOp.bvsrem)
    (hBvsmod : op ≠ UserOp.bvsmod)
    (hBvshl : op ≠ UserOp.bvshl)
    (hBvlshr : op ≠ UserOp.bvlshr)
    (hBvashr : op ≠ UserOp.bvashr)
    (hBvult : op ≠ UserOp.bvult)
    (hBvule : op ≠ UserOp.bvule)
    (hBvugt : op ≠ UserOp.bvugt)
    (hBvuge : op ≠ UserOp.bvuge)
    (hBvslt : op ≠ UserOp.bvslt)
    (hBvsle : op ≠ UserOp.bvsle)
    (hBvsgt : op ≠ UserOp.bvsgt)
    (hBvsge : op ≠ UserOp.bvsge)
    (hBvuaddo : op ≠ UserOp.bvuaddo)
    (hBvsaddo : op ≠ UserOp.bvsaddo)
    (hBvumulo : op ≠ UserOp.bvumulo)
    (hBvsmulo : op ≠ UserOp.bvsmulo)
    (hBvusubo : op ≠ UserOp.bvusubo)
    (hBvssubo : op ≠ UserOp.bvssubo)
    (hBvsdivo : op ≠ UserOp.bvsdivo)
    (hBvultbv : op ≠ UserOp.bvultbv)
    (hBvsltbv : op ≠ UserOp.bvsltbv)
    (hFromBools : op ≠ UserOp._at_from_bools)
    (hStringsDeqDiff : op ≠ UserOp._at_strings_deq_diff)
    (hStringsStoiResult : op ≠ UserOp._at_strings_stoi_result)
    (hStrConcat : op ≠ UserOp.str_concat)
    (hStrContains : op ≠ UserOp.str_contains)
    (hStrAt : op ≠ UserOp.str_at)
    (hStrPrefixof : op ≠ UserOp.str_prefixof)
    (hStrSuffixof : op ≠ UserOp.str_suffixof)
    (hStrLt : op ≠ UserOp.str_lt)
    (hStrLeq : op ≠ UserOp.str_leq)
    (hReRange : op ≠ UserOp.re_range)
    (hReConcat : op ≠ UserOp.re_concat)
    (hReInter : op ≠ UserOp.re_inter)
    (hReUnion : op ≠ UserOp.re_union)
    (hReDiff : op ≠ UserOp.re_diff)
    (hStrInRe : op ≠ UserOp.str_in_re)
    (hSeqNth : op ≠ UserOp.seq_nth)
    (hSetUnion : op ≠ UserOp.set_union)
    (hSetInter : op ≠ UserOp.set_inter)
    (hSetMinus : op ≠ UserOp.set_minus)
    (hSetMember : op ≠ UserOp.set_member)
    (hSetSubset : op ≠ UserOp.set_subset)
    (hStringsItosResult : op ≠ UserOp._at_strings_itos_result)
    (hStringsNumOccur : op ≠ UserOp._at_strings_num_occur)
    (hStringsNumOccurRe : op ≠ UserOp._at_strings_num_occur_re)
    (hArrayDeqDiff : op ≠ UserOp._at_array_deq_diff)
    (hSetsDeqDiff : op ≠ UserOp._at_sets_deq_diff)
    (hTuple : op ≠ UserOp.tuple)
    (hSetInsert : op ≠ UserOp.set_insert)
    (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
        (__eo_to_smt y) := by
  cases op <;> try rfl
  all_goals
    exfalso
    first
    | exact hAnd rfl
    | exact hOr rfl
    | exact hImp rfl
    | exact hXor rfl
    | exact hEq rfl
    | exact hPlus rfl
    | exact hNeg rfl
    | exact hMult rfl
    | exact hLt rfl
    | exact hLeq rfl
    | exact hGt rfl
    | exact hGeq rfl
    | exact hDiv rfl
    | exact hMod rfl
    | exact hSelect rfl
    | exact hDivisible rfl
    | exact hDivTotal rfl
    | exact hModTotal rfl
    | exact hQdivTotal rfl
    | exact hQdiv rfl
    | exact hConcat rfl
    | exact hBvand rfl
    | exact hBvor rfl
    | exact hBvnand rfl
    | exact hBvnor rfl
    | exact hBvxor rfl
    | exact hBvxnor rfl
    | exact hBvcomp rfl
    | exact hBvadd rfl
    | exact hBvmul rfl
    | exact hBvudiv rfl
    | exact hBvurem rfl
    | exact hBvsub rfl
    | exact hBvsdiv rfl
    | exact hBvsrem rfl
    | exact hBvsmod rfl
    | exact hBvshl rfl
    | exact hBvlshr rfl
    | exact hBvashr rfl
    | exact hBvult rfl
    | exact hBvule rfl
    | exact hBvugt rfl
    | exact hBvuge rfl
    | exact hBvslt rfl
    | exact hBvsle rfl
    | exact hBvsgt rfl
    | exact hBvsge rfl
    | exact hBvuaddo rfl
    | exact hBvsaddo rfl
    | exact hBvumulo rfl
    | exact hBvsmulo rfl
    | exact hBvusubo rfl
    | exact hBvssubo rfl
    | exact hBvsdivo rfl
    | exact hBvultbv rfl
    | exact hBvsltbv rfl
    | exact hFromBools rfl
    | exact hStringsDeqDiff rfl
    | exact hStringsStoiResult rfl
    | exact hStrConcat rfl
    | exact hStrContains rfl
    | exact hStrAt rfl
    | exact hStrPrefixof rfl
    | exact hStrSuffixof rfl
    | exact hStrLt rfl
    | exact hStrLeq rfl
    | exact hReRange rfl
    | exact hReConcat rfl
    | exact hReInter rfl
    | exact hReUnion rfl
    | exact hReDiff rfl
    | exact hStrInRe rfl
    | exact hSeqNth rfl
    | exact hSetUnion rfl
    | exact hSetInter rfl
    | exact hSetMinus rfl
    | exact hSetMember rfl
    | exact hSetSubset rfl
    | exact hStringsItosResult rfl
    | exact hStringsNumOccur rfl
    | exact hStringsNumOccurRe rfl
    | exact hArrayDeqDiff rfl
    | exact hSetsDeqDiff rfl
    | exact hTuple rfl
    | exact hSetInsert rfl
    | exact hForall rfl
    | exact hExists rfl

def substitute_uopHasUnarySmtTranslation : UserOp -> Bool
  | UserOp.not
  | UserOp.distinct
  | UserOp._at_purify
  | UserOp.to_real
  | UserOp.to_int
  | UserOp.is_int
  | UserOp.abs
  | UserOp.__eoo_neg_2
  | UserOp.int_pow2
  | UserOp.int_log2
  | UserOp.int_ispow2
  | UserOp._at_int_div_by_zero
  | UserOp._at_mod_by_zero
  | UserOp._at_bvsize
  | UserOp.bvnot
  | UserOp.bvneg
  | UserOp.bvnego
  | UserOp.bvredand
  | UserOp.bvredor
  | UserOp.str_len
  | UserOp.str_rev
  | UserOp.str_to_lower
  | UserOp.str_to_upper
  | UserOp.str_to_code
  | UserOp.str_from_code
  | UserOp.str_is_digit
  | UserOp.str_to_int
  | UserOp.str_from_int
  | UserOp.str_to_re
  | UserOp._at_strings_stoi_non_digit
  | UserOp.re_mult
  | UserOp.re_plus
  | UserOp.re_opt
  | UserOp.re_comp
  | UserOp.seq_unit
  | UserOp.set_singleton
  | UserOp.set_choose
  | UserOp.set_is_empty
  | UserOp.set_is_singleton
  | UserOp._at_div_by_zero
  | UserOp.ubv_to_int
  | UserOp.sbv_to_int => true
  | _ => false

theorem substitute_typeof_apply_none_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__smtx_typeof_apply]

theorem substitute_typeof_apply_reglan_head_eq_none
    (f x : SmtTerm)
    (hF : __smtx_typeof f = SmtType.RegLan)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  rw [hGeneric, hF]
  rfl

theorem substitute_typeof_apply_tuple_unit_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__eo_to_smt_tuple_decl,
    TranslationProofs.smtx_typeof_tuple_unit_translation]
  rfl

theorem substitute_uop_apply_typeof_none_of_not_unary_smt_translation
    (op : UserOp) (x : Term) :
    substitute_uopHasUnarySmtTranslation op = false ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None := by
  intro hUnary
  cases op <;>
    simp [substitute_uopHasUnarySmtTranslation] at hUnary ⊢
  case re_allchar =>
    exact substitute_typeof_apply_reglan_head_eq_none
      SmtTerm.re_allchar (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_none =>
    exact substitute_typeof_apply_reglan_head_eq_none
      SmtTerm.re_none (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_all =>
    exact substitute_typeof_apply_reglan_head_eq_none
      SmtTerm.re_all (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case tuple_unit =>
    exact substitute_typeof_apply_tuple_unit_head_eq_none (__eo_to_smt x)
  all_goals
    first
    | exact substitute_typeof_apply_none_head_eq_none (__eo_to_smt x)

theorem substitute_uopHasUnarySmtTranslation_eq_true_of_apply_translation
    {op : UserOp} {x : Term}
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x)) :
    substitute_uopHasUnarySmtTranslation op = true := by
  cases hUnary : substitute_uopHasUnarySmtTranslation op
  · exfalso
    exact
      no_translation_of_smt_type_none
        (t := Term.Apply (Term.UOp op) x)
        (substitute_uop_apply_typeof_none_of_not_unary_smt_translation
          op x hUnary)
        hTrans
  · rfl

theorem eo_typeof_apply_apply_uop_generic_support_of_unary_smt_translation
    {op : UserOp}
    (hUnary : substitute_uopHasUnarySmtTranslation op = true) :
    (∀ X Y,
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
        Term.Stuck ->
      __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ∧
        __eo_typeof Y ≠ Term.Stuck) ∧
    (∀ X X' Y Y',
      __eo_typeof (Term.Apply (Term.UOp op) X') =
        __eo_typeof (Term.Apply (Term.UOp op) X) ->
      __eo_typeof Y' = __eo_typeof Y ->
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X') Y') =
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y)) := by
  constructor
  · intro X Y hApp
    constructor
    · intro hHead
      cases op <;> simp [substitute_uopHasUnarySmtTranslation] at hUnary
      all_goals
        change
          __eo_typeof_apply
              (__eo_typeof (Term.Apply (Term.UOp _) X))
              (__eo_typeof Y) ≠ Term.Stuck at hApp
        exact eo_typeof_apply_head_ne_stuck hApp hHead
    · intro hY
      cases op <;> simp [substitute_uopHasUnarySmtTranslation] at hUnary
      all_goals
        change
          __eo_typeof_apply
              (__eo_typeof (Term.Apply (Term.UOp _) X))
              (__eo_typeof Y) ≠ Term.Stuck at hApp
        exact eo_typeof_apply_arg_ne_stuck hApp hY
  · intro X X' Y Y' hHead hY
    cases op <;> simp [substitute_uopHasUnarySmtTranslation] at hUnary
    all_goals
      change
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.UOp _) X'))
            (__eo_typeof Y') =
          __eo_typeof_apply (__eo_typeof (Term.Apply (Term.UOp _) X))
            (__eo_typeof Y)
      rw [hHead, hY]

theorem eo_to_smt_distinct_ne_dt_sel (x : Term) :
    ∀ s d i j, __eo_to_smt_distinct x ≠ SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases x <;> try cases h
  case Apply f a =>
    cases f <;> try cases h
    case Apply g b =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> simp [__eo_to_smt_distinct] at h
    case UOp op =>
      cases op <;> simp [__eo_to_smt_distinct] at h

theorem eo_to_smt_distinct_ne_dt_tester (x : Term) :
    ∀ s d i, __eo_to_smt_distinct x ≠ SmtTerm.DtTester s d i := by
  intro s d i h
  cases x <;> try cases h
  case Apply f a =>
    cases f <;> try cases h
    case Apply g b =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> simp [__eo_to_smt_distinct] at h
    case UOp op =>
      cases op <;> simp [__eo_to_smt_distinct] at h

theorem eo_to_smt_uop_apply_ne_dt_sel (op : UserOp) (x : Term) :
    ∀ s d i j,
      __eo_to_smt (Term.Apply (Term.UOp op) x) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases op <;> try cases h
  case distinct =>
    change
      native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct x) =
        SmtTerm.DtSel s d i j at h
    cases hElem :
      native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None <;>
      simp [native_ite, hElem] at h
    exact eo_to_smt_distinct_ne_dt_sel x s d i j h
  case _at_bvsize =>
    change
      (let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))
       native_ite (native_zleq 0 _v0)
          (SmtTerm._at_purify (SmtTerm.Numeral _v0)) SmtTerm.None) =
        SmtTerm.DtSel s d i j at h
    simp only at h
    cases hSize :
      native_zleq 0
        (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) <;>
      simp [native_ite, hSize] at h

theorem eo_to_smt_uop_apply_ne_dt_tester (op : UserOp) (x : Term) :
    ∀ s d i,
      __eo_to_smt (Term.Apply (Term.UOp op) x) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  cases op <;> try cases h
  case distinct =>
    change
      native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct x) =
        SmtTerm.DtTester s d i at h
    cases hElem :
      native_Teq (__eo_to_smt_typed_list_elem_type x) SmtType.None <;>
      simp [native_ite, hElem] at h
    exact eo_to_smt_distinct_ne_dt_tester x s d i h
  case _at_bvsize =>
    change
      (let _v0 := __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))
       native_ite (native_zleq 0 _v0)
          (SmtTerm._at_purify (SmtTerm.Numeral _v0)) SmtTerm.None) =
        SmtTerm.DtTester s d i at h
    simp only at h
    cases hSize :
      native_zleq 0
        (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) <;>
      simp [native_ite, hSize] at h

theorem dtcons_reserved_false_of_apply_has_smt_translation
    {s : native_String} {d : DatatypeDecl} {i : native_Nat} {a : Term}
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.DtCons s d i) a)) :
    __eo_to_smt_reserved_datatype_name s = false := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i))
          (__eo_to_smt a)) ≠
      SmtType.None at hTrans
  cases hReserved : __eo_to_smt_reserved_datatype_name s
  · rfl
  · exfalso
    rw [hReserved] at hTrans
    exact hTrans (by
      simpa [native_ite] using
        TranslationProofs.typeof_apply_none_eq (__eo_to_smt a))

theorem dtsel_reserved_false_of_apply_has_smt_translation
    {s : native_String} {d : DatatypeDecl} {i j : native_Nat} {a : Term}
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.DtSel s d i j) a)) :
    __eo_to_smt_reserved_datatype_name s = false := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
          (__eo_to_smt a)) ≠
      SmtType.None at hTrans
  cases hReserved : __eo_to_smt_reserved_datatype_name s
  · rfl
  · exfalso
    rw [hReserved] at hTrans
    exact hTrans (by
      simpa [native_ite] using
        TranslationProofs.typeof_apply_none_eq (__eo_to_smt a))

theorem substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
    (hFType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs) =
        __eo_typeof f)
    (hAType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ss bvs) =
      __eo_typeof (Term.Apply f a) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    substitute_simul_rec_apply
      (Term.Boolean isRename) f a xs ss bvs
      hisr hxs hss hbvs hNotBinder
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTy
  rw [hMk]
  exact
    eo_typeof_apply_eq_of_head_arg_type_eq
      f (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
      a (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)
      hFTrans hFSubTrans hFType hAType

theorem substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
    {isRename : Bool}
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean isRename) f xs ss bvs ≠
      Term.Stuck := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    substitute_simul_rec_apply
      (Term.Boolean isRename) f a xs ss bvs
      hisr hxs hss hbvs hNotBinder
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  exact
    eo_mk_apply_fun_ne_stuck_of_ne_stuck
      (eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk)

theorem substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
    {isRename : Bool}
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
      Term.Stuck := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    substitute_simul_rec_apply
      (Term.Boolean isRename) f a xs ss bvs
      hisr hxs hss hbvs hNotBinder
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hTy (by rw [hSubstEq, hStuck])
  have hMk :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hApplyTy :
      __eo_typeof
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hTyMk (by rw [hMk, hStuck])
  have hApplyEq :
      __eo_typeof
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        __eo_typeof_apply
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) :=
    eo_typeof_apply_eq_of_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
      (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)
      hFSubTrans
  have hApplyTy' :
      __eo_typeof_apply
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hApplyTy (by rw [hApplyEq, hStuck])
  exact eo_typeof_apply_arg_ne_stuck hApplyTy'

theorem eo_typeof_ne_stuck_of_has_smt_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
    __eo_typeof t ≠ Term.Stuck := by
  have hTrans' : eoHasSmtTranslation t := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hTrans
  intro hTy
  have hMatch :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans'
  exact hTrans' (by
    rw [hMatch, hTy]
    rfl)

/-- Quantifier-shaped substitution case: if the substituted quantifier has a
non-`Stuck` type, the capture-avoidance `requires` guard returned the rebuilt
quantified body. -/
theorem substitute_simul_quant_eq_of_typeof_ne_stuck
    (q v vs a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q (consTerm v vs)) a)
        xs ss bvs =
      __eo_mk_apply
        (Term.Apply q (consTerm v vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ss
          (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) :=
    substFalse_quant q v vs a xs ss bvs hxs hss hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  rw [hSubstEq]
  exact eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_eq_of_ne_stuck
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q (consTerm v vs)) a)
        xs ss bvs =
      __eo_mk_apply
        (Term.Apply q (consTerm v vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ss
          (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) :=
    substFalse_quant q v vs a xs ss bvs hxs hss hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    exact hNe (by rw [hSubstEq, hReqStuck])
  rw [hSubstEq]
  exact eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_typeof_eq_of_typeof_ne_stuck
    (q v vs a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hQuantTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply q (consTerm v vs)) a))
    (hBodyType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) =
        __eo_typeof a)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Apply q (consTerm v vs)) a) := by
  have hSubstEq :=
    substitute_simul_quant_eq_of_typeof_ne_stuck
      q v vs a xs ss bvs hXsEnv hBvsEnv hSs hTy
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (Term.Apply q (consTerm v vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) =
        Term.Apply
          (Term.Apply q (consTerm v vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTy
  rw [hMk]
  have hQuantTrans' :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply q (consTerm v vs)) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hQuantTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hQuantTrans'
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof (consTerm v vs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) =
        __eo_typeof_forall (__eo_typeof (consTerm v vs)) (__eo_typeof a)
    rw [hBodyType]
  · change
      __eo_typeof_forall (__eo_typeof (consTerm v vs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) =
        __eo_typeof_forall (__eo_typeof (consTerm v vs)) (__eo_typeof a)
    rw [hBodyType]

theorem substitute_simul_rec_atom_eq_self_of_ne_stuck
    {isRename : Bool}
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hSubstNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs = F := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil)
          (Term.Boolean true) F :=
    substitute_simul_rec_atom
      (Term.Boolean isRename) F xs ss bvs
      hisr hxs hss hbvs hNotApply hNotVar hNotStuck
  rw [hHeadEq] at hSubstNe ⊢
  exact eo_requires_result_eq_of_ne_stuck hSubstNe

theorem substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs) =
      __eo_typeof F := by
  have hSubstNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_ne_stuck hTy
  rw [substitute_simul_rec_atom_eq_self_of_ne_stuck
    F xs ss bvs hXsEnv hBvsEnv hSs
    hNotApply hNotVar hNotStuck hSubstNe]

theorem substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
    {isRename : Bool}
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs) := by
  rw [substitute_simul_rec_atom_eq_self_of_ne_stuck
    F xs ss bvs hXsEnv hBvsEnv hSs
    hNotApply hNotVar hNotStuck hNe]
  exact hFTrans

theorem substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (F a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        F ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply F a) =
        SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a))
    (hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt F))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply F a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply F a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply F a) xs ss bvs) =
      __eo_typeof (Term.Apply F a) := by
  have hArgs :=
    apply_generic_args_have_smt_translation_of_has_smt_translation
      F a hTranslate hGeneric hTrans
  have hFTrans : RuleProofs.eo_has_smt_translation F := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs ≠
        Term.Stuck :=
    substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hTy
  have hHeadSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs) :=
    substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
      F xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      hFTrans hHeadNe
  have hHeadType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs) =
        __eo_typeof F :=
    substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
      F xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      (eo_typeof_ne_stuck_of_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs)
        hHeadSubTrans)
  have hATy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck :=
    substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hHeadSubTrans hTy
  exact
    substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hFTrans
      hHeadSubTrans hHeadType (hARec hATrans hATy) hTy

theorem substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (F a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        F ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply F a) =
        SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a))
    (hNoSel :
      ∀ s d i j,
        __eo_to_smt F ≠ SmtTerm.DtSel s d i j)
    (hNoTester :
      ∀ s d i,
        __eo_to_smt F ≠ SmtTerm.DtTester s d i)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply F a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply F a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply F a) xs ss bvs) =
      __eo_typeof (Term.Apply F a) := by
  exact
    substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      hNotBinder hTranslate
      (generic_apply_type_of_non_special_head_closed
        (__eo_to_smt F) (__eo_to_smt a) hNoSel hNoTester)
      hTrans hARec hTy

theorem substitute_simul_rec_apply_dtsel_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat)
    (a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.DtSel s d i j) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.DtSel s d i j) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.DtSel s d i j) a) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hNotBinder :
      ∀ q v vs, Term.DtSel s d i j ≠ Term.Apply q (consTerm v vs) := by
    intro q v vs h
    cases h
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.DtSel s d i j) a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.DtSel s d i j) xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    substitute_simul_rec_apply
      (Term.Boolean isRename) (Term.DtSel s d i j) a xs ss bvs
      hisr hxs hss hbvs hNotBinder
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.DtSel s d i j) xs ss bvs ≠
        Term.Stuck :=
    substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.DtSel s d i j) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hTy
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.DtSel s d i j) xs ss bvs =
        Term.DtSel s d i j :=
    substitute_simul_rec_atom_eq_self_of_ne_stuck
      (Term.DtSel s d i j) xs ss bvs hXsEnv hBvsEnv hSs
      (by intro f x h; cases h)
      (by intro name T h; cases h)
      (by intro h; cases h)
      hHeadNe
  rw [hSubstEq, hHeadEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (Term.DtSel s d i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply (Term.DtSel s d i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTy
  rw [hMk] at hTy ⊢
  have hReserved :
      __eo_to_smt_reserved_datatype_name s = false :=
    dtsel_reserved_false_of_apply_has_smt_translation hTrans
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
          (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    change
      __smtx_typeof
          (SmtTerm.Apply
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
            (__eo_to_smt a)) ≠
        SmtType.None at hTrans
    rw [hReserved] at hTrans
    simpa [native_ite] using hTrans
  have hATrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [dt_sel_arg_datatype_of_non_none hApplyNN]
    intro h
    cases h
  have hATy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    intro hArgTy
    apply hTy
    change
      __eo_typeof_apply
          (__eo_typeof (Term.DtSel s d i j))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        Term.Stuck
    rw [hArgTy]
    rfl
  have hAType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        __eo_typeof a :=
    hARec hATrans hATy
  change
    __eo_typeof_apply
        (__eo_typeof (Term.DtSel s d i j))
        (__eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
      __eo_typeof_apply
        (__eo_typeof (Term.DtSel s d i j))
        (__eo_typeof a)
  rw [hAType]

theorem substitute_simul_rec_var_string_typeof_eq
    {isRename : Bool}
    (s : native_String) (T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hss : ss ≠ Term.Stuck)
    (hEntryTypes : SubstEntryPreservesTypes xs ss) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Var (Term.String s) T) xs ss bvs) = T := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvExact, hBvExact, _hBvEquiv⟩
  by_cases hBound : (s, T) ∈ bvExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) T)) = Term.Boolean false :=
      hBvExact.find_neg_false_of_mem hBound
    rw [substitute_simul_rec_var_bound
      (Term.Boolean isRename) (Term.String s) T xs ss bvs
      hisr hxs hss hbvs hb]
    rfl
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) T)) = Term.Boolean true :=
      hBvExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, T) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) = Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      rw [substitute_simul_rec_var_mapped
        (Term.Boolean isRename) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hb hx]
      exact hEntryTypes s T hx
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) = Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      rw [substitute_simul_rec_var_unmapped
        (Term.Boolean isRename) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hb hx]
      rfl

theorem substitute_simul_rec_var_any_typeof_eq
    {isRename : Bool}
    (name T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name T) xs ss bvs) =
      __eo_typeof (Term.Var name T) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_rec_var_string_typeof_eq
        s T xs ss bvs hXsEnv hBvsEnv
        (eoListAllHaveSmtTranslation_ne_stuck hSs) hEntryTypes
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

theorem substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
    {isRename : Bool}
    (name T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T))
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name T) xs ss bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Var name T) xs ss bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
    have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
    have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
    have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
    rcases hBvsEnv with ⟨bvExact, hBvExact, _hBvEquiv⟩
    by_cases hBound : (s, T) ∈ bvExact
    · have hb :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons bvs
                (Term.Var (Term.String s) T)) = Term.Boolean false :=
        hBvExact.find_neg_false_of_mem hBound
      rw [substitute_simul_rec_var_bound
        (Term.Boolean isRename) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hb]
      exact hVarTrans
    · have hb :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons bvs
                (Term.Var (Term.String s) T)) = Term.Boolean true :=
        hBvExact.find_neg_true_of_not_mem hBound
      rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
      by_cases hMapped : (s, T) ∈ xsExact
      · have hx :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) = Term.Boolean false :=
          hXsExact.find_neg_false_of_mem hMapped
        have hSubstEq :
            __substitute_simul_rec (Term.Boolean isRename)
                (Term.Var (Term.String s) T) xs ss bvs =
              __assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) :=
          substitute_simul_rec_var_mapped
            (Term.Boolean isRename) (Term.String s) T xs ss bvs
            hisr hxs hss hbvs hb hx
        have hEntryNe :
            __assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) ≠
              Term.Stuck := by
          rwa [hSubstEq] at hNe
        have hEntryTrans :
            eoHasSmtTranslation
              (__assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T))) :=
          assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck
            ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))
            hSs hEntryNe
        simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
          hSubstEq] using hEntryTrans
      · have hx :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) = Term.Boolean true :=
          hXsExact.find_neg_true_of_not_mem hMapped
        rw [substitute_simul_rec_var_unmapped
          (Term.Boolean isRename) (Term.String s) T xs ss bvs
          hisr hxs hss hbvs hb hx]
        exact hVarTrans
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

theorem substitute_simul_rec_apply_var_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (name T a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Var name T ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Var name T) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a))
    (hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Var name T)))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Var name T) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name T) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name T) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Var name T) a) := by
  have hArgs :=
    apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Var name T) a hTranslate hGeneric hTrans
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Var name T) := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name T) xs ss bvs ≠
        Term.Stuck :=
    substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hTy
  have hHeadSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name T) xs ss bvs) :=
    substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
      name T xs ss bvs hXsEnv hBvsEnv hSs hHeadTrans hHeadNe
  have hHeadType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Var name T) xs ss bvs) =
        __eo_typeof (Term.Var name T) :=
    substitute_simul_rec_var_any_typeof_eq
      name T xs ss bvs hXsEnv hBvsEnv hSs hEntryTypes hHeadTrans
  have hATy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck :=
    substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hHeadSubTrans hTy
  exact
    substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hHeadTrans hHeadSubTrans hHeadType
      (hARec hATrans hATy) hTy

theorem substitute_simul_rec_uop_eq_self
    {isRename : Bool}
    (op : UserOp) (xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss) :
    __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
      Term.UOp op := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp op) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp op) :=
    substitute_simul_rec_atom
      (Term.Boolean isRename) (Term.UOp op) xs ss bvs
      hisr hxs hss hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

theorem substitute_simul_rec_uop1_eq_self
    {isRename : Bool}
    (op : UserOp1) (idx xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss) :
    __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ss bvs =
      Term.UOp1 op idx := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ss bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp1 op idx) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp1 op idx) :=
    substitute_simul_rec_atom
      (Term.Boolean isRename) (Term.UOp1 op idx) xs ss bvs
      hisr hxs hss hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

theorem substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hTypeCong :
      ∀ X Y,
        __eo_typeof X = __eo_typeof Y ->
          __eo_typeof (Term.Apply (Term.UOp op) X) =
            __eo_typeof (Term.Apply (Term.UOp op) Y))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ss bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ss bvs hXsEnv hBvsEnv hSs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs =
        __eo_mk_apply (Term.UOp op) aSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) a xs ss bvs
        hisr hxs hss hbvs hNotBinder
    simpa [aSub, hHeadSub] using hApplyEq
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hMk :
      __eo_mk_apply (Term.UOp op) aSub =
        Term.Apply (Term.UOp op) aSub :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hFTransEo
  have hAType :
      __eo_typeof aSub = __eo_typeof a :=
    hRecArg hATrans (hArgTyNe aSub hTyApply)
  rw [hSubstEq, hMk]
  exact hTypeCong aSub a hAType

theorem substitute_simul_binary_op_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (x y xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hArgTyNe :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
          Term.Stuck ->
        __eo_typeof X ≠ Term.Stuck ∧ __eo_typeof Y ≠ Term.Stuck)
    (hTypeCong :
      ∀ X₁ Y₁ X₂ Y₂,
        __eo_typeof X₁ = __eo_typeof Y₁ ->
        __eo_typeof X₂ = __eo_typeof Y₂ ->
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X₁) X₂) =
          __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) Y₁) Y₂))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) =
          __eo_typeof x)
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) =
          __eo_typeof y)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ss bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ss bvs hXsEnv hBvsEnv hSs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x) xs ss bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) x xs ss bvs
        hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp op) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp op) xSub) ySub (by
      rw [← hInnerMk]
      exact hOuterNe)
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases hArgExtract hFTransEo with ⟨hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  rcases hArgTyNe xSub ySub hTyApply with ⟨hXSubTy, hYSubTy⟩
  have hXTy : __eo_typeof xSub = __eo_typeof x :=
    hRecX hXTrans hXSubTy
  have hYTy : __eo_typeof ySub = __eo_typeof y :=
    hRecY hYTrans hYSubTy
  rw [hSubstEq, hInnerMk, hOuterMk]
  exact hTypeCong xSub x ySub y hXTy hYTy

theorem eo_typeof_tuple_stuck_left (Y : Term) :
    __eo_typeof_tuple Term.Stuck Y = Term.Stuck := by
  rfl

theorem eo_typeof_tuple_stuck_right (X : Term) :
    __eo_typeof_tuple X Term.Stuck = Term.Stuck := by
  cases X <;> rfl

theorem eo_typeof_bvult_stuck_left (Y : Term) :
    __eo_typeof_bvult Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_bvult_stuck_right (X : Term) :
    __eo_typeof_bvult X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_set_insert_stuck_right (X : Term) :
    __eo_typeof_set_insert X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_set_insert_eq_set_of_base_set
    (L T : Term)
    (hNN :
      __eo_typeof_set_insert L (Term.Apply (Term.UOp UserOp.Set) T) ≠
        Term.Stuck) :
    __eo_typeof_set_insert L (Term.Apply (Term.UOp UserOp.Set) T) =
      Term.Apply (Term.UOp UserOp.Set) T := by
  cases L <;> try (exfalso; apply hNN; rfl)
  case Apply f U =>
    cases f <;> try (exfalso; apply hNN; rfl)
    case UOp op =>
      cases op <;> try (exfalso; apply hNN; rfl)
      case _at__at_TypedList =>
        have hReqNN :
            __eo_requires (__eo_eq U T) (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.Set) U) ≠
              Term.Stuck := by
          simpa [__eo_typeof_set_insert] using hNN
        have hGuard : __eo_eq U T = Term.Boolean true :=
          eo_requires_eq_of_ne_stuck hReqNN
        have hTU : T = U := eq_of_eo_eq_true U T hGuard
        change
          __eo_requires (__eo_eq U T) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.Set) U) =
            Term.Apply (Term.UOp UserOp.Set) T
        rw [eo_requires_result_eq_of_ne_stuck hReqNN]
        rw [hTU]

theorem substitute_simul_set_insert_typeof_eq_of_typeof_ne_stuck
    {isRename : Bool}
    (typedList base xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_insert) typedList ≠
          Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base))
    (hRecBase :
      RuleProofs.eo_has_smt_translation base ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) base xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) base xs ss bvs) =
          __eo_typeof base)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base)
          xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base)
          xs ss bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base) := by
  let typedListSub :=
    __substitute_simul_rec (Term.Boolean isRename) typedList xs ss bvs
  let baseSub :=
    __substitute_simul_rec (Term.Boolean isRename) base xs ss bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp UserOp.set_insert) xs ss bvs =
        Term.UOp UserOp.set_insert :=
    substitute_simul_rec_uop_eq_self
      UserOp.set_insert xs ss bvs hXsEnv hBvsEnv hSs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.set_insert) typedList) xs ss bvs =
        __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp UserOp.set_insert) typedList
        xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [typedListSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply (Term.UOp UserOp.set_insert) typedList)
        base xs ss bvs hisr hxs hss hbvs hNotBinder
    simpa [baseSub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub =
        Term.Apply (Term.UOp UserOp.set_insert) typedListSub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.set_insert) typedListSub hInnerNe
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.set_insert) typedListSub) baseSub
      (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hSetNN :
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None := by
    have h := hFTransEo
    unfold eoHasSmtTranslation at h
    change
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None at h
    exact h
  rcases eo_to_smt_set_insert_shape_of_non_none
      typedList (__eo_to_smt base) hSetNN with
    ⟨A, _hSetSmt, hBaseSmt, hElem, hANN⟩
  have hBaseTransEo : eoHasSmtTranslation base := by
    unfold eoHasSmtTranslation
    rw [hBaseSmt]
    simp
  have hBaseTrans : RuleProofs.eo_has_smt_translation base := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hBaseTransEo
  rcases
      TranslationProofs.eo_typeof_eq_set_of_smt_set_from_ih
        base
        (fun _ =>
          TranslationProofs.eo_to_smt_typeof_matches_translation
            base hBaseTransEo)
        hBaseSmt with
    ⟨T, hBaseType, hTToA⟩
  have hElemNN :
      __eo_to_smt_typed_list_elem_type typedList ≠ SmtType.None := by
    rw [hElem]
    exact hANN
  rcases
      TranslationProofs.eo_to_smt_typed_list_elem_type_of_non_none
        typedList hElemNN with
    ⟨U, hTypedListType, hUToElem, hUValid⟩
  have hUToA : __eo_to_smt_type U = A := by
    rw [hUToElem, hElem]
  have hUT : U = T :=
    eo_to_smt_type_eq_of_top_valid hUValid (hUToA.trans hTToA.symm)
  have hTValid : TranslationProofs.eo_type_valid T := by
    rwa [← hUT]
  have hTNe : T ≠ Term.Stuck :=
    TranslationProofs.eo_type_valid_not_stuck hTValid
  have hOrigSetType :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) =
        Term.Apply (Term.UOp UserOp.Set) T := by
    change
      __eo_typeof_set_insert (__eo_typeof typedList) (__eo_typeof base) =
        Term.Apply (Term.UOp UserOp.Set) T
    rw [hTypedListType, hBaseType, hUT]
    simp [__eo_typeof_set_insert, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not]
  have hBaseSubTyNe :
      __eo_typeof baseSub ≠ Term.Stuck := by
    intro hBaseStuck
    apply hTyApply
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) =
        Term.Stuck
    rw [hBaseStuck]
    exact eo_typeof_set_insert_stuck_right (__eo_typeof typedListSub)
  have hBaseSubTy :
      __eo_typeof baseSub = __eo_typeof base :=
    hRecBase hBaseTrans hBaseSubTyNe
  have hBaseSubType :
      __eo_typeof baseSub = Term.Apply (Term.UOp UserOp.Set) T := by
    rw [hBaseSubTy, hBaseType]
  have hSubSetType :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) =
        Term.Apply (Term.UOp UserOp.Set) T := by
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) =
        Term.Apply (Term.UOp UserOp.Set) T
    rw [hBaseSubType]
    apply eo_typeof_set_insert_eq_set_of_base_set
    have h := hTyApply
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) ≠
        Term.Stuck at h
    rwa [hBaseSubType] at h
  rw [hSubstEq, hInnerMk, hOuterMk]
  rw [hSubSetType, hOrigSetType]

end SubstituteSupport
