module

public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

def applyApplyUOpNeedsSpecialTranslation : UserOp -> Prop
  | UserOp.or => True
  | UserOp.and => True
  | UserOp.imp => True
  | UserOp.xor => True
  | UserOp.eq => True
  | UserOp.plus => True
  | UserOp.neg => True
  | UserOp.mult => True
  | UserOp.lt => True
  | UserOp.leq => True
  | UserOp.gt => True
  | UserOp.geq => True
  | UserOp.div => True
  | UserOp.mod => True
  | UserOp.divisible => True
  | UserOp.div_total => True
  | UserOp.mod_total => True
  | UserOp.select => True
  | UserOp._at_array_deq_diff => True
  | UserOp.concat => True
  | UserOp.bvand => True
  | UserOp.bvor => True
  | UserOp.bvnand => True
  | UserOp.bvnor => True
  | UserOp.bvxor => True
  | UserOp.bvxnor => True
  | UserOp.bvcomp => True
  | UserOp.bvadd => True
  | UserOp.bvmul => True
  | UserOp.bvudiv => True
  | UserOp.bvurem => True
  | UserOp.bvsub => True
  | UserOp.bvsdiv => True
  | UserOp.bvsrem => True
  | UserOp.bvsmod => True
  | UserOp.bvult => True
  | UserOp.bvule => True
  | UserOp.bvugt => True
  | UserOp.bvuge => True
  | UserOp.bvslt => True
  | UserOp.bvsle => True
  | UserOp.bvsgt => True
  | UserOp.bvsge => True
  | UserOp.bvshl => True
  | UserOp.bvlshr => True
  | UserOp.bvashr => True
  | UserOp.bvuaddo => True
  | UserOp.bvsaddo => True
  | UserOp.bvumulo => True
  | UserOp.bvsmulo => True
  | UserOp.bvusubo => True
  | UserOp.bvssubo => True
  | UserOp.bvsdivo => True
  | UserOp.bvultbv => True
  | UserOp.bvsltbv => True
  | UserOp._at_from_bools => True
  | UserOp.str_concat => True
  | UserOp.str_contains => True
  | UserOp.str_at => True
  | UserOp.str_prefixof => True
  | UserOp.str_suffixof => True
  | UserOp.str_lt => True
  | UserOp.str_leq => True
  | UserOp.re_range => True
  | UserOp.re_concat => True
  | UserOp.re_inter => True
  | UserOp.re_union => True
  | UserOp.re_diff => True
  | UserOp.str_in_re => True
  | UserOp.seq_nth => True
  | UserOp._at_strings_deq_diff => True
  | UserOp._at_strings_stoi_result => True
  | UserOp._at_strings_itos_result => True
  | UserOp._at_strings_num_occur => True
  | UserOp._at_strings_num_occur_re => True
  | UserOp.tuple => True
  | UserOp.set_union => True
  | UserOp.set_inter => True
  | UserOp.set_minus => True
  | UserOp.set_member => True
  | UserOp.set_subset => True
  | UserOp.set_insert => True
  | UserOp._at_sets_deq_diff => True
  | UserOp.qdiv => True
  | UserOp.qdiv_total => True
  | UserOp.forall => True
  | UserOp.exists => True
  | _ => False

def applyApplyApplyUOpNeedsSpecialTranslation : UserOp -> Prop
  | UserOp.ite => True
  | UserOp.store => True
  | UserOp.bvite => True
  | UserOp.str_substr => True
  | UserOp.str_replace => True
  | UserOp.str_replace_all => True
  | UserOp.str_indexof => True
  | UserOp.str_update => True
  | UserOp.str_replace_re => True
  | UserOp.str_replace_re_all => True
  | UserOp.str_indexof_re => True
  | UserOp._at_strings_occur_index => True
  | UserOp._at_strings_occur_index_re => True
  | _ => False

def applyApplyApplyApplyUOpNeedsSpecialTranslation : UserOp -> Prop
  | UserOp._at_strings_replace_all_result => True
  | UserOp._at_strings_replace_re_all_result => True
  | _ => False

structure ApplyApplyUOpBranchExclusions (g : Term) : Prop where
  notOr : g ≠ Term.UOp UserOp.or
  notAnd : g ≠ Term.UOp UserOp.and
  notImp : g ≠ Term.UOp UserOp.imp
  notXor : g ≠ Term.UOp UserOp.xor
  notEq : g ≠ Term.UOp UserOp.eq
  notPlus : g ≠ Term.UOp UserOp.plus
  notNeg : g ≠ Term.UOp UserOp.neg
  notMult : g ≠ Term.UOp UserOp.mult
  notLt : g ≠ Term.UOp UserOp.lt
  notLeq : g ≠ Term.UOp UserOp.leq
  notGt : g ≠ Term.UOp UserOp.gt
  notGeq : g ≠ Term.UOp UserOp.geq
  notDiv : g ≠ Term.UOp UserOp.div
  notMod : g ≠ Term.UOp UserOp.mod
  notDivisible : g ≠ Term.UOp UserOp.divisible
  notDivTotal : g ≠ Term.UOp UserOp.div_total
  notModTotal : g ≠ Term.UOp UserOp.mod_total
  notSelect : g ≠ Term.UOp UserOp.select
  notArrayDeqDiff : g ≠ Term.UOp UserOp._at_array_deq_diff
  notConcat : g ≠ Term.UOp UserOp.concat
  notBvand : g ≠ Term.UOp UserOp.bvand
  notBvor : g ≠ Term.UOp UserOp.bvor
  notBvnand : g ≠ Term.UOp UserOp.bvnand
  notBvnor : g ≠ Term.UOp UserOp.bvnor
  notBvxor : g ≠ Term.UOp UserOp.bvxor
  notBvxnor : g ≠ Term.UOp UserOp.bvxnor
  notBvcomp : g ≠ Term.UOp UserOp.bvcomp
  notBvadd : g ≠ Term.UOp UserOp.bvadd
  notBvmul : g ≠ Term.UOp UserOp.bvmul
  notBvudiv : g ≠ Term.UOp UserOp.bvudiv
  notBvurem : g ≠ Term.UOp UserOp.bvurem
  notBvsub : g ≠ Term.UOp UserOp.bvsub
  notBvsdiv : g ≠ Term.UOp UserOp.bvsdiv
  notBvsrem : g ≠ Term.UOp UserOp.bvsrem
  notBvsmod : g ≠ Term.UOp UserOp.bvsmod
  notBvult : g ≠ Term.UOp UserOp.bvult
  notBvule : g ≠ Term.UOp UserOp.bvule
  notBvugt : g ≠ Term.UOp UserOp.bvugt
  notBvuge : g ≠ Term.UOp UserOp.bvuge
  notBvslt : g ≠ Term.UOp UserOp.bvslt
  notBvsle : g ≠ Term.UOp UserOp.bvsle
  notBvsgt : g ≠ Term.UOp UserOp.bvsgt
  notBvsge : g ≠ Term.UOp UserOp.bvsge
  notBvshl : g ≠ Term.UOp UserOp.bvshl
  notBvlshr : g ≠ Term.UOp UserOp.bvlshr
  notBvashr : g ≠ Term.UOp UserOp.bvashr
  notBvuaddo : g ≠ Term.UOp UserOp.bvuaddo
  notBvsaddo : g ≠ Term.UOp UserOp.bvsaddo
  notBvumulo : g ≠ Term.UOp UserOp.bvumulo
  notBvsmulo : g ≠ Term.UOp UserOp.bvsmulo
  notBvusubo : g ≠ Term.UOp UserOp.bvusubo
  notBvssubo : g ≠ Term.UOp UserOp.bvssubo
  notBvsdivo : g ≠ Term.UOp UserOp.bvsdivo
  notBvultbv : g ≠ Term.UOp UserOp.bvultbv
  notBvsltbv : g ≠ Term.UOp UserOp.bvsltbv
  notFromBools : g ≠ Term.UOp UserOp._at_from_bools
  notStrConcat : g ≠ Term.UOp UserOp.str_concat
  notStrContains : g ≠ Term.UOp UserOp.str_contains
  notStrAt : g ≠ Term.UOp UserOp.str_at
  notStrPrefixof : g ≠ Term.UOp UserOp.str_prefixof
  notStrSuffixof : g ≠ Term.UOp UserOp.str_suffixof
  notStrLt : g ≠ Term.UOp UserOp.str_lt
  notStrLeq : g ≠ Term.UOp UserOp.str_leq
  notReRange : g ≠ Term.UOp UserOp.re_range
  notReConcat : g ≠ Term.UOp UserOp.re_concat
  notReInter : g ≠ Term.UOp UserOp.re_inter
  notReUnion : g ≠ Term.UOp UserOp.re_union
  notReDiff : g ≠ Term.UOp UserOp.re_diff
  notStrInRe : g ≠ Term.UOp UserOp.str_in_re
  notSeqNth : g ≠ Term.UOp UserOp.seq_nth
  notStringsDeqDiff : g ≠ Term.UOp UserOp._at_strings_deq_diff
  notStringsStoiResult : g ≠ Term.UOp UserOp._at_strings_stoi_result
  notStringsItosResult : g ≠ Term.UOp UserOp._at_strings_itos_result
  notStringsNumOccur : g ≠ Term.UOp UserOp._at_strings_num_occur
  notStringsNumOccurRe : g ≠ Term.UOp UserOp._at_strings_num_occur_re
  notTuple : g ≠ Term.UOp UserOp.tuple
  notSetUnion : g ≠ Term.UOp UserOp.set_union
  notSetInter : g ≠ Term.UOp UserOp.set_inter
  notSetMinus : g ≠ Term.UOp UserOp.set_minus
  notSetMember : g ≠ Term.UOp UserOp.set_member
  notSetSubset : g ≠ Term.UOp UserOp.set_subset
  notSetInsert : g ≠ Term.UOp UserOp.set_insert
  notSetsDeqDiff : g ≠ Term.UOp UserOp._at_sets_deq_diff
  notQdiv : g ≠ Term.UOp UserOp.qdiv
  notQdivTotal : g ≠ Term.UOp UserOp.qdiv_total
  notForall : g ≠ Term.UOp UserOp.forall
  notExists : g ≠ Term.UOp UserOp.exists

structure ApplyApplyApplyUOpBranchExclusions (g : Term) : Prop where
  notIte : ¬ ∃ c, g = Term.Apply (Term.UOp UserOp.ite) c
  notStore : ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.store) s
  notBvite : ¬ ∃ c, g = Term.Apply (Term.UOp UserOp.bvite) c
  notStrSubstr : ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_substr) s
  notStrReplace : ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_replace) s
  notStrReplaceAll :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_replace_all) s
  notStrIndexof : ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_indexof) s
  notStrUpdate : ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_update) s
  notStrReplaceRe :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_replace_re) s
  notStrReplaceReAll :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_replace_re_all) s
  notStrIndexofRe :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp.str_indexof_re) s
  notStringsOccurIndex :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp._at_strings_occur_index) s
  notStringsOccurIndexRe :
    ¬ ∃ s, g = Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s

structure ApplyApplyApplyApplyUOpBranchExclusions (g : Term) : Prop where
  notStringsReplaceAllResult :
    ¬ ∃ s p,
      g =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) s) p
  notStringsReplaceReAllResult :
    ¬ ∃ s p,
      g =
        Term.Apply
          (Term.Apply
            (Term.UOp UserOp._at_strings_replace_re_all_result) s) p

theorem eo_to_smt_apply_apply_generic_of_not_special
    {g x a : Term}
    (hNoUOp :
      ∀ op, applyApplyUOpNeedsSpecialTranslation op -> g ≠ Term.UOp op)
    (hNoUpdate :
      ∀ idx, g ≠ Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ∀ idx, g ≠ Term.UOp1 UserOp1.tuple_update idx)
    (hNoApplyUOp :
      ∀ op y,
        applyApplyApplyUOpNeedsSpecialTranslation op ->
          g ≠ Term.Apply (Term.UOp op) y)
    (hNoApplyApplyUOp :
      ∀ op w z,
        applyApplyApplyApplyUOpNeedsSpecialTranslation op ->
          g ≠ Term.Apply (Term.Apply (Term.UOp op) w) z) :
    __eo_to_smt (Term.Apply (Term.Apply g x) a) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a) := by
  cases g <;> try rfl
  · rename_i op
    cases op <;> try rfl
    all_goals
      exact False.elim
        (hNoUOp _ (by simp [applyApplyUOpNeedsSpecialTranslation]) rfl)
  · rename_i op idx
    cases op <;> try rfl
    · exact False.elim (hNoUpdate idx rfl)
    · exact False.elim (hNoTupleUpdate idx rfl)
  · rename_i head y
    cases head <;> try rfl
    · rename_i op
      cases op <;> try rfl
      all_goals
        exact False.elim
          (hNoApplyUOp _ y
            (by simp [applyApplyApplyUOpNeedsSpecialTranslation]) rfl)
    · rename_i head' z
      cases head' <;> try rfl
      · rename_i op
        cases op <;> try rfl
        all_goals
          exact False.elim
            (hNoApplyApplyUOp _ z y
              (by
                simp [applyApplyApplyApplyUOpNeedsSpecialTranslation])
              rfl)

theorem eo_to_smt_apply_apply_generic_of_branch_exclusions
    {g x a : Term}
    (hUOp : ApplyApplyUOpBranchExclusions g)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hApplyUOp : ApplyApplyApplyUOpBranchExclusions g)
    (hApplyApplyUOp : ApplyApplyApplyApplyUOpBranchExclusions g) :
    __eo_to_smt (Term.Apply (Term.Apply g x) a) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a) := by
  exact
    eo_to_smt_apply_apply_generic_of_not_special
      (g := g) (x := x) (a := a)
      (by
        intro op hSpecial hEq
        subst g
        rcases hUOp with
          ⟨hOr, hAnd, hImp, hXor, hEqOp, hPlus, hNeg, hMult, hLt, hLeq,
            hGt, hGeq, hDiv, hMod, hDivisible, hDivTotal, hModTotal, hSelect,
            hArrayDeqDiff, hConcat,
            hBvand, hBvor, hBvnand, hBvnor, hBvxor, hBvxnor, hBvcomp,
            hBvadd, hBvmul, hBvudiv, hBvurem, hBvsub, hBvsdiv, hBvsrem,
            hBvsmod, hBvult, hBvule, hBvugt, hBvuge, hBvslt, hBvsle,
            hBvsgt, hBvsge, hBvshl, hBvlshr, hBvashr, hBvuaddo,
            hBvsaddo, hBvumulo, hBvsmulo, hBvusubo, hBvssubo, hBvsdivo,
            hBvultbv, hBvsltbv, hFromBools, hStrConcat, hStrContains,
            hStrAt, hStrPrefixof, hStrSuffixof, hStrLt, hStrLeq, hReRange,
            hReConcat, hReInter, hReUnion, hReDiff, hStrInRe, hSeqNth,
            hStringsDeqDiff, hStringsStoiResult, hStringsItosResult,
            hStringsNumOccur, hStringsNumOccurRe, hTuple, hSetUnion,
            hSetInter, hSetMinus, hSetMember, hSetSubset, hSetInsert,
            hSetsDeqDiff, hQdiv, hQdivTotal, hForall, hExists⟩
        cases op <;>
          simp [applyApplyUOpNeedsSpecialTranslation] at hSpecial <;>
          contradiction)
      (fun idx hEq => hNoUpdate ⟨idx, hEq⟩)
      (fun idx hEq => hNoTupleUpdate ⟨idx, hEq⟩)
      (by
        intro op y hSpecial hEq
        subst g
        cases op <;>
          simp [applyApplyApplyUOpNeedsSpecialTranslation] at hSpecial
        all_goals
          first
          | exact hApplyUOp.notIte ⟨y, rfl⟩
          | exact hApplyUOp.notStore ⟨y, rfl⟩
          | exact hApplyUOp.notBvite ⟨y, rfl⟩
          | exact hApplyUOp.notStrSubstr ⟨y, rfl⟩
          | exact hApplyUOp.notStrReplace ⟨y, rfl⟩
          | exact hApplyUOp.notStrReplaceAll ⟨y, rfl⟩
          | exact hApplyUOp.notStrIndexof ⟨y, rfl⟩
          | exact hApplyUOp.notStrUpdate ⟨y, rfl⟩
          | exact hApplyUOp.notStrReplaceRe ⟨y, rfl⟩
          | exact hApplyUOp.notStrReplaceReAll ⟨y, rfl⟩
          | exact hApplyUOp.notStrIndexofRe ⟨y, rfl⟩
          | exact hApplyUOp.notStringsOccurIndex ⟨y, rfl⟩
          | exact hApplyUOp.notStringsOccurIndexRe ⟨y, rfl⟩
          | contradiction)
      (by
        intro op w z hSpecial hEq
        subst g
        cases op <;>
          simp [applyApplyApplyApplyUOpNeedsSpecialTranslation] at hSpecial
        all_goals
          first
          | exact hApplyApplyUOp.notStringsReplaceAllResult ⟨w, z, rfl⟩
          | exact
              hApplyApplyUOp.notStringsReplaceReAllResult ⟨w, z, rfl⟩
          | contradiction)

end SubstitutePreservationSupport
