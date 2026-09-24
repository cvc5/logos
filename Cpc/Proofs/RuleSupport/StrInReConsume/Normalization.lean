module

public import Cpc.Proofs.RuleSupport.StrInReConsume.Reverse
import all Cpc.Proofs.RuleSupport.StrInReConsume.Reverse

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

/--
`{ε}`-valued `str.to_re` chunk arguments: the empty string literal and
`seq.empty` atoms.  These are the chunk arguments the re-flattening
pass DROPS (their chunk value is the neutral `{ε}`).
-/
def StrInReConsumeInternal.consume_chunk_eps_valued_local (x : Term) : Prop :=
  x = Term.String [] ∨ ∃ U : Term, x = Term.UOp1 UserOp1.seq_empty U

/--
Reproduction behavior of a `str.to_re` chunk argument under
re-flattening: splitting the re-flattened singleton list either
reproduces the chunk exactly, drops it (in which case it is
`{ε}`-valued), or the inner string flatten is stuck (in which case the
enclosing flatten is stuck and any evaluation hypothesis is vacuous).
-/
def StrInReConsumeInternal.consume_chunk_reprod_local (x : Term) : Prop :=
  (∀ X : Term,
      __re_split_str_to_re
          (__str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) x))
          X =
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) x)) X) ∨
  ((∀ X : Term,
      __re_split_str_to_re
          (__str_flatten
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) x))
          X =
        X) ∧
    StrInReConsumeInternal.consume_chunk_eps_valued_local x) ∨
  __str_flatten
      (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) x) =
    Term.Stuck

/--
Invariant of the reversal images of `__re_flatten true` outputs, the
regexes the second consume pass re-flattens.  Flags as in
`StrInReConsumeInternal.consume_wf_local`: 3 = chain (eps-terminated `re.++` spine),
0 = chunk, 1/2 = `re.inter`/`re.union` tails.  Chunk conditions:
`str.to_re` arguments reproduce (or drop/stick) under re-flattening,
`re.*` bodies and `re.inter`/`re.union` left components are again
rev-image chains, and no chunk is itself a raw `re.++` (the flatten
splice guarantees this).  All other chunk shapes are `__re_flatten
false`-fixed by that function's catch-all, hence unconstrained.
-/
def StrInReConsumeInternal.consume_rev_flat_local : Nat -> Term -> Prop
  | 3, Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) => True
  | 3, Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =>
      StrInReConsumeInternal.consume_rev_flat_local 0 a ∧ StrInReConsumeInternal.consume_rev_flat_local 3 b
  | 3, _ => False
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) _) _ => False
  | 0, Term.Apply (Term.UOp UserOp.str_to_re) x =>
      StrInReConsumeInternal.consume_chunk_reprod_local x
  | 0, Term.Apply (Term.UOp UserOp.re_mult) body =>
      StrInReConsumeInternal.consume_rev_flat_local 3 body
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =>
      StrInReConsumeInternal.consume_rev_flat_local 3 c1 ∧ StrInReConsumeInternal.consume_rev_flat_local 1 c2
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =>
      StrInReConsumeInternal.consume_rev_flat_local 3 c1 ∧ StrInReConsumeInternal.consume_rev_flat_local 1 c2
  | 1, Term.Apply (Term.UOp UserOp.re_mult) body =>
      StrInReConsumeInternal.consume_rev_flat_local 3 body
  | 1, Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =>
      StrInReConsumeInternal.consume_rev_flat_local 3 c1 ∧ StrInReConsumeInternal.consume_rev_flat_local 1 c2
  | 1, Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =>
      StrInReConsumeInternal.consume_rev_flat_local 3 c1 ∧ StrInReConsumeInternal.consume_rev_flat_local 1 c2
  | 2, t => StrInReConsumeInternal.consume_rev_flat_local 1 t
  | _, _ => True
termination_by flag t => (sizeOf t, flag)

abbrev StrInReConsumeInternal.consume_rev_flat_chunk_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_rev_flat_local 0 t
abbrev StrInReConsumeInternal.consume_rev_flat_inter_tail_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_rev_flat_local 1 t
abbrev StrInReConsumeInternal.consume_rev_flat_union_tail_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_rev_flat_local 1 t
abbrev StrInReConsumeInternal.consume_rev_flat_chain_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_rev_flat_local 3 t

theorem StrInReConsumeInternal.consume_rev_flat_chain_eps_local :
    StrInReConsumeInternal.consume_rev_flat_chain_local
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  simp [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local]

theorem StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local {a b : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) :
    StrInReConsumeInternal.consume_rev_flat_chunk_local a ∧ StrInReConsumeInternal.consume_rev_flat_chain_local b := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local {a b : Term}
    (h1 : StrInReConsumeInternal.consume_rev_flat_chunk_local a)
    (h2 : StrInReConsumeInternal.consume_rev_flat_chain_local b) :
    StrInReConsumeInternal.consume_rev_flat_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) := by
  simp only [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local]
  exact ⟨h1, h2⟩

theorem StrInReConsumeInternal.consume_rev_flat_chunk_str_to_re_parts_local {x : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.UOp UserOp.str_to_re) x)) :
    StrInReConsumeInternal.consume_chunk_reprod_local x := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_str_to_re_of_reprod_local {x : Term}
    (h : StrInReConsumeInternal.consume_chunk_reprod_local x) :
    StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.UOp UserOp.str_to_re) x) := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_mult_parts_local {body : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.UOp UserOp.re_mult) body)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local body := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_mult_of_chain_local {body : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chain_local body) :
    StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.UOp UserOp.re_mult) body) := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_inter_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
      StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_inter_tail_local, StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_inter_of_parts_local {c1 c2 : Term}
    (h1 : StrInReConsumeInternal.consume_rev_flat_chain_local c1)
    (h2 : StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2) :
    StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
  simp only [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_local]
  exact ⟨h1, h2⟩

theorem StrInReConsumeInternal.consume_rev_flat_chunk_union_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
      StrInReConsumeInternal.consume_rev_flat_union_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_union_tail_local, StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_chunk_union_of_parts_local {c1 c2 : Term}
    (h1 : StrInReConsumeInternal.consume_rev_flat_chain_local c1)
    (h2 : StrInReConsumeInternal.consume_rev_flat_union_tail_local c2) :
    StrInReConsumeInternal.consume_rev_flat_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
  simp only [StrInReConsumeInternal.consume_rev_flat_chunk_local, StrInReConsumeInternal.consume_rev_flat_local]
  exact ⟨h1, h2⟩

theorem StrInReConsumeInternal.consume_rev_flat_inter_tail_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_inter_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
      StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_rev_flat_inter_tail_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_union_tail_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_union_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
      StrInReConsumeInternal.consume_rev_flat_union_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_rev_flat_union_tail_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_tail_mult_parts_local {body : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_inter_tail_local
      (Term.Apply (Term.UOp UserOp.re_mult) body)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local body := by
  simpa [StrInReConsumeInternal.consume_rev_flat_inter_tail_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_rev_flat_tail_union_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_inter_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
      StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_rev_flat_inter_tail_local, StrInReConsumeInternal.consume_rev_flat_chain_local,
    StrInReConsumeInternal.consume_rev_flat_local] using h

theorem StrInReConsumeInternal.consume_eo_requires_2way_local (a b c : Term) :
    __eo_requires a b c = c ∨ __eo_requires a b c = Term.Stuck := by
  have hDef :
      __eo_requires a b c =
        native_ite (native_teq a b)
          (native_ite (native_not (native_teq a Term.Stuck)) c Term.Stuck)
          Term.Stuck := rfl
  rw [hDef]
  cases native_teq a b with
  | false => exact Or.inr rfl
  | true =>
      cases native_not (native_teq a Term.Stuck) with
      | false => exact Or.inr rfl
      | true => exact Or.inl rfl

theorem StrInReConsumeInternal.consume_eo_nil_str_concat_shape_local (T : Term) :
    __eo_nil (Term.UOp UserOp.str_concat) T = Term.Stuck ∨
      __eo_nil (Term.UOp UserOp.str_concat) T = Term.String [] ∨
      ∃ U : Term,
        __eo_nil (Term.UOp UserOp.str_concat) T =
          Term.UOp1 UserOp1.seq_empty U := by
  have hDisp :
      __eo_nil (Term.UOp UserOp.str_concat) T = Term.Stuck ∨
        __eo_nil (Term.UOp UserOp.str_concat) T =
          __eo_nil_str_concat T := by
    cases T <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hDisp with h | h
  · exact Or.inl h
  · rw [h, __eo_nil_str_concat.eq_def]
    split
    · rw [__seq_empty.eq_def]
      split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inl rfl

theorem StrInReConsumeInternal.consume_str_flatten_string_empty_local :
    __str_flatten (Term.String []) = Term.String [] := rfl

theorem StrInReConsumeInternal.consume_str_flatten_atom_2way_local (x : Term)
    (hNe : x ≠ Term.Stuck)
    (hNC : ∀ t tail : Term,
      x = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail →
        False) :
    __str_flatten x = x ∨ __str_flatten x = Term.Stuck := by
  have hNS : ∀ a a2 b : Term,
      x = Term.Apply
        (Term.Apply (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) a2)) b →
        False := by
    intro a a2 b h
    exact hNC _ _ h
  rw [__str_flatten.eq_4 x (fun h => hNe h) hNS hNC]
  exact StrInReConsumeInternal.consume_eo_requires_2way_local x (__seq_empty (__eo_typeof x)) x

theorem StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local (c : Term) :
    __re_split_str_to_re c Term.Stuck = Term.Stuck := by
  by_cases hc : c = Term.Stuck
  · rw [hc, __re_split_str_to_re.eq_1]
  · exact __re_split_str_to_re.eq_2 c (fun h => hc h)

theorem StrInReConsumeInternal.consume_split_str_to_re_non_concat_local (c : Term)
    (hNe : c ≠ Term.Stuck)
    (hNC : ∀ a b : Term,
      c = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b →
        False) :
    ∀ X : Term, __re_split_str_to_re c X = X := by
  intro X
  by_cases hX : X = Term.Stuck
  · rw [hX]
    exact StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local c
  · exact __re_split_str_to_re.eq_4 c X (fun h => hNe h) hNC
      (fun h => hX h)

theorem StrInReConsumeInternal.consume_is_list_str_concat_string_empty_local :
    __eo_is_list (Term.UOp UserOp.str_concat) (Term.String []) =
      Term.Boolean true := rfl

theorem StrInReConsumeInternal.consume_is_list_str_concat_seq_empty_local (U : Term) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (Term.UOp1 UserOp1.seq_empty U) =
      Term.Boolean true := rfl

theorem StrInReConsumeInternal.consume_chunk_reprod_string_single_local
    (c : native_Char) :
    StrInReConsumeInternal.consume_chunk_reprod_local (Term.String [c]) := by
  left
  intro X
  rw [StrInReConsumeInternal.str_flatten_singleton_intro_string_single_local c]
  by_cases hX : X = Term.Stuck
  · rw [hX, StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local]
    rfl
  · rw [__re_split_str_to_re.eq_3 X (Term.String [c]) (Term.String [])
      (fun h => hX h)]
    rw [StrInReConsumeInternal.consume_split_str_to_re_non_concat_local (Term.String [])
      (by intro h; cases h) (by intro a b h; cases h) X]

theorem StrInReConsumeInternal.consume_chunk_reprod_string_empty_local :
    StrInReConsumeInternal.consume_chunk_reprod_local (Term.String []) := by
  right
  left
  refine ⟨?_, Or.inl rfl⟩
  intro X
  have hSingleton :
      __eo_list_singleton_intro (Term.UOp UserOp.str_concat)
          (Term.String []) =
        Term.String [] := by
    rw [__eo_list_singleton_intro.eq_1,
      StrInReConsumeInternal.consume_is_list_str_concat_string_empty_local, eo_ite_true]
  rw [hSingleton, StrInReConsumeInternal.consume_str_flatten_string_empty_local]
  exact StrInReConsumeInternal.consume_split_str_to_re_non_concat_local (Term.String [])
    (by intro h; cases h) (by intro a b h; cases h) X

/--
Inversion of a true `is_list str.++` result on a term that is neither a
`str.++` application nor a string literal: only `seq.empty` atoms
qualify.
-/
theorem StrInReConsumeInternal.consume_is_list_true_atom_inversion_local (x : Term)
    (hNe : x ≠ Term.Stuck)
    (hNC : ∀ t tail : Term,
      x = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail →
        False)
    (hNotStr : ∀ w : native_String, x = Term.String w → False)
    (hIL : __eo_is_list (Term.UOp UserOp.str_concat) x =
      Term.Boolean true) :
    ∃ U : Term, x = Term.UOp1 UserOp1.seq_empty U := by
  rw [__eo_is_list.eq_3 (Term.UOp UserOp.str_concat) x
    (fun h => by cases h) (fun h => hNe h)] at hIL
  cases x with
  | UOp1 op U =>
      cases op with
      | seq_empty => exact ⟨U, rfl⟩
      | _ =>
          exfalso
          simp [__eo_get_nil_rec, __eo_is_list_nil,
            __eo_is_list_nil_str_concat, __eo_is_ok, __eo_requires,
            __eo_eq, native_teq, native_ite, native_not,
            SmtEval.native_not] at hIL
  | Apply f y =>
      exfalso
      cases f with
      | Apply g z =>
          by_cases hg : g = Term.UOp UserOp.str_concat
          · subst hg
            exact hNC z y rfl
          · have hGet :
                __eo_get_nil_rec (Term.UOp UserOp.str_concat)
                    (Term.Apply (Term.Apply g z) y) =
                  __eo_requires (Term.UOp UserOp.str_concat) g
                    (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) :=
              rfl
            rw [hGet] at hIL
            have hTeq : native_teq (Term.UOp UserOp.str_concat) g =
                false := by
              cases hEq : native_teq (Term.UOp UserOp.str_concat) g
              · rfl
              · have hgg : Term.UOp UserOp.str_concat = g := by
                  simpa [native_teq] using hEq
                exact absurd hgg.symm hg
            have hReqStuck :
                __eo_requires (Term.UOp UserOp.str_concat) g
                    (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) =
                  Term.Stuck := by
              have hReqDef :
                  __eo_requires (Term.UOp UserOp.str_concat) g
                      (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
                        y) =
                    native_ite
                      (native_teq (Term.UOp UserOp.str_concat) g)
                      (native_ite
                        (native_not
                          (native_teq (Term.UOp UserOp.str_concat)
                            Term.Stuck))
                        (__eo_get_nil_rec
                          (Term.UOp UserOp.str_concat) y)
                        Term.Stuck)
                      Term.Stuck := rfl
              rw [hReqDef, hTeq]
              rfl
            rw [hReqStuck] at hIL
            simp [__eo_is_ok, native_teq, native_not,
              SmtEval.native_not] at hIL
      | _ =>
          simp [__eo_get_nil_rec, __eo_is_list_nil,
            __eo_is_list_nil_str_concat, __eo_is_ok, __eo_requires,
            __eo_eq, native_teq, native_ite, native_not,
            SmtEval.native_not] at hIL
  | String w => exact absurd rfl (hNotStr w)
  | Stuck => exact absurd rfl hNe
  | _ =>
      exfalso
      simp [__eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_is_ok, __eo_requires,
        __eo_eq, native_teq, native_ite, native_not,
        SmtEval.native_not] at hIL

/--
Reproduction for kept (non-string-literal, non-list) chunk arguments.
-/
theorem StrInReConsumeInternal.consume_chunk_reprod_of_atom_local (x : Term)
    (hNe : x ≠ Term.Stuck)
    (hNC : ∀ t tail : Term,
      x = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail →
        False)
    (hNotStr : ∀ w : native_String, x = Term.String w → False) :
    StrInReConsumeInternal.consume_chunk_reprod_local x := by
  have hIsStrX : __eo_is_str x = Term.Boolean false := by
    have hInt : __eo_is_str_internal x = Term.Boolean false := by
      cases x <;>
        first
          | rfl
          | exact absurd rfl hNe
          | exact absurd rfl (hNotStr _)
    have hDef : __eo_is_str x =
        Term.Boolean
          (native_and (native_not (native_teq x Term.Stuck))
            (native_teq (__eo_is_str_internal x)
              (Term.Boolean true))) := rfl
    rw [hDef, hInt]
    cases native_not (native_teq x Term.Stuck) <;> rfl
  by_cases hIL : __eo_is_list (Term.UOp UserOp.str_concat) x =
      Term.Boolean true
  · -- proper-list atom: only seq.empty atoms qualify; chunk drops
    rcases StrInReConsumeInternal.consume_is_list_true_atom_inversion_local x hNe hNC hNotStr
      hIL with ⟨U, rfl⟩
    have hSingleton :
        __eo_list_singleton_intro (Term.UOp UserOp.str_concat)
            (Term.UOp1 UserOp1.seq_empty U) =
          Term.UOp1 UserOp1.seq_empty U := by
      rw [__eo_list_singleton_intro.eq_1, hIL, eo_ite_true]
    rcases StrInReConsumeInternal.consume_str_flatten_atom_2way_local
        (Term.UOp1 UserOp1.seq_empty U) (by intro h; cases h)
        (by intro t tail h; cases h) with hF | hF
    · right
      left
      refine ⟨?_, Or.inr ⟨U, rfl⟩⟩
      intro X
      rw [hSingleton, hF]
      exact StrInReConsumeInternal.consume_split_str_to_re_non_concat_local _
        (by intro h; cases h) (by intro a b h; cases h) X
    · right
      right
      rw [hSingleton]
      exact hF
  · -- not a proper list: singleton_intro wraps with the type's nil
    have hILB : __eo_is_list (Term.UOp UserOp.str_concat) x =
        Term.Boolean false := by
      rw [__eo_is_list.eq_3 (Term.UOp UserOp.str_concat) x
        (fun h => by cases h) (fun h => hNe h)] at hIL ⊢
      have hOk : __eo_is_ok
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) x) =
        Term.Boolean
          (native_not
            (native_teq
              (__eo_get_nil_rec (Term.UOp UserOp.str_concat) x)
              Term.Stuck)) := rfl
      rw [hOk] at hIL ⊢
      revert hIL
      cases native_not
          (native_teq (__eo_get_nil_rec (Term.UOp UserOp.str_concat) x)
            Term.Stuck) with
      | false => intro _; rfl
      | true => intro hIL; exact absurd rfl hIL
    have hIte : __eo_list_singleton_intro (Term.UOp UserOp.str_concat)
        x =
      __eo_requires
        (__eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x)))
        (Term.Boolean true)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) := by
      rw [__eo_list_singleton_intro.eq_1, hILB, eo_ite_false]
    rcases StrInReConsumeInternal.consume_eo_nil_str_concat_shape_local (__eo_typeof x) with
      hNil | hNil | ⟨U, hNil⟩
    · -- nil is stuck: everything sticks
      right
      right
      rw [hIte, hNil]
      have hReq :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
              (Term.Boolean true)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) x)
                Term.Stuck) =
            Term.Stuck := rfl
      rw [hReq]
      rfl
    · -- nil is the empty string literal
      left
      intro X
      rw [hIte, hNil]
      have hReq :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (Term.String []))
              (Term.Boolean true)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) x)
                (Term.String [])) =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.String []) := rfl
      have hMk :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.String []) =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.String []) := by
        cases x <;> first | exact absurd rfl hNe | rfl
      rw [hReq, hMk, __str_flatten.eq_3 x (Term.String []) hNC,
        hIsStrX, eo_ite_false, StrInReConsumeInternal.consume_str_flatten_string_empty_local,
        hMk]
      by_cases hX : X = Term.Stuck
      · rw [hX, StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local]
        rfl
      · rw [__re_split_str_to_re.eq_3 X x (Term.String [])
          (fun h => hX h)]
        rw [StrInReConsumeInternal.consume_split_str_to_re_non_concat_local (Term.String [])
          (by intro h; cases h) (by intro a b h; cases h) X]
    · have hReq :
          __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (Term.UOp1 UserOp1.seq_empty U))
              (Term.Boolean true)
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.str_concat) x)
                (Term.UOp1 UserOp1.seq_empty U)) =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.UOp1 UserOp1.seq_empty U) := rfl
      have hMk :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.UOp1 UserOp1.seq_empty U) =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x)
              (Term.UOp1 UserOp1.seq_empty U) := by
        cases x <;> first | exact absurd rfl hNe | rfl
      rcases StrInReConsumeInternal.consume_str_flatten_atom_2way_local
          (Term.UOp1 UserOp1.seq_empty U) (by intro h; cases h)
          (by intro t tail h; cases h) with hF | hF
      · left
        intro X
        rw [hIte, hNil, hReq, hMk,
          __str_flatten.eq_3 x (Term.UOp1 UserOp1.seq_empty U) hNC,
          hIsStrX, eo_ite_false, hF, hMk]
        by_cases hX : X = Term.Stuck
        · rw [hX, StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local]
          rfl
        · rw [__re_split_str_to_re.eq_3 X x
            (Term.UOp1 UserOp1.seq_empty U) (fun h => hX h)]
          rw [StrInReConsumeInternal.consume_split_str_to_re_non_concat_local
            (Term.UOp1 UserOp1.seq_empty U) (by intro h; cases h)
            (by intro a b h; cases h) X]
      · right
        right
        rw [hIte, hNil, hReq, hMk,
          __str_flatten.eq_3 x (Term.UOp1 UserOp1.seq_empty U) hNC,
          hIsStrX, eo_ite_false, hF]
        rfl

theorem StrInReConsumeInternal.consume_eo_requires_stuck_third_local (a b : Term) :
    __eo_requires a b Term.Stuck = Term.Stuck := by
  rcases StrInReConsumeInternal.consume_eo_requires_2way_local a b Term.Stuck with h | h <;>
    exact h

theorem StrInReConsumeInternal.consume_chunk_reprod_stuck_local :
    StrInReConsumeInternal.consume_chunk_reprod_local Term.Stuck := by
  right
  right
  rw [__eo_list_singleton_intro.eq_1]
  rfl

theorem StrInReConsumeInternal.consume_seq_empty_shape_local (X : Term) :
    __seq_empty X = Term.Stuck ∨ __seq_empty X = Term.String [] ∨
      ∃ U : Term, __seq_empty X = Term.UOp1 UserOp1.seq_empty U := by
  rw [__seq_empty.eq_def]
  split
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem StrInReConsumeInternal.consume_is_str_shape_local (t : Term) :
    __eo_is_str t = Term.Boolean true ∨
      __eo_is_str t = Term.Boolean false := by
  have hDef : __eo_is_str t =
      Term.Boolean
        (native_and (native_not (native_teq t Term.Stuck))
          (native_teq (__eo_is_str_internal t) (Term.Boolean true))) :=
    rfl
  rw [hDef]
  cases native_and (native_not (native_teq t Term.Stuck))
      (native_teq (__eo_is_str_internal t) (Term.Boolean true)) with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

theorem StrInReConsumeInternal.consume_is_str_true_string_local (t : Term)
    (h : __eo_is_str t = Term.Boolean true) :
    ∃ w : native_String, t = Term.String w := by
  cases t <;>
    first
      | exact ⟨_, rfl⟩
      | (exfalso;
          simp [__eo_is_str, __eo_is_str_internal, native_teq,
            native_and, native_not, SmtEval.native_not,
            SmtEval.native_and] at h)

theorem StrInReConsumeInternal.consume_is_str_string_true_local (w : native_String) :
    __eo_is_str (Term.String w) = Term.Boolean true := by
  simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
    native_not, SmtEval.native_not, SmtEval.native_and]

/-- Chunk lists produced by `__str_flatten`: `str.++` spines of
reproducing chunks ending in an empty-string or `seq.empty` nil. -/
def StrInReConsumeInternal.consume_parts_reprod_local : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c) rest =>
      StrInReConsumeInternal.consume_chunk_reprod_local c ∧ StrInReConsumeInternal.consume_parts_reprod_local rest
  | Term.String [] => True
  | Term.UOp1 UserOp1.seq_empty _ => True
  | _ => False

theorem StrInReConsumeInternal.consume_parts_reprod_ne_stuck_local {t : Term}
    (h : StrInReConsumeInternal.consume_parts_reprod_local t) : t ≠ Term.Stuck := by
  intro hEq
  subst hEq
  simp [StrInReConsumeInternal.consume_parts_reprod_local] at h

theorem StrInReConsumeInternal.consume_extractString_length_le_one_local
    (s : native_String) (i : native_Int) :
    (extractString s i).length ≤ 1 := by
  simp only [extractString, native_str_substr]
  split
  · simp
  · have h1 : native_zplus (native_zplus i (native_zneg i)) 1 = 1 := by
      show i + -i + 1 = 1
      exact (show ∀ x : Int, x + -x + 1 = 1 by intro x; omega) i
    rw [h1]
    refine Nat.le_trans (List.length_take_le _ _) ?_
    rw [Int.min_def]
    split
    · decide
    · rename_i hle
      exact (show ∀ x : Int, ¬(1 ≤ x) → Int.toNat x ≤ 1 by
        intro x h; omega) _ hle

theorem StrInReConsumeInternal.consume_chunk_reprod_string_le_one_local
    (w : native_String) (hLen : w.length ≤ 1) :
    StrInReConsumeInternal.consume_chunk_reprod_local (Term.String w) := by
  cases w with
  | nil => exact StrInReConsumeInternal.consume_chunk_reprod_string_empty_local
  | cons c cs =>
      cases cs with
      | nil => exact StrInReConsumeInternal.consume_chunk_reprod_string_single_local c
      | cons c2 cs2 => simp at hLen

theorem StrInReConsumeInternal.consume_parts_reprod_substrWord_local
    (s : native_String) :
    ∀ (n : Nat) (start : native_Int),
      StrInReConsumeInternal.consume_parts_reprod_local (substrWord s start n)
  | 0, _start => by simp [substrWord, StrInReConsumeInternal.consume_parts_reprod_local]
  | n + 1, start => by
      rw [show substrWord s start (n + 1) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String (extractString s start)))
            (substrWord s (start + 1) n) from rfl]
      exact ⟨StrInReConsumeInternal.consume_chunk_reprod_string_le_one_local _
          (StrInReConsumeInternal.consume_extractString_length_le_one_local s start),
        StrInReConsumeInternal.consume_parts_reprod_substrWord_local s n (start + 1)⟩

theorem StrInReConsumeInternal.consume_parts_reprod_concat_rec_local :
    ∀ a z : Term,
      StrInReConsumeInternal.consume_parts_reprod_local a ->
      StrInReConsumeInternal.consume_parts_reprod_local z ->
      StrInReConsumeInternal.consume_parts_reprod_local (__eo_list_concat_rec a z) ∨
        __eo_list_concat_rec a z = Term.Stuck := by
  intro a z
  induction a, z using __eo_list_concat_rec.induct with
  | case1 x =>
      intro hA _
      simp [StrInReConsumeInternal.consume_parts_reprod_local] at hA
  | case2 t _ =>
      intro _ hZ
      simp [StrInReConsumeInternal.consume_parts_reprod_local] at hZ
  | case3 f x y z hZNe ih =>
      intro hA hZ
      cases f with
      | UOp op =>
          cases op
          case str_concat =>
            rcases hA with ⟨hC, hRest⟩
            have hStep :
                __eo_list_concat_rec
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) x) y) z =
                  __eo_mk_apply
                    (Term.Apply (Term.UOp UserOp.str_concat) x)
                    (__eo_list_concat_rec y z) := by
              cases z <;> first | exact absurd rfl (fun h => hZNe h) | rfl
            rcases ih hRest hZ with hRec | hRec
            · have hRecNe := StrInReConsumeInternal.consume_parts_reprod_ne_stuck_local hRec
              have hApp :
                  __eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.str_concat) x)
                      (__eo_list_concat_rec y z) =
                    Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) x)
                      (__eo_list_concat_rec y z) := by
                cases hR : __eo_list_concat_rec y z <;>
                  first | exact absurd hR hRecNe | rfl
              rw [hStep, hApp]
              exact Or.inl ⟨hC, hRec⟩
            · right
              rw [hStep, hRec]
              rfl
          all_goals (exfalso; simp [StrInReConsumeInternal.consume_parts_reprod_local] at hA)
      | _ =>
          exfalso
          simp [StrInReConsumeInternal.consume_parts_reprod_local] at hA
  | case4 nil z hNilNe hZNe hNotApp =>
      intro hA hZ
      have hStep : __eo_list_concat_rec nil z = z := by
        cases nil with
        | Stuck => exact absurd rfl (fun h => hNilNe h)
        | Apply a b =>
            cases a with
            | Apply g x =>
                exact absurd rfl (fun h => hNotApp _ _ _ h)
            | _ =>
                cases z <;>
                  first | exact absurd rfl (fun h => hZNe h) | rfl
        | _ =>
            cases z <;>
              first | exact absurd rfl (fun h => hZNe h) | rfl
      rw [hStep]
      exact Or.inl hZ

theorem StrInReConsumeInternal.consume_parts_reprod_list_concat_local
    (a z : Term)
    (hA : StrInReConsumeInternal.consume_parts_reprod_local a)
    (hZ : StrInReConsumeInternal.consume_parts_reprod_local z) :
    StrInReConsumeInternal.consume_parts_reprod_local
        (__eo_list_concat (Term.UOp UserOp.str_concat) a z) ∨
      __eo_list_concat (Term.UOp UserOp.str_concat) a z =
        Term.Stuck := by
  have hDef : __eo_list_concat (Term.UOp UserOp.str_concat) a z =
      __eo_requires
        (__eo_is_list (Term.UOp UserOp.str_concat) a)
        (Term.Boolean true)
        (__eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) z)
          (Term.Boolean true)
          (__eo_list_concat_rec a z)) := rfl
  rw [hDef]
  rcases StrInReConsumeInternal.consume_eo_requires_2way_local
      (__eo_is_list (Term.UOp UserOp.str_concat) a) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) with h1 | h1
  · rw [h1]
    rcases StrInReConsumeInternal.consume_eo_requires_2way_local
        (__eo_is_list (Term.UOp UserOp.str_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z) with h2 | h2
    · rw [h2]
      exact StrInReConsumeInternal.consume_parts_reprod_concat_rec_local a z hA hZ
    · rw [h2]
      exact Or.inr rfl
  · rw [h1]
    exact Or.inr rfl

/-- FACTS-0: `__str_flatten` outputs are reproducing chunk lists. -/
theorem StrInReConsumeInternal.consume_parts_reprod_str_flatten_local :
    ∀ L : Term,
      StrInReConsumeInternal.consume_parts_reprod_local (__str_flatten L) ∨
        __str_flatten L = Term.Stuck := by
  intro L
  induction L using __str_flatten.induct with
  | case1 => exact Or.inr rfl
  | case2 a a2 b ih1 ih2 =>
      rw [__str_flatten.eq_2]
      rcases ih1 with h1 | h1
      · rcases ih2 with h2 | h2
        · exact StrInReConsumeInternal.consume_parts_reprod_list_concat_local _ _ h1 h2
        · right
          rw [h2]
          have hDef : __eo_list_concat (Term.UOp UserOp.str_concat)
              (__str_flatten
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) a) a2))
              Term.Stuck =
            __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) a) a2)))
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
                (Term.Boolean true)
                (__eo_list_concat_rec
                  (__str_flatten
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) a) a2))
                  Term.Stuck)) := rfl
          rw [hDef]
          have hInner :
              __eo_requires
                  (__eo_is_list (Term.UOp UserOp.str_concat)
                    Term.Stuck)
                  (Term.Boolean true)
                  (__eo_list_concat_rec
                    (__str_flatten
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat) a)
                        a2))
                    Term.Stuck) =
                Term.Stuck := rfl
          rw [hInner]
          exact StrInReConsumeInternal.consume_eo_requires_stuck_third_local _ _
      · right
        rw [h1]
        have hDef : __eo_list_concat (Term.UOp UserOp.str_concat)
            Term.Stuck (__str_flatten b) =
          __eo_requires
            (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
            (Term.Boolean true)
            (__eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten b))
              (Term.Boolean true)
              (__eo_list_concat_rec Term.Stuck (__str_flatten b))) :=
          rfl
        rw [hDef]
        rfl
  | case3 t tail hNC ih =>
      rcases StrInReConsumeInternal.consume_is_str_shape_local t with hStr | hStr
      · rcases StrInReConsumeInternal.consume_is_str_true_string_local t hStr with ⟨w, rfl⟩
        rw [str_flatten_concat_string_eq_local w tail]
        rcases ih with hT | hT
        · exact StrInReConsumeInternal.consume_parts_reprod_list_concat_local _ _
            (StrInReConsumeInternal.consume_parts_reprod_substrWord_local w w.length 0) hT
        · right
          rw [hT]
          have hDef : __eo_list_concat (Term.UOp UserOp.str_concat)
              (substrWord w 0 w.length) Term.Stuck =
            __eo_requires
              (__eo_is_list (Term.UOp UserOp.str_concat)
                (substrWord w 0 w.length))
              (Term.Boolean true)
              (__eo_requires
                (__eo_is_list (Term.UOp UserOp.str_concat) Term.Stuck)
                (Term.Boolean true)
                (__eo_list_concat_rec (substrWord w 0 w.length)
                  Term.Stuck)) := rfl
          rw [hDef]
          have hInner :
              __eo_requires
                  (__eo_is_list (Term.UOp UserOp.str_concat)
                    Term.Stuck)
                  (Term.Boolean true)
                  (__eo_list_concat_rec (substrWord w 0 w.length)
                    Term.Stuck) =
                Term.Stuck := rfl
          rw [hInner]
          exact StrInReConsumeInternal.consume_eo_requires_stuck_third_local _ _
      · rw [__str_flatten.eq_3 t tail hNC, hStr, eo_ite_false]
        rcases ih with hT | hT
        · have hTNe := StrInReConsumeInternal.consume_parts_reprod_ne_stuck_local hT
          have hApp :
              __eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (__str_flatten tail) =
                Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (__str_flatten tail) := by
            cases hF : __str_flatten tail <;>
              first | exact absurd hF hTNe | rfl
          rw [hApp]
          left
          refine ⟨?_, hT⟩
          by_cases hStuck : t = Term.Stuck
          · subst hStuck
            exact StrInReConsumeInternal.consume_chunk_reprod_stuck_local
          · refine StrInReConsumeInternal.consume_chunk_reprod_of_atom_local t hStuck hNC ?_
            intro w hw
            subst hw
            rw [StrInReConsumeInternal.consume_is_str_string_true_local w] at hStr
            cases hStr
        · right
          rw [hT]
          rfl
  | case4 x hStuck hNS hNC =>
      rcases StrInReConsumeInternal.consume_str_flatten_atom_2way_local x
          (fun h => hStuck h) hNC with hF | hF
      · left
        rw [hF]
        have hXNe : __str_flatten x ≠ Term.Stuck := by
          rw [hF]
          exact fun h => hStuck h
        rw [__str_flatten.eq_4 x hStuck hNS hNC] at hXNe
        have hEqT := eo_requires_eq_of_ne_stuck _ _ _ hXNe
        rcases StrInReConsumeInternal.consume_seq_empty_shape_local (__eo_typeof x) with
          hS | hS | ⟨U, hS⟩
        · exact absurd (hEqT.trans hS) (fun h => hStuck h)
        · rw [hEqT, hS]
          simp [StrInReConsumeInternal.consume_parts_reprod_local]
        · rw [hEqT, hS]
          simp [StrInReConsumeInternal.consume_parts_reprod_local]
      · right
        exact hF

theorem StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local {t : Term}
    (h : StrInReConsumeInternal.consume_rev_flat_chain_local t) : t ≠ Term.Stuck := by
  intro hEq
  subst hEq
  simp [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local] at h

/-- Transport: splitting a reproducing chunk list onto a rev-flat chain
yields a rev-flat chain (or sticks). -/
theorem StrInReConsumeInternal.consume_rev_flat_chain_split_local :
    ∀ parts tail : Term,
      StrInReConsumeInternal.consume_parts_reprod_local parts ->
      StrInReConsumeInternal.consume_rev_flat_chain_local tail ->
      StrInReConsumeInternal.consume_rev_flat_chain_local
          (__re_split_str_to_re parts tail) ∨
        __re_split_str_to_re parts tail = Term.Stuck := by
  intro parts tail
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 x =>
      intro hP _
      simp [StrInReConsumeInternal.consume_parts_reprod_local] at hP
  | case2 t _ =>
      intro _ hT
      exact absurd rfl (StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hT)
  | case3 c s tail hTailNe ih =>
      intro hP hT
      rcases hP with ⟨hC, hRest⟩
      rw [__re_split_str_to_re.eq_3 tail c s hTailNe]
      rcases ih hRest hT with hRec | hRec
      · have hRecNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRec
        have hApp :
            __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re s tail) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) c))
                (__re_split_str_to_re s tail) := by
          cases hR : __re_split_str_to_re s tail <;>
            first | exact absurd hR hRecNe | rfl
        rw [hApp]
        exact Or.inl (StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local
          (StrInReConsumeInternal.consume_rev_flat_chunk_str_to_re_of_reprod_local hC) hRec)
      · right
        rw [hRec]
        rfl
  | case4 c tail hCNe hTailNe hNotCons =>
      intro hP hT
      rw [__re_split_str_to_re.eq_4 c tail hCNe hNotCons hTailNe]
      exact Or.inl hT

theorem StrInReConsumeInternal.consume_mk_apply_stuck_right_local (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck :=
  Classical.byContradiction
    (fun hNe =>
      eo_mk_apply_arg_ne_stuck_of_ne_stuck f Term.Stuck hNe rfl)

theorem StrInReConsumeInternal.consume_rev_flat_chain_shape_local :
    ∀ t : Term, StrInReConsumeInternal.consume_rev_flat_chain_local t ->
      t = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ∨
      ∃ a b : Term,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b := by
  intro t h
  cases t with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;>
            first
              | (cases x with
                  | String w =>
                      cases w with
                      | nil => exact Or.inl rfl
                      | cons c cs =>
                          exfalso
                          simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
                            StrInReConsumeInternal.consume_rev_flat_local] at h
                  | _ =>
                      exfalso
                      simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
                        StrInReConsumeInternal.consume_rev_flat_local] at h)
              | (exfalso;
                  simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
                    StrInReConsumeInternal.consume_rev_flat_local] at h)
      | Apply g y =>
          cases g with
          | UOp op2 =>
              cases op2 <;>
                first
                  | exact Or.inr ⟨_, _, rfl⟩
                  | (exfalso;
                      simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
                        StrInReConsumeInternal.consume_rev_flat_local] at h)
          | _ =>
              exfalso
              simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
                StrInReConsumeInternal.consume_rev_flat_local] at h
      | _ =>
          exfalso
          simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
            StrInReConsumeInternal.consume_rev_flat_local] at h
  | _ =>
      exfalso
      simp [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local] at h

theorem StrInReConsumeInternal.consume_re_list_concat_stuck_left_local (z : Term) :
    __eo_list_concat (Term.UOp UserOp.re_concat) Term.Stuck z =
      Term.Stuck := rfl

theorem StrInReConsumeInternal.consume_re_list_concat_stuck_right_local (a : Term) :
    __eo_list_concat (Term.UOp UserOp.re_concat) a Term.Stuck =
      Term.Stuck := by
  have hDef : __eo_list_concat (Term.UOp UserOp.re_concat) a
      Term.Stuck =
    __eo_requires
      (__eo_is_list (Term.UOp UserOp.re_concat) a)
      (Term.Boolean true)
      (__eo_requires
        (__eo_is_list (Term.UOp UserOp.re_concat) Term.Stuck)
        (Term.Boolean true)
        (__eo_list_concat_rec a Term.Stuck)) := rfl
  have hInner :
      __eo_requires
          (__eo_is_list (Term.UOp UserOp.re_concat) Term.Stuck)
          (Term.Boolean true)
          (__eo_list_concat_rec a Term.Stuck) = Term.Stuck := rfl
  rw [hDef, hInner]
  exact StrInReConsumeInternal.consume_eo_requires_stuck_third_local _ _

theorem StrInReConsumeInternal.consume_rev_flat_chain_concat_rec_local :
    ∀ a z : Term,
      StrInReConsumeInternal.consume_rev_flat_chain_local a ->
      StrInReConsumeInternal.consume_rev_flat_chain_local z ->
      StrInReConsumeInternal.consume_rev_flat_chain_local (__eo_list_concat_rec a z) ∨
        __eo_list_concat_rec a z = Term.Stuck := by
  intro a z
  induction a, z using __eo_list_concat_rec.induct with
  | case1 x =>
      intro hA _
      exact absurd rfl (StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hA)
  | case2 t _ =>
      intro _ hZ
      exact absurd rfl (StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hZ)
  | case3 f x y z hZNe ih =>
      intro hA hZ
      cases f with
      | UOp op =>
          cases op
          case re_concat =>
            have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hA
            have hStep :
                __eo_list_concat_rec
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat) x) y) z =
                  __eo_mk_apply
                    (Term.Apply (Term.UOp UserOp.re_concat) x)
                    (__eo_list_concat_rec y z) := by
              cases z <;>
                first | exact absurd rfl (fun h => hZNe h) | rfl
            rcases ih hParts.2 hZ with hRec | hRec
            · have hRecNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRec
              have hApp :
                  __eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.re_concat) x)
                      (__eo_list_concat_rec y z) =
                    Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat) x)
                      (__eo_list_concat_rec y z) := by
                cases hR : __eo_list_concat_rec y z <;>
                  first | exact absurd hR hRecNe | rfl
              rw [hStep, hApp]
              exact Or.inl
                (StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local hParts.1 hRec)
            · right
              rw [hStep, hRec]
              exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
          all_goals (
            exfalso;
            simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
              StrInReConsumeInternal.consume_rev_flat_local] at hA)
      | _ =>
          exfalso
          simp [StrInReConsumeInternal.consume_rev_flat_chain_local,
            StrInReConsumeInternal.consume_rev_flat_local] at hA
  | case4 nil z hNilNe hZNe hNotApp =>
      intro hA hZ
      rcases StrInReConsumeInternal.consume_rev_flat_chain_shape_local _ hA with hEps | ⟨a', b', hC⟩
      · subst hEps
        have hStep : __eo_list_concat_rec
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
            z = z := by
          cases z <;>
            first | exact absurd rfl (fun h => hZNe h) | rfl
        rw [hStep]
        exact Or.inl hZ
      · exact absurd hC (fun h => hNotApp _ _ _ h)

theorem StrInReConsumeInternal.consume_rev_flat_chain_list_concat_local
    (a z : Term)
    (hA : StrInReConsumeInternal.consume_rev_flat_chain_local a)
    (hZ : StrInReConsumeInternal.consume_rev_flat_chain_local z) :
    StrInReConsumeInternal.consume_rev_flat_chain_local
        (__eo_list_concat (Term.UOp UserOp.re_concat) a z) ∨
      __eo_list_concat (Term.UOp UserOp.re_concat) a z =
        Term.Stuck := by
  have hDef : __eo_list_concat (Term.UOp UserOp.re_concat) a z =
      __eo_requires
        (__eo_is_list (Term.UOp UserOp.re_concat) a)
        (Term.Boolean true)
        (__eo_requires
          (__eo_is_list (Term.UOp UserOp.re_concat) z)
          (Term.Boolean true)
          (__eo_list_concat_rec a z)) := rfl
  rw [hDef]
  rcases StrInReConsumeInternal.consume_eo_requires_2way_local
      (__eo_is_list (Term.UOp UserOp.re_concat) a) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.re_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z)) with h1 | h1
  · rw [h1]
    rcases StrInReConsumeInternal.consume_eo_requires_2way_local
        (__eo_is_list (Term.UOp UserOp.re_concat) z)
        (Term.Boolean true) (__eo_list_concat_rec a z) with h2 | h2
    · rw [h2]
      exact StrInReConsumeInternal.consume_rev_flat_chain_concat_rec_local a z hA hZ
    · rw [h2]
      exact Or.inr rfl
  · rw [h1]
    exact Or.inr rfl

/--
FACTS-1: `__re_flatten` outputs satisfy the rev-flat invariant — the
true mode produces invariant chains, the false mode invariant chunks
(on non-`re.++`, non-`str.to_re` inputs) and tail chunks.
-/
theorem StrInReConsumeInternal.consume_rev_flat_flatten_facts_local :
    ∀ mode r,
      (mode = Term.Boolean true ->
        (StrInReConsumeInternal.consume_rev_flat_chain_local (__re_flatten mode r) ∨
          __re_flatten mode r = Term.Stuck)) ∧
      (mode = Term.Boolean false ->
        ((∀ a b,
            r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              b -> False) ->
          (∀ s, r = Term.Apply (Term.UOp UserOp.str_to_re) s ->
            False) ->
          (StrInReConsumeInternal.consume_rev_flat_chunk_local (__re_flatten mode r) ∨
            __re_flatten mode r = Term.Stuck)) ∧
        (StrInReConsumeInternal.consume_rev_flat_inter_tail_local (__re_flatten mode r) ∨
          __re_flatten mode r = Term.Stuck)) := by
  intro mode r
  induction mode, r using __re_flatten.induct with
  | case1 x =>
      have hRed : __re_flatten x Term.Stuck = Term.Stuck := by
        simp [__re_flatten]
      rw [hRed]
      exact ⟨fun _ => Or.inr rfl,
        fun _ => ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩⟩
  | case2 =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
            Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
          simp [__re_flatten]
        rw [hRed]
        exact Or.inl StrInReConsumeInternal.consume_rev_flat_chain_eps_local
      · intro hMode
        simp at hMode
  | case3 s b ih =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s)) b) =
            __re_split_str_to_re
              (__str_flatten
                (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
                  s))
              (__re_flatten (Term.Boolean true) b) := by
          simp [__re_flatten]
        rw [hRed]
        rcases StrInReConsumeInternal.consume_parts_reprod_str_flatten_local
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)
          with hP | hP
        · rcases ih.1 rfl with hB | hB
          · exact StrInReConsumeInternal.consume_rev_flat_chain_split_local _ _ hP hB
          · right
            rw [hB]
            exact StrInReConsumeInternal.consume_split_str_to_re_stuck_right_local _
        · right
          rw [hP, __re_split_str_to_re.eq_1]
      · intro hMode
        simp at hMode
  | case4 a1 a2 b ih1 ih2 =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) a1) a2)) b) =
            __eo_list_concat (Term.UOp UserOp.re_concat)
              (__re_flatten (Term.Boolean true)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
              (__re_flatten (Term.Boolean true) b) := by
          simp [__re_flatten]
        rw [hRed]
        rcases ih1.1 rfl with h1 | h1
        · rcases ih2.1 rfl with h2 | h2
          · exact StrInReConsumeInternal.consume_rev_flat_chain_list_concat_local _ _ h1 h2
          · right
            rw [h2]
            exact StrInReConsumeInternal.consume_re_list_concat_stuck_right_local _
        · right
          rw [h1]
          exact StrInReConsumeInternal.consume_re_list_concat_stuck_left_local _
      · intro hMode
        simp at hMode
  | case5 a b hNotStr hNotNested ihA ihB =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean false) a))
              (__re_flatten (Term.Boolean true) b) := by
          simp [__re_flatten]
        rw [hRed]
        rcases (ihA.2 rfl).1 (fun x y h => hNotNested x y h)
            (fun s h => hNotStr s h) with hChunk | hAStuck
        · by_cases hFAS : __re_flatten (Term.Boolean false) a =
              Term.Stuck
          · right
            rw [hFAS]
            rfl
          · rcases ihB.1 rfl with hChain | hBStuck
            · have hBNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hChain
              have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean false) a)
                (__re_flatten (Term.Boolean true) b)
                (by intro h; cases h) hFAS hBNe
              rw [hShape]
              exact Or.inl
                (StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local hChunk hChain)
            · right
              rw [hBStuck]
              exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
        · right
          rw [hAStuck]
          rfl
      · intro hMode
        simp at hMode
  | case6 s hNotEmpty =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply (Term.UOp UserOp.str_to_re) s) =
            __re_split_str_to_re
              (__str_flatten
                (__eo_list_singleton_intro (Term.UOp UserOp.str_concat)
                  s))
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) := by
          simp [__re_flatten]
        rw [hRed]
        rcases StrInReConsumeInternal.consume_parts_reprod_str_flatten_local
            (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)
          with hP | hP
        · exact StrInReConsumeInternal.consume_rev_flat_chain_split_local _ _ hP
            StrInReConsumeInternal.consume_rev_flat_chain_eps_local
        · right
          rw [hP, __re_split_str_to_re.eq_1]
      · intro hMode
        simp at hMode
  | case7 c hCNe hEmpty hConcatStr hNested hConcat hStr ih =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true) c =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean false) c))
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) := by
          simp [__re_flatten]
        rw [hRed]
        rcases (ih.2 rfl).1 (fun a b h => hConcat a b h)
            (fun s h => hStr s h) with hChunk | hStuck
        · by_cases hFS : __re_flatten (Term.Boolean false) c =
              Term.Stuck
          · right
            rw [hFS]
            rfl
          · have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
              (Term.UOp UserOp.re_concat)
              (__re_flatten (Term.Boolean false) c)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
              (by intro h; cases h) hFS (by intro h; cases h)
            rw [hShape]
            exact Or.inl (StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local hChunk
              StrInReConsumeInternal.consume_rev_flat_chain_eps_local)
        · right
          rw [hStuck]
          rfl
      · intro hMode
        simp at hMode
  | case8 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        constructor
        · intro _ _
          exact Or.inl (by
            simp [__re_flatten, StrInReConsumeInternal.consume_rev_flat_chunk_local,
              StrInReConsumeInternal.consume_rev_flat_local])
        · exact Or.inl (by
            simp [__re_flatten, StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
              StrInReConsumeInternal.consume_rev_flat_local])
  | case9 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        constructor
        · intro _ _
          exact Or.inl (by
            simp [__re_flatten, StrInReConsumeInternal.consume_rev_flat_chunk_local,
              StrInReConsumeInternal.consume_rev_flat_local])
        · exact Or.inl (by
            simp [__re_flatten, StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
              StrInReConsumeInternal.consume_rev_flat_local])
  | case10 body ih =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.UOp UserOp.re_mult) body) =
            __eo_mk_apply (Term.UOp UserOp.re_mult)
              (__re_flatten (Term.Boolean true) body) := by
          simp [__re_flatten]
        rw [hRed]
        rcases ih.1 rfl with hChain | hStuck
        · have hBNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hChain
          have hApp : __eo_mk_apply (Term.UOp UserOp.re_mult)
              (__re_flatten (Term.Boolean true) body) =
            Term.Apply (Term.UOp UserOp.re_mult)
              (__re_flatten (Term.Boolean true) body) := by
            cases hB : __re_flatten (Term.Boolean true) body <;>
              first | exact absurd hB hBNe | rfl
          rw [hApp]
          constructor
          · intro _ _
            exact Or.inl
              (StrInReConsumeInternal.consume_rev_flat_chunk_mult_of_chain_local hChain)
          · exact Or.inl (by
              simpa [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                StrInReConsumeInternal.consume_rev_flat_local] using hChain)
        · rw [hStuck, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
          exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
  | case11 c1 c2 ih1 ih2 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
              c2) =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter)
                (__re_flatten (Term.Boolean true) c1))
              (__re_flatten (Term.Boolean false) c2) := by
          simp [__re_flatten]
        rw [hRed]
        rcases ih1.1 rfl with hChain | hStuck
        · rcases (ih2.2 rfl).2 with hTail | hTStuck
          · by_cases hFS : __re_flatten (Term.Boolean false) c2 =
                Term.Stuck
            · rw [hFS, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
              exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
            · have hC1Ne :=
                StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hChain
              have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                (Term.UOp UserOp.re_inter)
                (__re_flatten (Term.Boolean true) c1)
                (__re_flatten (Term.Boolean false) c2)
                (by intro h; cases h) hC1Ne hFS
              rw [hShape]
              constructor
              · intro _ _
                exact Or.inl
                  (StrInReConsumeInternal.consume_rev_flat_chunk_inter_of_parts_local hChain
                    hTail)
              · exact Or.inl (by
                  simp only [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                    StrInReConsumeInternal.consume_rev_flat_local]
                  exact ⟨hChain, hTail⟩)
          · rw [hTStuck, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
            exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
        · rw [hStuck]
          have hInnerStuck :
              __eo_mk_apply (Term.UOp UserOp.re_inter) Term.Stuck =
                Term.Stuck := rfl
          rw [hInnerStuck]
          exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
  | case12 c1 c2 ih1 ih2 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
              c2) =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union)
                (__re_flatten (Term.Boolean true) c1))
              (__re_flatten (Term.Boolean false) c2) := by
          simp [__re_flatten]
        rw [hRed]
        rcases ih1.1 rfl with hChain | hStuck
        · rcases (ih2.2 rfl).2 with hTail | hTStuck
          · by_cases hFS : __re_flatten (Term.Boolean false) c2 =
                Term.Stuck
            · rw [hFS, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
              exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
            · have hC1Ne :=
                StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hChain
              have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                (Term.UOp UserOp.re_union)
                (__re_flatten (Term.Boolean true) c1)
                (__re_flatten (Term.Boolean false) c2)
                (by intro h; cases h) hC1Ne hFS
              rw [hShape]
              constructor
              · intro _ _
                exact Or.inl
                  (StrInReConsumeInternal.consume_rev_flat_chunk_union_of_parts_local hChain
                    hTail)
              · exact Or.inl (by
                  simp only [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                    StrInReConsumeInternal.consume_rev_flat_local]
                  exact ⟨hChain, hTail⟩)
          · rw [hTStuck, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
            exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
        · rw [hStuck]
          have hInnerStuck :
              __eo_mk_apply (Term.UOp UserOp.re_union) Term.Stuck =
                Term.Stuck := rfl
          rw [hInnerStuck]
          exact ⟨fun _ _ => Or.inr rfl, Or.inr rfl⟩
  | case13 c hCNe hAll hNone hMult hInter hUnion =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hEq : __re_flatten (Term.Boolean false) c = c := by
          cases c
          case Stuck => exact absurd rfl (fun h => hCNe h)
          case UOp op => cases op <;> simp [__re_flatten]
          case Apply f x =>
            cases f
            case UOp op =>
              cases op <;>
                first
                  | exact ((hMult _ rfl).elim)
                  | simp [__re_flatten]
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hInter _ _ rfl).elim)
                    | exact ((hUnion _ _ rfl).elim)
                    | simp [__re_flatten]
              all_goals simp [__re_flatten]
            all_goals simp [__re_flatten]
          all_goals simp [__re_flatten]
        rw [hEq]
        constructor
        · intro hNotConcat hNotStr
          refine Or.inl ?_
          cases c
          case Apply f x =>
            cases f
            case UOp op =>
              cases op <;>
                first
                  | exact ((hMult _ rfl).elim)
                  | exact ((hNotStr _ rfl).elim)
                  | simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
                      StrInReConsumeInternal.consume_rev_flat_local]
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hNotConcat _ _ rfl).elim)
                    | exact ((hInter _ _ rfl).elim)
                    | exact ((hUnion _ _ rfl).elim)
                    | simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
                        StrInReConsumeInternal.consume_rev_flat_local]
              all_goals simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
                StrInReConsumeInternal.consume_rev_flat_local]
            all_goals simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
              StrInReConsumeInternal.consume_rev_flat_local]
          all_goals simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
            StrInReConsumeInternal.consume_rev_flat_local]
        · refine Or.inl ?_
          cases c
          case Apply f x =>
            cases f
            case UOp op =>
              cases op <;>
                first
                  | exact ((hMult _ rfl).elim)
                  | simp [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                      StrInReConsumeInternal.consume_rev_flat_local]
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hInter _ _ rfl).elim)
                    | exact ((hUnion _ _ rfl).elim)
                    | simp [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                        StrInReConsumeInternal.consume_rev_flat_local]
              all_goals simp [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
                StrInReConsumeInternal.consume_rev_flat_local]
            all_goals simp [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
              StrInReConsumeInternal.consume_rev_flat_local]
          all_goals simp [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
            StrInReConsumeInternal.consume_rev_flat_local]
  | case14 x x_1 hTreeNe hEmpty hConcatStr hNested hConcat hStr hTrue
      hAll hNone hMult hInter hUnion hFalse =>
      constructor
      · intro hMode
        exact absurd hMode (fun h => hTrue h)
      · intro hMode
        exact absurd hMode (fun h => hFalse h)

def StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local
    (t acc : Term) : Prop :=
  StrInReConsumeInternal.consume_rev_flat_chain_local t ->
  StrInReConsumeInternal.consume_rev_flat_chain_local acc ->
  (StrInReConsumeInternal.consume_rev_flat_chain_local (__re_rev_map_rev t acc) ∨
    __re_rev_map_rev t acc = Term.Stuck)

def StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local (c : Term) : Prop :=
  (StrInReConsumeInternal.consume_rev_flat_chunk_local c ->
    (StrInReConsumeInternal.consume_rev_flat_chunk_local (__re_rev_comp c) ∨
      __re_rev_comp c = Term.Stuck)) ∧
  (StrInReConsumeInternal.consume_rev_flat_inter_tail_local c ->
    (StrInReConsumeInternal.consume_rev_flat_inter_tail_local (__re_rev_comp c) ∨
      __re_rev_comp c = Term.Stuck))

/--
The rev-flat invariant is preserved by `__re_rev_map_rev` /
`__re_rev_comp` (or the reversal sticks).
-/
theorem StrInReConsumeInternal.consume_rev_flat_rev_facts_local :
    (∀ t acc, StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local t acc) ∧
      (∀ c, StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local c) := by
  have case1 : ∀ t, StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local t
      Term.Stuck := by
    intro t _ hAcc
    exact absurd rfl (StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hAcc)
  have case2 : ∀ acc, (acc = Term.Stuck -> False) ->
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) acc := by
    intro acc hAccNe _ hAcc
    rw [__re_rev_map_rev.eq_2 acc hAccNe]
    exact Or.inl hAcc
  have case3 : ∀ a b acc, (acc = Term.Stuck -> False) ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local a ->
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local b
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat) (__re_rev_comp a))
          acc) ->
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
        acc := by
    intro a b acc hAccNe ihComp ihTail hChain hAcc
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    rw [__re_rev_map_rev.eq_3 acc a b hAccNe]
    by_cases hCS : __re_rev_comp a = Term.Stuck
    · right
      have hAccStuck :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_rev_comp a)) acc = Term.Stuck := by
        rw [hCS]
        rfl
      rw [hAccStuck, __re_rev_map_rev.eq_1]
    · rcases ihComp.1 hParts.1 with hChunk | hCS2
      · have hAccNe' : acc ≠ Term.Stuck := fun h => hAccNe h
        have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
          (Term.UOp UserOp.re_concat) (__re_rev_comp a) acc
          (by intro h; cases h) hCS hAccNe'
        rw [hShape] at ihTail ⊢
        exact ihTail hParts.2
          (StrInReConsumeInternal.consume_rev_flat_chain_of_parts_local hChunk hAcc)
      · exact absurd hCS2 hCS
  have case4 : ∀ t x, (x = Term.Stuck -> False) ->
      (t = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
        False) ->
      (∀ a b,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False) ->
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local t x := by
    intro t x _hXNe hNotEps hNotConcat hChain _
    rcases StrInReConsumeInternal.consume_rev_flat_chain_shape_local t hChain with
      hEps | ⟨a, b, hC⟩
    · exact absurd hEps (fun h => hNotEps h)
    · exact absurd hC (fun h => hNotConcat _ _ h)
  have case5 : StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local Term.Stuck :=
    ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩
  have case6 :
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local (Term.UOp UserOp.re_all) :=
    ⟨fun h => Or.inl h, fun h => Or.inl h⟩
  have case7 :
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
        (Term.UOp UserOp.re_none) :=
    ⟨fun h => Or.inl h, fun h => Or.inl h⟩
  have case8 : ∀ body,
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local body
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
        (Term.Apply (Term.UOp UserOp.re_mult) body) := by
    intro body ihBody
    have hRed : __re_rev_comp
        (Term.Apply (Term.UOp UserOp.re_mult) body) =
      __eo_mk_apply (Term.UOp UserOp.re_mult)
        (__re_rev_map_rev body
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) := by
      simp [__re_rev_comp]
    constructor
    · intro hChunk
      have hBody := StrInReConsumeInternal.consume_rev_flat_chunk_mult_parts_local hChunk
      rw [hRed]
      rcases ihBody hBody StrInReConsumeInternal.consume_rev_flat_chain_eps_local with
        hRev | hRevS
      · have hRevNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRev
        have hApp : __eo_mk_apply (Term.UOp UserOp.re_mult)
            (__re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) =
          Term.Apply (Term.UOp UserOp.re_mult)
            (__re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) := by
          cases hB : __re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) <;>
            first | exact absurd hB hRevNe | rfl
        rw [hApp]
        exact Or.inl (StrInReConsumeInternal.consume_rev_flat_chunk_mult_of_chain_local hRev)
      · right
        rw [hRevS]
        exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
    · intro hTail
      have hBody := StrInReConsumeInternal.consume_rev_flat_tail_mult_parts_local hTail
      rw [hRed]
      rcases ihBody hBody StrInReConsumeInternal.consume_rev_flat_chain_eps_local with
        hRev | hRevS
      · have hRevNe := StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRev
        have hApp : __eo_mk_apply (Term.UOp UserOp.re_mult)
            (__re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) =
          Term.Apply (Term.UOp UserOp.re_mult)
            (__re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) := by
          cases hB : __re_rev_map_rev body
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) <;>
            first | exact absurd hB hRevNe | rfl
        rw [hApp]
        exact Or.inl (by
          simpa [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
            StrInReConsumeInternal.consume_rev_flat_local] using hRev)
      · right
        rw [hRevS]
        exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
  have case9 : ∀ c1 c2,
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local c2 ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
    intro c1 c2 ihC1 ihC2
    have hRed : __re_rev_comp
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) =
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_inter)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) := by
      simp [__re_rev_comp]
    have hCore : ∀ hChain : StrInReConsumeInternal.consume_rev_flat_chain_local c1,
        ∀ hTailC2 : StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2,
        (StrInReConsumeInternal.consume_rev_flat_chain_local
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) ∧
          StrInReConsumeInternal.consume_rev_flat_inter_tail_local (__re_rev_comp c2) ∧
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter)
                (__re_rev_map_rev c1
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))))
              (__re_rev_comp c2) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (__re_rev_map_rev c1
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))))
              (__re_rev_comp c2)) ∨
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_inter)
              (__re_rev_map_rev c1
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String []))))
            (__re_rev_comp c2) =
          Term.Stuck := by
      intro hChain hTailC2
      rcases ihC1 hChain StrInReConsumeInternal.consume_rev_flat_chain_eps_local with
        hRev1 | hS1
      · by_cases hCS : __re_rev_comp c2 = Term.Stuck
        · right
          rw [hCS]
          exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
        · rcases ihC2.2 hTailC2 with hTail2 | hS2
          · have hRev1Ne :=
              StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRev1
            have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
              (Term.UOp UserOp.re_inter)
              (__re_rev_map_rev c1
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))
              (__re_rev_comp c2)
              (by intro h; cases h) hRev1Ne hCS
            exact Or.inl ⟨hRev1, hTail2, hShape⟩
          · exact absurd hS2 hCS
      · right
        rw [hS1]
        rfl
    constructor
    · intro hChunk
      have hParts := StrInReConsumeInternal.consume_rev_flat_chunk_inter_parts_local hChunk
      rw [hRed]
      rcases hCore hParts.1 hParts.2 with
        ⟨hRev1, hTail2, hShape⟩ | hStuck
      · rw [hShape]
        exact Or.inl
          (StrInReConsumeInternal.consume_rev_flat_chunk_inter_of_parts_local hRev1 hTail2)
      · right
        exact hStuck
    · intro hTail
      have hParts := StrInReConsumeInternal.consume_rev_flat_inter_tail_parts_local hTail
      rw [hRed]
      rcases hCore hParts.1 hParts.2 with
        ⟨hRev1, hTail2, hShape⟩ | hStuck
      · rw [hShape]
        exact Or.inl (by
          simp only [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
            StrInReConsumeInternal.consume_rev_flat_local]
          exact ⟨hRev1, hTail2⟩)
      · right
        exact hStuck
  have case10 : ∀ c1 c2,
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local c2 ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
    intro c1 c2 ihC1 ihC2
    have hRed : __re_rev_comp
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) =
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_union)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) := by
      simp [__re_rev_comp]
    have hCore : ∀ hChain : StrInReConsumeInternal.consume_rev_flat_chain_local c1,
        ∀ hTailC2 : StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2,
        (StrInReConsumeInternal.consume_rev_flat_chain_local
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) ∧
          StrInReConsumeInternal.consume_rev_flat_inter_tail_local (__re_rev_comp c2) ∧
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union)
                (__re_rev_map_rev c1
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))))
              (__re_rev_comp c2) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (__re_rev_map_rev c1
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))))
              (__re_rev_comp c2)) ∨
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.re_union)
              (__re_rev_map_rev c1
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String []))))
            (__re_rev_comp c2) =
          Term.Stuck := by
      intro hChain hTailC2
      rcases ihC1 hChain StrInReConsumeInternal.consume_rev_flat_chain_eps_local with
        hRev1 | hS1
      · by_cases hCS : __re_rev_comp c2 = Term.Stuck
        · right
          rw [hCS]
          exact StrInReConsumeInternal.consume_mk_apply_stuck_right_local _
        · rcases ihC2.2 hTailC2 with hTail2 | hS2
          · have hRev1Ne :=
              StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hRev1
            have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
              (Term.UOp UserOp.re_union)
              (__re_rev_map_rev c1
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))
              (__re_rev_comp c2)
              (by intro h; cases h) hRev1Ne hCS
            exact Or.inl ⟨hRev1, hTail2, hShape⟩
          · exact absurd hS2 hCS
      · right
        rw [hS1]
        rfl
    constructor
    · intro hChunk
      have hParts := StrInReConsumeInternal.consume_rev_flat_chunk_union_parts_local hChunk
      rw [hRed]
      rcases hCore hParts.1 hParts.2 with
        ⟨hRev1, hTail2, hShape⟩ | hStuck
      · rw [hShape]
        exact Or.inl
          (StrInReConsumeInternal.consume_rev_flat_chunk_union_of_parts_local hRev1 hTail2)
      · right
        exact hStuck
    · intro hTail
      have hParts := StrInReConsumeInternal.consume_rev_flat_tail_union_parts_local hTail
      rw [hRed]
      rcases hCore hParts.1 hParts.2 with
        ⟨hRev1, hTail2, hShape⟩ | hStuck
      · rw [hShape]
        exact Or.inl (by
          simp only [StrInReConsumeInternal.consume_rev_flat_inter_tail_local,
            StrInReConsumeInternal.consume_rev_flat_local]
          exact ⟨hRev1, hTail2⟩)
      · right
        exact hStuck
  have case11 : ∀ c, (c = Term.Stuck -> False) ->
      (c = Term.UOp UserOp.re_all -> False) ->
      (c = Term.UOp UserOp.re_none -> False) ->
      (∀ body, c = Term.Apply (Term.UOp UserOp.re_mult) body -> False) ->
      (∀ c1 c2,
        c = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
          False) ->
      (∀ c1 c2,
        c = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
          False) ->
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local c := by
    intro c hNe _hAll _hNone hMult hInter hUnion
    have hEq : __re_rev_comp c = c := by
      cases c
      case Stuck => exact absurd rfl (fun h => hNe h)
      case UOp op => cases op <;> rfl
      case Apply f x =>
        cases f
        case UOp op =>
          cases op <;> first | rfl | exact ((hMult _ rfl).elim)
        case Apply g y =>
          cases g
          case UOp op2 =>
            cases op2 <;>
              first
                | rfl
                | exact ((hInter _ _ rfl).elim)
                | exact ((hUnion _ _ rfl).elim)
          all_goals rfl
        all_goals rfl
      all_goals rfl
    rw [StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local, hEq]
    exact ⟨fun h => Or.inl h, fun h => Or.inl h⟩
  constructor
  · intro t acc
    exact __re_rev_map_rev.induct
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 t acc
  · intro c
    exact __re_rev_comp.induct
      StrInReConsumeInternal.consume_rev_flat_rev_map_motive_local
      StrInReConsumeInternal.consume_rev_flat_rev_comp_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 c

/--
The seed for the bridges: `rFlat = __re_rev_map_rev (__re_flatten true
r) eps` satisfies the rev-flat chain invariant whenever it is not
stuck.
-/
theorem StrInReConsumeInternal.consume_rev_flat_chain_rev_flatten_local (r : Term)
    (hNe :
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
          StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck) :
    StrInReConsumeInternal.consume_rev_flat_chain_local
      (__re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        StrInReConsumeInternal.re_empty_string_re_consume_local) := by
  have hEpsChain : StrInReConsumeInternal.consume_rev_flat_chain_local
      StrInReConsumeInternal.re_empty_string_re_consume_local :=
    StrInReConsumeInternal.consume_rev_flat_chain_eps_local
  rcases (StrInReConsumeInternal.consume_rev_flat_flatten_facts_local (Term.Boolean true)
      r).1 rfl with hChain | hStuck
  · rcases StrInReConsumeInternal.consume_rev_flat_rev_facts_local.1 _ _ hChain hEpsChain with
      h | h
    · exact h
    · exact absurd h hNe
  · exfalso
    apply hNe
    rw [hStuck]
    exact StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local Term.Stuck _
      (by intro h; cases h) (by intro a b h; cases h)

theorem StrInReConsumeInternal.consume_re_concat_eps_right_local (C : SmtRegLan) :
    native_re_concat C (native_str_to_re []) = C := by
  cases C <;> rfl

theorem StrInReConsumeInternal.consume_eval_eps_re_local (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      SmtValue.RegLan (native_str_to_re []) := by
  change __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    SmtValue.RegLan (native_str_to_re [])
  rw [show __smtx_model_eval M
      (SmtTerm.str_to_re (SmtTerm.String [])) =
    __smtx_model_eval_str_to_re
      (__smtx_model_eval M (SmtTerm.String [])) from by
    simp [__smtx_model_eval]]
  rw [show __smtx_model_eval M (SmtTerm.String []) =
    SmtValue.Seq (native_pack_string []) from by
    simp [__smtx_model_eval]]
  simp [__smtx_model_eval_str_to_re]

theorem StrInReConsumeInternal.consume_eval_re_concat_inv_local (M : SmtModel)
    (A B : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) A) B)) =
      SmtValue.RegLan v) :
    ∃ av bv : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt A) = SmtValue.RegLan av ∧
      __smtx_model_eval M (__eo_to_smt B) = SmtValue.RegLan bv ∧
      v = native_re_concat av bv := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt A) (__eo_to_smt B)) =
    SmtValue.RegLan v at h
  have h' : __smtx_model_eval_re_concat
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt B)) = SmtValue.RegLan v := by
    rw [show __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt A) (__eo_to_smt B)) =
      __smtx_model_eval_re_concat
        (__smtx_model_eval M (__eo_to_smt A))
        (__smtx_model_eval M (__eo_to_smt B)) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M (__eo_to_smt A) with
  | RegLan av =>
      cases hB : __smtx_model_eval M (__eo_to_smt B) with
      | RegLan bv =>
          rw [hA, hB] at h'
          have h2 : SmtValue.RegLan (native_re_concat av bv) =
              SmtValue.RegLan v := h'
          injection h2 with h3
          exact ⟨av, bv, rfl, rfl, h3.symm⟩
      | _ =>
          rw [hA, hB] at h'
          exact absurd h' (by simp [__smtx_model_eval_re_concat])
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_re_concat])

theorem StrInReConsumeInternal.consume_eval_re_mult_inv_local (M : SmtModel)
    (A : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) A)) =
      SmtValue.RegLan v) :
    ∃ av : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt A) = SmtValue.RegLan av ∧
      v = native_re_mult av := by
  change __smtx_model_eval M
      (SmtTerm.re_mult (__eo_to_smt A)) = SmtValue.RegLan v at h
  have h' : __smtx_model_eval_re_mult
      (__smtx_model_eval M (__eo_to_smt A)) = SmtValue.RegLan v := by
    rw [show __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt A)) =
      __smtx_model_eval_re_mult
        (__smtx_model_eval M (__eo_to_smt A)) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M (__eo_to_smt A) with
  | RegLan av =>
      rw [hA] at h'
      have h2 : SmtValue.RegLan (native_re_mult av) =
          SmtValue.RegLan v := h'
      injection h2 with h3
      exact ⟨av, rfl, h3.symm⟩
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_re_mult])

theorem StrInReConsumeInternal.consume_eval_re_inter_inv_local (M : SmtModel)
    (A B : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) A) B)) =
      SmtValue.RegLan v) :
    ∃ av bv : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt A) = SmtValue.RegLan av ∧
      __smtx_model_eval M (__eo_to_smt B) = SmtValue.RegLan bv ∧
      v = native_re_inter av bv := by
  change __smtx_model_eval M
      (SmtTerm.re_inter (__eo_to_smt A) (__eo_to_smt B)) =
    SmtValue.RegLan v at h
  have h' : __smtx_model_eval_re_inter
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt B)) = SmtValue.RegLan v := by
    rw [show __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt A) (__eo_to_smt B)) =
      __smtx_model_eval_re_inter
        (__smtx_model_eval M (__eo_to_smt A))
        (__smtx_model_eval M (__eo_to_smt B)) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M (__eo_to_smt A) with
  | RegLan av =>
      cases hB : __smtx_model_eval M (__eo_to_smt B) with
      | RegLan bv =>
          rw [hA, hB] at h'
          have h2 : SmtValue.RegLan (native_re_inter av bv) =
              SmtValue.RegLan v := h'
          injection h2 with h3
          exact ⟨av, bv, rfl, rfl, h3.symm⟩
      | _ =>
          rw [hA, hB] at h'
          exact absurd h' (by simp [__smtx_model_eval_re_inter])
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_re_inter])

theorem StrInReConsumeInternal.consume_eval_re_union_inv_local (M : SmtModel)
    (A B : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) A) B)) =
      SmtValue.RegLan v) :
    ∃ av bv : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt A) = SmtValue.RegLan av ∧
      __smtx_model_eval M (__eo_to_smt B) = SmtValue.RegLan bv ∧
      v = native_re_union av bv := by
  change __smtx_model_eval M
      (SmtTerm.re_union (__eo_to_smt A) (__eo_to_smt B)) =
    SmtValue.RegLan v at h
  have h' : __smtx_model_eval_re_union
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt B)) = SmtValue.RegLan v := by
    rw [show __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt A) (__eo_to_smt B)) =
      __smtx_model_eval_re_union
        (__smtx_model_eval M (__eo_to_smt A))
        (__smtx_model_eval M (__eo_to_smt B)) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M (__eo_to_smt A) with
  | RegLan av =>
      cases hB : __smtx_model_eval M (__eo_to_smt B) with
      | RegLan bv =>
          rw [hA, hB] at h'
          have h2 : SmtValue.RegLan (native_re_union av bv) =
              SmtValue.RegLan v := h'
          injection h2 with h3
          exact ⟨av, bv, rfl, rfl, h3.symm⟩
      | _ =>
          rw [hA, hB] at h'
          exact absurd h' (by simp [__smtx_model_eval_re_union])
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_re_union])

theorem StrInReConsumeInternal.consume_eval_str_to_re_inv_local (M : SmtModel)
    (A : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) A)) =
      SmtValue.RegLan v) :
    ∃ sv : SmtSeq,
      __smtx_model_eval M (__eo_to_smt A) = SmtValue.Seq sv ∧
      v = native_str_to_re (native_unpack_seq sv) := by
  change __smtx_model_eval M
      (SmtTerm.str_to_re (__eo_to_smt A)) = SmtValue.RegLan v at h
  have h' : __smtx_model_eval_str_to_re
      (__smtx_model_eval M (__eo_to_smt A)) = SmtValue.RegLan v := by
    rw [show __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt A)) =
      __smtx_model_eval_str_to_re
        (__smtx_model_eval M (__eo_to_smt A)) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M (__eo_to_smt A) with
  | Seq sv =>
      rw [hA] at h'
      have h2 : SmtValue.RegLan
          (native_str_to_re (native_unpack_seq sv)) =
        SmtValue.RegLan v := h'
      injection h2 with h3
      exact ⟨sv, rfl, h3.symm⟩
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_str_to_re])

theorem StrInReConsumeInternal.consume_eval_str_to_re_seq_empty_local (M : SmtModel)
    (U : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_to_re)
            (Term.UOp1 UserOp1.seq_empty U))) =
      SmtValue.RegLan v) :
    v = native_str_to_re [] := by
  rcases StrInReConsumeInternal.consume_eval_str_to_re_inv_local M _ v h with ⟨sv, hSv, hV⟩
  have hSmt : __eo_to_smt (Term.UOp1 UserOp1.seq_empty U) =
      __eo_to_smt_seq_empty (__eo_to_smt_type U) := rfl
  rw [hSmt] at hSv
  cases hT : __eo_to_smt_type U with
  | Seq T =>
      rw [hT] at hSv
      simp only [__eo_to_smt_seq_empty] at hSv
      rw [show __smtx_model_eval M (SmtTerm.seq_empty T) =
        SmtValue.Seq (SmtSeq.empty T) from by
        simp [__smtx_model_eval]] at hSv
      injection hSv with h3
      rw [hV, ← h3]
      first
        | rfl
        | simp [native_unpack_seq]
  | _ =>
      rw [hT] at hSv
      simp only [__eo_to_smt_seq_empty] at hSv
      rw [show __smtx_model_eval M SmtTerm.None =
        SmtValue.NotValue from by simp [__smtx_model_eval]] at hSv
      cases hSv

theorem StrInReConsumeInternal.consume_smt_value_rel_re_mult_congr_local
    {r r' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r')) :
    RuleProofs.smt_value_rel (SmtValue.RegLan (native_re_mult r))
      (SmtValue.RegLan (native_re_mult r')) :=
  smt_value_rel_of_native_includes_local
    (native_includes_star_mono (native_includes_of_smt_value_rel hr))
    (native_includes_star_mono
      (native_includes_of_smt_value_rel
        (RuleProofs.smt_value_rel_symm _ _ hr)))

theorem StrInReConsumeInternal.consume_smt_value_rel_re_union_congr_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union r s))
      (SmtValue.RegLan (native_re_union r' s')) :=
  smt_value_rel_re_union_consume_local hr hs

theorem StrInReConsumeInternal.consume_smt_value_rel_re_inter_congr_local
    {r r' s s' : SmtRegLan}
    (hr : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan r'))
    (hs : RuleProofs.smt_value_rel (SmtValue.RegLan s)
      (SmtValue.RegLan s')) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter r s))
      (SmtValue.RegLan (native_re_inter r' s')) :=
  smt_value_rel_re_inter_consume_local hr hs

theorem StrInReConsumeInternal.consume_eval_det_local {M : SmtModel} {A : SmtTerm}
    {v1 v2 : SmtRegLan}
    (h1 : __smtx_model_eval M A = SmtValue.RegLan v1)
    (h2 : __smtx_model_eval M A = SmtValue.RegLan v2) : v1 = v2 := by
  rw [h1] at h2
  injection h2

theorem StrInReConsumeInternal.consume_eval_stuck_not_reglan_local {M : SmtModel}
    {v : SmtRegLan}
    (h : __smtx_model_eval M (__eo_to_smt Term.Stuck) =
      SmtValue.RegLan v) : False := by
  change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan v at h
  rw [show __smtx_model_eval M SmtTerm.None =
    SmtValue.NotValue from by simp [__smtx_model_eval]] at h
  cases h

theorem StrInReConsumeInternal.consume_flatten_false_id_local (c : Term)
    (hMult : ∀ body, c = Term.Apply (Term.UOp UserOp.re_mult) body ->
      False)
    (hInter : ∀ c1 c2,
      c = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ->
        False)
    (hUnion : ∀ c1 c2,
      c = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 ->
        False) :
    __re_flatten (Term.Boolean false) c = c := by
  cases c
  case Stuck => simp [__re_flatten]
  case UOp op => cases op <;> simp [__re_flatten]
  case Apply f x =>
    cases f
    case UOp op =>
      cases op <;>
        first
          | exact ((hMult _ rfl).elim)
          | simp [__re_flatten]
    case Apply g y =>
      cases g
      case UOp op2 =>
        cases op2 <;>
          first
            | exact ((hInter _ _ rfl).elim)
            | exact ((hUnion _ _ rfl).elim)
            | simp [__re_flatten]
      all_goals simp [__re_flatten]
    all_goals simp [__re_flatten]
  all_goals simp [__re_flatten]

theorem StrInReConsumeInternal.consume_rev_comp_str_to_re_id_local (x : Term) :
    __re_rev_comp (Term.Apply (Term.UOp UserOp.str_to_re) x) =
      Term.Apply (Term.UOp UserOp.str_to_re) x := by
  simp [__re_rev_comp]

/--
Core value step: both sides are a reversal of a tail continued with a
single-chunk accumulator `(re.++ K eps)`; the tails are value-related
(by the outer induction) and the chunks are value-related, hence the
full values are related.
-/
theorem StrInReConsumeInternal.consume_core_step_local (M : SmtModel)
    (T1 T2 K1 K2 : Term) (v1 v2 : SmtRegLan)
    (hEval1 : __smtx_model_eval M
        (__eo_to_smt
          (__re_rev_map_rev T1
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) K1)
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))) =
      SmtValue.RegLan v1)
    (hEval2 : __smtx_model_eval M
        (__eo_to_smt
          (__re_rev_map_rev T2
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) K2)
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))) =
      SmtValue.RegLan v2)
    (hIH : ∀ w1 w2 : SmtRegLan,
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev T1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])))) =
        SmtValue.RegLan w1 ->
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev T2
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])))) =
        SmtValue.RegLan w2 ->
      RuleProofs.smt_value_rel (SmtValue.RegLan w1)
        (SmtValue.RegLan w2))
    (hK : ∀ k1 k2 : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt K1) = SmtValue.RegLan k1 ->
      __smtx_model_eval M (__eo_to_smt K2) = SmtValue.RegLan k2 ->
      RuleProofs.smt_value_rel (SmtValue.RegLan k1)
        (SmtValue.RegLan k2)) :
    RuleProofs.smt_value_rel (SmtValue.RegLan v1)
      (SmtValue.RegLan v2) := by
  rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M T1 _ v1 hEval1
    with ⟨⟨a1V, hA1V⟩, C1, hC1⟩
  rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M T2 _ v2 hEval2
    with ⟨⟨a2V, hA2V⟩, C2, hC2⟩
  rcases StrInReConsumeInternal.consume_eval_re_concat_inv_local M K1 _ a1V hA1V with
    ⟨k1, e1, hK1, hE1, hA1Eq⟩
  rcases StrInReConsumeInternal.consume_eval_re_concat_inv_local M K2 _ a2V hA2V with
    ⟨k2, e2, hK2, hE2, hA2Eq⟩
  have hE1Eq : e1 = native_str_to_re [] :=
    StrInReConsumeInternal.consume_eval_det_local hE1 (StrInReConsumeInternal.consume_eval_eps_re_local M)
  have hE2Eq : e2 = native_str_to_re [] :=
    StrInReConsumeInternal.consume_eval_det_local hE2 (StrInReConsumeInternal.consume_eval_eps_re_local M)
  rcases hC1 (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      (native_str_to_re []) (StrInReConsumeInternal.consume_eval_eps_re_local M) with
    ⟨w1, hW1, hRelW1⟩
  rcases hC2 (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      (native_str_to_re []) (StrInReConsumeInternal.consume_eval_eps_re_local M) with
    ⟨w2, hW2, hRelW2⟩
  have hRelW := hIH w1 w2 hW1 hW2
  rcases hC1 _ a1V hA1V with ⟨v1', hV1', hRelV1⟩
  have hv1Eq : v1 = v1' := StrInReConsumeInternal.consume_eval_det_local hEval1 hV1'
  rcases hC2 _ a2V hA2V with ⟨v2', hV2', hRelV2⟩
  have hv2Eq : v2 = v2' := StrInReConsumeInternal.consume_eval_det_local hEval2 hV2'
  have hKRel := hK k1 k2 hK1 hK2
  rw [StrInReConsumeInternal.consume_re_concat_eps_right_local] at hRelW1 hRelW2
  have hC12 : RuleProofs.smt_value_rel (SmtValue.RegLan C1)
      (SmtValue.RegLan C2) :=
    RuleProofs.smt_value_rel_trans _ _ _
      (RuleProofs.smt_value_rel_symm _ _ hRelW1)
      (RuleProofs.smt_value_rel_trans _ _ _ hRelW hRelW2)
  have hAccRel : RuleProofs.smt_value_rel (SmtValue.RegLan a1V)
      (SmtValue.RegLan a2V) := by
    rw [hA1Eq, hA2Eq, hE1Eq, hE2Eq]
    exact smt_value_rel_re_concat_consume_local hKRel
      (RuleProofs.smt_value_rel_refl _)
  rw [hv1Eq, hv2Eq]
  exact RuleProofs.smt_value_rel_trans _ _ _ hRelV1
    (RuleProofs.smt_value_rel_trans _ _ _
      (smt_value_rel_re_concat_consume_local hC12 hAccRel)
      (RuleProofs.smt_value_rel_symm _ _ hRelV2))

/--
CORE: on rev-flat invariant chains, re-flattening before reversal is
value-preserving; chunk- and tail-level companions for the
combinator recursion.
-/
theorem StrInReConsumeInternal.consume_core_rel_fuel_local (M : SmtModel) :
    ∀ n : Nat, ∀ t : Term, sizeOf t < n ->
      (StrInReConsumeInternal.consume_rev_flat_chain_local t ->
        ∀ v1 v2 : SmtRegLan,
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_map_rev (__re_flatten (Term.Boolean true) t)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])))) =
            SmtValue.RegLan v1 ->
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_map_rev t
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])))) =
            SmtValue.RegLan v2 ->
          RuleProofs.smt_value_rel (SmtValue.RegLan v1)
            (SmtValue.RegLan v2)) ∧
      (StrInReConsumeInternal.consume_rev_flat_chunk_local t ->
        ∀ v1 v2 : SmtRegLan,
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp (__re_flatten (Term.Boolean false) t))) =
            SmtValue.RegLan v1 ->
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp t)) =
            SmtValue.RegLan v2 ->
          RuleProofs.smt_value_rel (SmtValue.RegLan v1)
            (SmtValue.RegLan v2)) ∧
      (StrInReConsumeInternal.consume_rev_flat_inter_tail_local t ->
        ∀ v1 v2 : SmtRegLan,
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp (__re_flatten (Term.Boolean false) t))) =
            SmtValue.RegLan v1 ->
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp t)) =
            SmtValue.RegLan v2 ->
          RuleProofs.smt_value_rel (SmtValue.RegLan v1)
            (SmtValue.RegLan v2)) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exact absurd ht (Nat.not_lt_zero _)
  | succ n ih =>
      intro t ht
      -- combinator-component handler shared by the chunk and tail
      -- conjuncts
      have hComb : ∀ v1 v2 : SmtRegLan,
          (∃ body,
            t = Term.Apply (Term.UOp UserOp.re_mult) body ∧
              StrInReConsumeInternal.consume_rev_flat_chain_local body) ∨
          (∃ c1 c2,
            (t = Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 ∨
             t = Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) c1) c2) ∧
              StrInReConsumeInternal.consume_rev_flat_chain_local c1 ∧
              StrInReConsumeInternal.consume_rev_flat_inter_tail_local c2) ->
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp (__re_flatten (Term.Boolean false) t))) =
            SmtValue.RegLan v1 ->
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp t)) =
            SmtValue.RegLan v2 ->
          RuleProofs.smt_value_rel (SmtValue.RegLan v1)
            (SmtValue.RegLan v2) := by
        intro v1 v2 hShape hEval1 hEval2
        rcases hShape with ⟨body, rfl, hBody⟩ | ⟨c1, c2, hUI, hC1, hC2⟩
        · -- re_mult
          have hSize : sizeOf body < n := by
            simp at ht
            omega
          have hRed : __re_flatten (Term.Boolean false)
              (Term.Apply (Term.UOp UserOp.re_mult) body) =
            __eo_mk_apply (Term.UOp UserOp.re_mult)
              (__re_flatten (Term.Boolean true) body) := by
            simp [__re_flatten]
          rw [hRed] at hEval1
          by_cases hFS : __re_flatten (Term.Boolean true) body =
              Term.Stuck
          · exfalso
            rw [hFS] at hEval1
            have hMk : __eo_mk_apply (Term.UOp UserOp.re_mult)
                Term.Stuck = Term.Stuck := rfl
            rw [hMk] at hEval1
            have hRC : __re_rev_comp Term.Stuck = Term.Stuck := by simp [__re_rev_comp]
            rw [hRC] at hEval1
            exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
          · have hMk : __eo_mk_apply (Term.UOp UserOp.re_mult)
                (__re_flatten (Term.Boolean true) body) =
              Term.Apply (Term.UOp UserOp.re_mult)
                (__re_flatten (Term.Boolean true) body) := by
              cases hF : __re_flatten (Term.Boolean true) body <;>
                first | exact absurd hF hFS | rfl
            rw [hMk] at hEval1
            have hRC1 : __re_rev_comp
                (Term.Apply (Term.UOp UserOp.re_mult)
                  (__re_flatten (Term.Boolean true) body)) =
              __eo_mk_apply (Term.UOp UserOp.re_mult)
                (__re_rev_map_rev
                  (__re_flatten (Term.Boolean true) body)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) := by
              simp [__re_rev_comp]
            have hRC2 : __re_rev_comp
                (Term.Apply (Term.UOp UserOp.re_mult) body) =
              __eo_mk_apply (Term.UOp UserOp.re_mult)
                (__re_rev_map_rev body
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) := by
              simp [__re_rev_comp]
            rw [hRC1] at hEval1
            rw [hRC2] at hEval2
            by_cases hR1S : __re_rev_map_rev
                (__re_flatten (Term.Boolean true) body)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])) = Term.Stuck
            · exfalso
              rw [hR1S, StrInReConsumeInternal.consume_mk_apply_stuck_right_local] at hEval1
              exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
            · by_cases hR2S : __re_rev_map_rev body
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])) = Term.Stuck
              · exfalso
                rw [hR2S, StrInReConsumeInternal.consume_mk_apply_stuck_right_local] at hEval2
                exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
              · have hApp1 : __eo_mk_apply (Term.UOp UserOp.re_mult)
                    (__re_rev_map_rev
                      (__re_flatten (Term.Boolean true) body)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))) =
                  Term.Apply (Term.UOp UserOp.re_mult)
                    (__re_rev_map_rev
                      (__re_flatten (Term.Boolean true) body)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))) := by
                  cases hF : __re_rev_map_rev
                      (__re_flatten (Term.Boolean true) body)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String [])) <;>
                    first | exact absurd hF hR1S | rfl
                have hApp2 : __eo_mk_apply (Term.UOp UserOp.re_mult)
                    (__re_rev_map_rev body
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))) =
                  Term.Apply (Term.UOp UserOp.re_mult)
                    (__re_rev_map_rev body
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))) := by
                  cases hF : __re_rev_map_rev body
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String [])) <;>
                    first | exact absurd hF hR2S | rfl
                rw [hApp1] at hEval1
                rw [hApp2] at hEval2
                rcases StrInReConsumeInternal.consume_eval_re_mult_inv_local M _ _ hEval1 with
                  ⟨i1, hI1, hV1⟩
                rcases StrInReConsumeInternal.consume_eval_re_mult_inv_local M _ _ hEval2 with
                  ⟨i2, hI2, hV2⟩
                have hInner := (ih body hSize).1 hBody i1 i2 hI1 hI2
                rw [hV1, hV2]
                exact StrInReConsumeInternal.consume_smt_value_rel_re_mult_congr_local hInner
        · -- re_inter / re_union: uniform treatment
          rcases hUI with rfl | rfl
          · -- inter
            simp at ht
            have hSize1 : sizeOf c1 < n := by omega
            have hSize2 : sizeOf c2 < n := by omega
            have hRed : __re_flatten (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                  c2) =
              __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_inter)
                  (__re_flatten (Term.Boolean true) c1))
                (__re_flatten (Term.Boolean false) c2) := by
              simp [__re_flatten]
            rw [hRed] at hEval1
            by_cases hF1S : __re_flatten (Term.Boolean true) c1 =
                Term.Stuck
            · exfalso
              rw [hF1S] at hEval1
              have hMk : __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.re_inter) Term.Stuck)
                  (__re_flatten (Term.Boolean false) c2) =
                Term.Stuck := rfl
              rw [hMk] at hEval1
              have hRC : __re_rev_comp Term.Stuck = Term.Stuck := by simp [__re_rev_comp]
              rw [hRC] at hEval1
              exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
            · by_cases hF2S : __re_flatten (Term.Boolean false) c2 =
                  Term.Stuck
              · exfalso
                rw [hF2S, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                  at hEval1
                have hRC : __re_rev_comp Term.Stuck = Term.Stuck := by simp [__re_rev_comp]
                rw [hRC] at hEval1
                exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
              · have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                  (Term.UOp UserOp.re_inter)
                  (__re_flatten (Term.Boolean true) c1)
                  (__re_flatten (Term.Boolean false) c2)
                  (by intro h; cases h) hF1S hF2S
                rw [hShape] at hEval1
                have hRC1 : __re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_inter)
                        (__re_flatten (Term.Boolean true) c1))
                      (__re_flatten (Term.Boolean false) c2)) =
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_inter)
                      (__re_rev_map_rev
                        (__re_flatten (Term.Boolean true) c1)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []))))
                    (__re_rev_comp
                      (__re_flatten (Term.Boolean false) c2)) := by
                  simp [__re_rev_comp]
                have hRC2 : __re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) =
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_inter)
                      (__re_rev_map_rev c1
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []))))
                    (__re_rev_comp c2) := by
                  simp [__re_rev_comp]
                rw [hRC1] at hEval1
                rw [hRC2] at hEval2
                by_cases hRa : __re_rev_map_rev
                    (__re_flatten (Term.Boolean true) c1)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])) = Term.Stuck
                · exfalso
                  rw [hRa] at hEval1
                  have hMk : __eo_mk_apply
                      (__eo_mk_apply (Term.UOp UserOp.re_inter)
                        Term.Stuck)
                      (__re_rev_comp
                        (__re_flatten (Term.Boolean false) c2)) =
                    Term.Stuck := rfl
                  rw [hMk] at hEval1
                  exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                · by_cases hRb : __re_rev_comp
                      (__re_flatten (Term.Boolean false) c2) =
                      Term.Stuck
                  · exfalso
                    rw [hRb, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                      at hEval1
                    exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                  · have hShape1 :=
                      StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                        (Term.UOp UserOp.re_inter)
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) c1)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__re_rev_comp
                          (__re_flatten (Term.Boolean false) c2))
                        (by intro h; cases h) hRa hRb
                    rw [hShape1] at hEval1
                    by_cases hRc : __re_rev_map_rev c1
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String [])) = Term.Stuck
                    · exfalso
                      rw [hRc] at hEval2
                      have hMk : __eo_mk_apply
                          (__eo_mk_apply (Term.UOp UserOp.re_inter)
                            Term.Stuck) (__re_rev_comp c2) =
                        Term.Stuck := rfl
                      rw [hMk] at hEval2
                      exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
                    · by_cases hRd : __re_rev_comp c2 = Term.Stuck
                      · exfalso
                        rw [hRd, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                          at hEval2
                        exact
                          StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
                      · have hShape2 :=
                          StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                            (Term.UOp UserOp.re_inter)
                            (__re_rev_map_rev c1
                              (Term.Apply (Term.UOp UserOp.str_to_re)
                                (Term.String [])))
                            (__re_rev_comp c2)
                            (by intro h; cases h) hRc hRd
                        rw [hShape2] at hEval2
                        rcases StrInReConsumeInternal.consume_eval_re_inter_inv_local M _ _ _
                            hEval1 with ⟨a1, b1, hA1, hB1, hV1⟩
                        rcases StrInReConsumeInternal.consume_eval_re_inter_inv_local M _ _ _
                            hEval2 with ⟨a2, b2, hA2, hB2, hV2⟩
                        have hLeft := (ih c1 hSize1).1 hC1 a1 a2 hA1
                          hA2
                        have hRight := (ih c2 hSize2).2.2 hC2 b1 b2
                          hB1 hB2
                        rw [hV1, hV2]
                        exact
                          StrInReConsumeInternal.consume_smt_value_rel_re_inter_congr_local
                            hLeft hRight
          · -- union: mirror of inter
            simp at ht
            have hSize1 : sizeOf c1 < n := by omega
            have hSize2 : sizeOf c2 < n := by omega
            have hRed : __re_flatten (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
                  c2) =
              __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_union)
                  (__re_flatten (Term.Boolean true) c1))
                (__re_flatten (Term.Boolean false) c2) := by
              simp [__re_flatten]
            rw [hRed] at hEval1
            by_cases hF1S : __re_flatten (Term.Boolean true) c1 =
                Term.Stuck
            · exfalso
              rw [hF1S] at hEval1
              have hMk : __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.re_union) Term.Stuck)
                  (__re_flatten (Term.Boolean false) c2) =
                Term.Stuck := rfl
              rw [hMk] at hEval1
              have hRC : __re_rev_comp Term.Stuck = Term.Stuck := by simp [__re_rev_comp]
              rw [hRC] at hEval1
              exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
            · by_cases hF2S : __re_flatten (Term.Boolean false) c2 =
                  Term.Stuck
              · exfalso
                rw [hF2S, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                  at hEval1
                have hRC : __re_rev_comp Term.Stuck = Term.Stuck := by simp [__re_rev_comp]
                rw [hRC] at hEval1
                exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
              · have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                  (Term.UOp UserOp.re_union)
                  (__re_flatten (Term.Boolean true) c1)
                  (__re_flatten (Term.Boolean false) c2)
                  (by intro h; cases h) hF1S hF2S
                rw [hShape] at hEval1
                have hRC1 : __re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_union)
                        (__re_flatten (Term.Boolean true) c1))
                      (__re_flatten (Term.Boolean false) c2)) =
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_union)
                      (__re_rev_map_rev
                        (__re_flatten (Term.Boolean true) c1)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []))))
                    (__re_rev_comp
                      (__re_flatten (Term.Boolean false) c2)) := by
                  simp [__re_rev_comp]
                have hRC2 : __re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_union) c1) c2) =
                  __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_union)
                      (__re_rev_map_rev c1
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []))))
                    (__re_rev_comp c2) := by
                  simp [__re_rev_comp]
                rw [hRC1] at hEval1
                rw [hRC2] at hEval2
                by_cases hRa : __re_rev_map_rev
                    (__re_flatten (Term.Boolean true) c1)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])) = Term.Stuck
                · exfalso
                  rw [hRa] at hEval1
                  have hMk : __eo_mk_apply
                      (__eo_mk_apply (Term.UOp UserOp.re_union)
                        Term.Stuck)
                      (__re_rev_comp
                        (__re_flatten (Term.Boolean false) c2)) =
                    Term.Stuck := rfl
                  rw [hMk] at hEval1
                  exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                · by_cases hRb : __re_rev_comp
                      (__re_flatten (Term.Boolean false) c2) =
                      Term.Stuck
                  · exfalso
                    rw [hRb, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                      at hEval1
                    exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                  · have hShape1 :=
                      StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                        (Term.UOp UserOp.re_union)
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) c1)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__re_rev_comp
                          (__re_flatten (Term.Boolean false) c2))
                        (by intro h; cases h) hRa hRb
                    rw [hShape1] at hEval1
                    by_cases hRc : __re_rev_map_rev c1
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String [])) = Term.Stuck
                    · exfalso
                      rw [hRc] at hEval2
                      have hMk : __eo_mk_apply
                          (__eo_mk_apply (Term.UOp UserOp.re_union)
                            Term.Stuck) (__re_rev_comp c2) =
                        Term.Stuck := rfl
                      rw [hMk] at hEval2
                      exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
                    · by_cases hRd : __re_rev_comp c2 = Term.Stuck
                      · exfalso
                        rw [hRd, StrInReConsumeInternal.consume_mk_apply_stuck_right_local]
                          at hEval2
                        exact
                          StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
                      · have hShape2 :=
                          StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                            (Term.UOp UserOp.re_union)
                            (__re_rev_map_rev c1
                              (Term.Apply (Term.UOp UserOp.str_to_re)
                                (Term.String [])))
                            (__re_rev_comp c2)
                            (by intro h; cases h) hRc hRd
                        rw [hShape2] at hEval2
                        rcases StrInReConsumeInternal.consume_eval_re_union_inv_local M _ _ _
                            hEval1 with ⟨a1, b1, hA1, hB1, hV1⟩
                        rcases StrInReConsumeInternal.consume_eval_re_union_inv_local M _ _ _
                            hEval2 with ⟨a2, b2, hA2, hB2, hV2⟩
                        have hLeft := (ih c1 hSize1).1 hC1 a1 a2 hA1
                          hA2
                        have hRight := (ih c2 hSize2).2.2 hC2 b1 b2
                          hB1 hB2
                        rw [hV1, hV2]
                        exact
                          StrInReConsumeInternal.consume_smt_value_rel_re_union_congr_local
                            hLeft hRight
      -- identity handler for all other chunk shapes
      have hIdent : ∀ v1 v2 : SmtRegLan,
          (∀ body, t = Term.Apply (Term.UOp UserOp.re_mult) body ->
            False) ->
          (∀ c1 c2,
            t = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
              c2 -> False) ->
          (∀ c1 c2,
            t = Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
              c2 -> False) ->
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp (__re_flatten (Term.Boolean false) t))) =
            SmtValue.RegLan v1 ->
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp t)) =
            SmtValue.RegLan v2 ->
          RuleProofs.smt_value_rel (SmtValue.RegLan v1)
            (SmtValue.RegLan v2) := by
        intro v1 v2 hM hI hU hEval1 hEval2
        rw [StrInReConsumeInternal.consume_flatten_false_id_local t hM hI hU] at hEval1
        have hEq := StrInReConsumeInternal.consume_eval_det_local hEval1 hEval2
        rw [hEq]
        exact RuleProofs.smt_value_rel_refl _
      refine ⟨?_, ?_, ?_⟩
      · -- chain conjunct
        intro hChain v1 v2 hEval1 hEval2
        rcases StrInReConsumeInternal.consume_rev_flat_chain_shape_local t hChain with
          hEps | ⟨h, rest, rfl⟩
        · subst hEps
          have hRed : __re_flatten (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) =
            Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
            simp [__re_flatten]
          rw [hRed] at hEval1
          have hEq := StrInReConsumeInternal.consume_eval_det_local hEval1 hEval2
          rw [hEq]
          exact RuleProofs.smt_value_rel_refl _
        · have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local
            hChain
          simp at ht
          have hSizeRest : sizeOf rest < n := by omega
          have hSizeH : sizeOf h < n := by omega
          -- normalize the plain side
          rw [__re_rev_map_rev.eq_3 _ h rest (by intro hh; cases hh)]
            at hEval2
          by_cases hCS : __re_rev_comp h = Term.Stuck
          · exfalso
            rw [hCS] at hEval2
            have hMk : __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.re_concat) Term.Stuck)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])) = Term.Stuck := rfl
            rw [hMk, __re_rev_map_rev.eq_1] at hEval2
            exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval2
          · have hShape2 := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
              (Term.UOp UserOp.re_concat) (__re_rev_comp h)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
              (by intro hh; cases hh) hCS (by intro hh; cases hh)
            rw [hShape2] at hEval2
            -- dispatch on the head chunk
            by_cases hIsStr : ∃ x,
                h = Term.Apply (Term.UOp UserOp.str_to_re) x
            · obtain ⟨x, rfl⟩ := hIsStr
              have hReprod :=
                StrInReConsumeInternal.consume_rev_flat_chunk_str_to_re_parts_local hParts.1
              have hRed : __re_flatten (Term.Boolean true)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.Apply (Term.UOp UserOp.str_to_re) x))
                    rest) =
                __re_split_str_to_re
                  (__str_flatten
                    (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) x))
                  (__re_flatten (Term.Boolean true) rest) := by
                simp [__re_flatten]
              rw [hRed] at hEval1
              rcases hReprod with hExact | ⟨hDrop, hEpsV⟩ | hStuck
              · -- exact reproduction
                rw [hExact (__re_flatten (Term.Boolean true) rest)]
                  at hEval1
                by_cases hFS : __re_flatten (Term.Boolean true) rest =
                    Term.Stuck
                · exfalso
                  rw [hFS, StrInReConsumeInternal.consume_mk_apply_stuck_right_local,
                    StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local Term.Stuck
                      _ (by intro hh; cases hh)
                      (by intro a b hh; cases hh)] at hEval1
                  exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                · have hApp : __eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.re_concat)
                        (Term.Apply (Term.UOp UserOp.str_to_re) x))
                      (__re_flatten (Term.Boolean true) rest) =
                    Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat)
                        (Term.Apply (Term.UOp UserOp.str_to_re) x))
                      (__re_flatten (Term.Boolean true) rest) := by
                    cases hF : __re_flatten (Term.Boolean true)
                        rest <;>
                      first | exact absurd hF hFS | rfl
                  rw [hApp, __re_rev_map_rev.eq_3 _ _ _
                    (by intro hh; cases hh)] at hEval1
                  rw [StrInReConsumeInternal.consume_rev_comp_str_to_re_id_local] at hEval1
                  have hShape1 :=
                    StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                      (Term.UOp UserOp.re_concat)
                      (Term.Apply (Term.UOp UserOp.str_to_re) x)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))
                      (by intro hh; cases hh) (by intro hh; cases hh)
                      (by intro hh; cases hh)
                  rw [hShape1] at hEval1
                  rw [StrInReConsumeInternal.consume_rev_comp_str_to_re_id_local] at hEval2
                  exact StrInReConsumeInternal.consume_core_step_local M _ _ _ _ v1 v2 hEval1
                    hEval2
                    (fun w1 w2 h1 h2 =>
                      (ih rest hSizeRest).1 hParts.2 w1 w2 h1 h2)
                    (fun k1 k2 h1 h2 => by
                      have hEq := StrInReConsumeInternal.consume_eval_det_local h1 h2
                      rw [hEq]
                      exact RuleProofs.smt_value_rel_refl _)
              · -- dropped ε chunk
                rw [hDrop (__re_flatten (Term.Boolean true) rest)]
                  at hEval1
                rw [StrInReConsumeInternal.consume_rev_comp_str_to_re_id_local] at hEval2
                rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M rest
                    _ v2 hEval2 with ⟨⟨a2V, hA2V⟩, C2, hC2⟩
                rcases StrInReConsumeInternal.consume_eval_re_concat_inv_local M _ _ a2V hA2V
                  with ⟨k2, e2, hK2, hE2, hA2Eq⟩
                have hE2Eq : e2 = native_str_to_re [] :=
                  StrInReConsumeInternal.consume_eval_det_local hE2
                    (StrInReConsumeInternal.consume_eval_eps_re_local M)
                have hK2Eq : k2 = native_str_to_re [] := by
                  rcases hEpsV with rfl | ⟨U, rfl⟩
                  · exact StrInReConsumeInternal.consume_eval_det_local hK2
                      (StrInReConsumeInternal.consume_eval_eps_re_local M)
                  · exact StrInReConsumeInternal.consume_eval_str_to_re_seq_empty_local M U k2
                      hK2
                rcases hC2 (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])) (native_str_to_re [])
                    (StrInReConsumeInternal.consume_eval_eps_re_local M) with
                  ⟨w2, hW2, hRelW2⟩
                have hIH := (ih rest hSizeRest).1 hParts.2 v1 w2 hEval1
                  hW2
                rcases hC2 _ a2V hA2V with ⟨v2', hV2', hRelV2⟩
                have hv2Eq : v2 = v2' :=
                  StrInReConsumeInternal.consume_eval_det_local hEval2 hV2'
                rw [StrInReConsumeInternal.consume_re_concat_eps_right_local] at hRelW2
                have hAccEps : a2V = native_str_to_re [] := by
                  rw [hA2Eq, hK2Eq, hE2Eq]
                  exact StrInReConsumeInternal.consume_re_concat_eps_right_local _
                rw [hv2Eq]
                refine RuleProofs.smt_value_rel_trans _ _ _ hIH ?_
                refine RuleProofs.smt_value_rel_trans _ _ _ hRelW2 ?_
                have : native_re_concat C2 a2V = C2 := by
                  rw [hAccEps]
                  exact StrInReConsumeInternal.consume_re_concat_eps_right_local _
                rw [this] at hRelV2
                exact RuleProofs.smt_value_rel_symm _ _ hRelV2
              · -- stuck string flatten
                exfalso
                rw [hStuck, __re_split_str_to_re.eq_1] at hEval1
                have hRevStuck := StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local
                  Term.Stuck
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))
                  (by intro hh; cases hh) (by intro a b hh; cases hh)
                rw [hRevStuck] at hEval1
                exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
            · -- generic head chunk
              have hNotStr : ∀ s,
                  h = Term.Apply (Term.UOp UserOp.str_to_re) s ->
                    False := fun s hEq => hIsStr ⟨s, hEq⟩
              have hNotConcat : ∀ a b,
                  h = Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
                    False := by
                intro a b hEq
                have := hParts.1
                rw [hEq] at this
                simp [StrInReConsumeInternal.consume_rev_flat_chunk_local,
                  StrInReConsumeInternal.consume_rev_flat_local] at this
              have hRed : __re_flatten (Term.Boolean true)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) h) rest) =
                __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.re_concat)
                    (__re_flatten (Term.Boolean false) h))
                  (__re_flatten (Term.Boolean true) rest) := by
                simp [__re_flatten]
              rw [hRed] at hEval1
              by_cases hFHS : __re_flatten (Term.Boolean false) h =
                  Term.Stuck
              · exfalso
                rw [hFHS] at hEval1
                have hMk : __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_concat)
                      Term.Stuck)
                    (__re_flatten (Term.Boolean true) rest) =
                  Term.Stuck := rfl
                rw [hMk] at hEval1
                have hRevStuck :=
                  StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local
                    Term.Stuck
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String []))
                    (by intro hh; cases hh)
                    (by intro a b hh; cases hh)
                rw [hRevStuck] at hEval1
                exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
              · by_cases hFTS : __re_flatten (Term.Boolean true)
                    rest = Term.Stuck
                · exfalso
                  rw [hFTS, StrInReConsumeInternal.consume_mk_apply_stuck_right_local,
                    StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local Term.Stuck
                      _ (by intro hh; cases hh)
                      (by intro a b hh; cases hh)] at hEval1
                  exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                · have hShapeF := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                    (Term.UOp UserOp.re_concat)
                    (__re_flatten (Term.Boolean false) h)
                    (__re_flatten (Term.Boolean true) rest)
                    (by intro hh; cases hh) hFHS hFTS
                  rw [hShapeF, __re_rev_map_rev.eq_3 _ _ _
                    (by intro hh; cases hh)] at hEval1
                  by_cases hRCS : __re_rev_comp
                      (__re_flatten (Term.Boolean false) h) =
                      Term.Stuck
                  · exfalso
                    rw [hRCS] at hEval1
                    have hMk : __eo_mk_apply
                        (__eo_mk_apply (Term.UOp UserOp.re_concat)
                          Term.Stuck)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String [])) = Term.Stuck := rfl
                    rw [hMk, __re_rev_map_rev.eq_1] at hEval1
                    exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hEval1
                  · have hShape1 :=
                      StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
                        (Term.UOp UserOp.re_concat)
                        (__re_rev_comp
                          (__re_flatten (Term.Boolean false) h))
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String []))
                        (by intro hh; cases hh) hRCS
                        (by intro hh; cases hh)
                    rw [hShape1] at hEval1
                    exact StrInReConsumeInternal.consume_core_step_local M _ _ _ _ v1 v2
                      hEval1 hEval2
                      (fun w1 w2 h1 h2 =>
                        (ih rest hSizeRest).1 hParts.2 w1 w2 h1 h2)
                      (fun k1 k2 h1 h2 =>
                        (ih h hSizeH).2.1 hParts.1 k1 k2 h1 h2)
      · -- chunk conjunct
        intro hChunk v1 v2 hEval1 hEval2
        by_cases hMult : ∃ body,
            t = Term.Apply (Term.UOp UserOp.re_mult) body
        · obtain ⟨body, rfl⟩ := hMult
          exact hComb v1 v2
            (Or.inl ⟨body, rfl,
              StrInReConsumeInternal.consume_rev_flat_chunk_mult_parts_local hChunk⟩)
            hEval1 hEval2
        · by_cases hInter : ∃ c1 c2,
              t = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                c2
          · obtain ⟨c1, c2, rfl⟩ := hInter
            have hP := StrInReConsumeInternal.consume_rev_flat_chunk_inter_parts_local hChunk
            exact hComb v1 v2
              (Or.inr ⟨c1, c2, Or.inl rfl, hP.1, hP.2⟩) hEval1 hEval2
          · by_cases hUnion : ∃ c1 c2,
                t = Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union) c1) c2
            · obtain ⟨c1, c2, rfl⟩ := hUnion
              have hP :=
                StrInReConsumeInternal.consume_rev_flat_chunk_union_parts_local hChunk
              exact hComb v1 v2
                (Or.inr ⟨c1, c2, Or.inr rfl, hP.1, hP.2⟩) hEval1
                hEval2
            · exact hIdent v1 v2
                (fun body hEq => hMult ⟨body, hEq⟩)
                (fun c1 c2 hEq => hInter ⟨c1, c2, hEq⟩)
                (fun c1 c2 hEq => hUnion ⟨c1, c2, hEq⟩)
                hEval1 hEval2
      · -- tail conjunct
        intro hTail v1 v2 hEval1 hEval2
        by_cases hMult : ∃ body,
            t = Term.Apply (Term.UOp UserOp.re_mult) body
        · obtain ⟨body, rfl⟩ := hMult
          exact hComb v1 v2
            (Or.inl ⟨body, rfl,
              StrInReConsumeInternal.consume_rev_flat_tail_mult_parts_local hTail⟩)
            hEval1 hEval2
        · by_cases hInter : ∃ c1 c2,
              t = Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                c2
          · obtain ⟨c1, c2, rfl⟩ := hInter
            have hP := StrInReConsumeInternal.consume_rev_flat_inter_tail_parts_local hTail
            exact hComb v1 v2
              (Or.inr ⟨c1, c2, Or.inl rfl, hP.1, hP.2⟩) hEval1 hEval2
          · by_cases hUnion : ∃ c1 c2,
                t = Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union) c1) c2
            · obtain ⟨c1, c2, rfl⟩ := hUnion
              have hP := StrInReConsumeInternal.consume_rev_flat_tail_union_parts_local hTail
              exact hComb v1 v2
                (Or.inr ⟨c1, c2, Or.inr rfl, hP.1, hP.2⟩) hEval1
                hEval2
            · exact hIdent v1 v2
                (fun body hEq => hMult ⟨body, hEq⟩)
                (fun c1 c2 hEq => hInter ⟨c1, c2, hEq⟩)
                (fun c1 c2 hEq => hUnion ⟨c1, c2, hEq⟩)
                hEval1 hEval2

/--
Value-level bridge for the retried (carry-true) second pass of the
`re_mult` wrapper: the algorithm's `nextR` is
`__re_rev_map_rev (__re_flatten true rFlat) eps` where `rFlat` is
itself `__re_rev_map_rev (__re_flatten true rSrc) eps`; its value is
extensionally the value of `__re_flatten true rSrc` (i.e. of `rSrc`).

Not a syntactic identity: `__re_flatten true` may drop
`str_to_re (seq_empty _)` chunks of `rFlat` (value `{ε}`) and
normalize `re_mult`/`re_inter`/`re_union` chunk interiors.  Provable
by the chunk-invariant induction: `rFlat`'s chunks are `__re_rev_comp`
images of `__re_flatten true` output chunks, hence single-character
literals, opaque atoms, or false-normal combinator atoms — on those
the extra flatten is value-preserving chunkwise, and reversal
distributes over the chunk list on both sides.
-/
theorem StrInReConsumeInternal.eval_rev_flatten_rev_rflat_rel_local
    (M : SmtModel) (rSrc : Term)
    (hRFlatNe :
      __re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
        Term.Stuck)
    (nRv flatRv : SmtRegLan)
    (hNEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))) =
        SmtValue.RegLan nRv)
    (hFEval :
      __smtx_model_eval M
          (__eo_to_smt (__re_flatten (Term.Boolean true) rSrc)) =
        SmtValue.RegLan flatRv) :
    RuleProofs.smt_value_rel (SmtValue.RegLan nRv)
      (SmtValue.RegLan flatRv) := by
  have hFlatNe : __re_flatten (Term.Boolean true) rSrc ≠ Term.Stuck := by
    intro hBad
    apply hRFlatNe
    rw [hBad]
    exact StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local Term.Stuck _
      (by intro hh; cases hh) (by intro a b hh; cases hh)
  have hChain : StrInReConsumeInternal.consume_rev_flat_chain_local
      (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) :=
    StrInReConsumeInternal.consume_rev_flat_chain_rev_flatten_local rSrc
      (fun h => hRFlatNe h)
  have hInv :
      __re_rev_map_rev
          (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        __re_flatten (Term.Boolean true) rSrc :=
    StrInReConsumeInternal.re_flatten_true_action_double_eps_local rSrc hFlatNe
  have hPlainEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])))) =
        SmtValue.RegLan flatRv := by
    rw [hInv]
    exact hFEval
  exact (StrInReConsumeInternal.consume_core_rel_fuel_local M
      (sizeOf (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) + 1)
      _ (Nat.lt_succ_self _)).1 hChain nRv flatRv hNEval hPlainEval

/--
Threading of the rev-flat chain invariant through the consume
recursion: the residual regex of any consume step on an invariant
chain is again an invariant chain (a suffix chain or the rebuilt
input), or the membership extraction sticks.
-/
theorem StrInReConsumeInternal.consume_rev_flat_chain_memb_re_rec_local :
    ∀ s0 r0 fuel0 : Term,
      StrInReConsumeInternal.consume_rev_flat_chain_local r0 ->
      (StrInReConsumeInternal.consume_rev_flat_chain_local
          (__str_membership_re (__str_re_consume_rec s0 r0 fuel0)) ∨
        __str_membership_re (__str_re_consume_rec s0 r0 fuel0) =
          Term.Stuck) := by
  intro s0 r0 fuel0
  refine __str_re_consume_rec.induct
    (fun _ _ _ => True)
    (fun s r fuel =>
      StrInReConsumeInternal.consume_rev_flat_chain_local r ->
      (StrInReConsumeInternal.consume_rev_flat_chain_local
          (__str_membership_re (__str_re_consume_rec s r fuel)) ∨
        __str_membership_re (__str_re_consume_rec s r fuel) =
          Term.Stuck))
    (fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
  -- inter companion cases (motive1 = True)
  · intro x x1
    trivial
  · intro x x1 _
    trivial
  · intro s c1 fuel _ _ _
    trivial
  · intro s c1 c2 fuel _ _ _ _ _
    trivial
  · intro x x1 x2 _ _ _ _
    trivial
  -- rec: s stuck
  · intro r fuel
    intro _
    right
    rw [__str_re_consume_rec.eq_1]
    rfl
  -- rec: r stuck — impossible on chains
  · intro s fuel _hS
    intro hChain
    exact absurd rfl (StrInReConsumeInternal.consume_rev_flat_chain_ne_stuck_local hChain)
  -- rec: fuel stuck
  · intro s r hS hR
    intro _
    by_cases hV : __str_re_consume_rec s r Term.Stuck = Term.Stuck
    · right
      rw [hV]
      rfl
    · exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r
        (__str_re_consume_rec s r Term.Stuck) hS hR rfl hV
  -- eq_4: eps head, concat string
  · intro s1 s2 r2 fuel hFuel ih
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    rw [str_re_consume_rec_re_concat_empty_left_eq _ r2 fuel
      (by intro h; cases h) (fun h => hFuel h)]
    exact ih hParts.2
  -- eq_5: str_to_re head
  · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    by_cases hV : __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3)) r2)
        fuel = Term.Stuck
    · right
      rw [hV]
      rfl
    · rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel]
        at hV ⊢
      rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hE | hE
      · rw [hE, eo_ite_true]
        exact ih hParts.2
      · rw [hE, eo_ite_false] at hV ⊢
        rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hL | hL
        · rw [hL, eo_ite_true]
          right
          rfl
        · rw [hL, eo_ite_false]
          left
          exact hChain
  -- eq_6: range head
  · intro s1 s2 s3 s5 r2 fuel hFuel ih
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    by_cases hV : __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3)
              s5)) r2)
        fuel = Term.Stuck
    · right
      rw [hV]
      rfl
    · rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel]
        at hV ⊢
      rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hE | hE
      · rw [hE, eo_ite_true] at hV ⊢
        rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hM | hM
        · rw [hM, eo_ite_true]
          exact ih hParts.2
        · rw [hM, eo_ite_false]
          right
          rfl
      · rw [hE, eo_ite_false]
        left
        exact hChain
  -- eq_7: allchar head
  · intro s1 s2 r2 fuel hFuel ih
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    by_cases hV : __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.UOp UserOp.re_allchar)) r2)
        fuel = Term.Stuck
    · right
      rw [hV]
      rfl
    · rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] at hV ⊢
      rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hE | hE
      · rw [hE, eo_ite_true]
        exact ih hParts.2
      · rw [hE, eo_ite_false]
        left
        exact hChain
  -- eq_8: re_mult head with concat fuel
  · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
      _ihLeft ihRight _ihLeftAgain ihResidual
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    by_cases hV : __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr) =
        Term.Stuck
    · right
      rw [hV]
      rfl
    · rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr] at hV ⊢
      rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hE | hE
      · rw [hE, eo_ite_true]
        exact ihRight hParts.2
      · rw [hE, eo_ite_false] at hV ⊢
        rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hM | hM
        · rw [hM, eo_ite_true] at hV ⊢
          rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hRF | hRF
          · rw [hRF, eo_ite_true] at hV ⊢
            rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hSame | hSame
            · rw [hSame, eo_ite_true]
              left
              exact hChain
            · rw [hSame, eo_ite_false]
              exact ihResidual hChain
          · rw [hRF, eo_ite_false]
            left
            exact hChain
        · rw [hM, eo_ite_false]
          left
          exact hChain
  -- eq_9: re_mult head, non-concat fuel
  · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    intro hChain
    rw [__str_re_consume_rec.eq_9 fuel s1 s2 r3 r2 hFuel
      hNotFuelConcat]
    left
    exact hChain
  -- eq_10: generic concat head
  · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
      hR1Allchar hFuelMult hR1Mult _v0 _v1 _ihLeft _ihLeftAgain
      ihResidual
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    by_cases hV : __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel = Term.Stuck
    · right
      rw [hV]
      rfl
    · rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
        hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult]
        at hV ⊢
      rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hE | hE
      · rw [hE, eo_ite_true]
        right
        rfl
      · rw [hE, eo_ite_false] at hV ⊢
        rcases eo_ite_cases_of_ne_stuck _ _ _ hV with hM | hM
        · rw [hM, eo_ite_true]
          exact ihResidual hParts.2
        · rw [hM, eo_ite_false]
          left
          exact hChain
  -- eq_11: eps head, non-concat string
  · intro s r fuel hS hFuel _hNotConcat ih
    intro hChain
    have hParts := StrInReConsumeInternal.consume_rev_flat_chain_concat_parts_local hChain
    rw [str_re_consume_rec_re_concat_empty_left_eq s r fuel
      (fun h => hS h) (fun h => hFuel h)]
    exact ih hParts.2
  -- eq_12: inter dispatch — impossible on chains
  · intro s r1 r2 fuel hS hFuel _ih
    intro hChain
    exfalso
    simp [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local]
      at hChain
  -- eq_13: union dispatch — impossible on chains
  · intro s r1 r2 fuel hS hFuel _ih
    intro hChain
    exfalso
    simp [StrInReConsumeInternal.consume_rev_flat_chain_local, StrInReConsumeInternal.consume_rev_flat_local]
      at hChain
  -- default: rebuilt `str_in_re s r`
  · intro s r fuel hS hR hFuel hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
      hNotRConcatEmpty hNotRInter hNotRUnion
    intro hChain
    rw [str_re_consume_rec_default_eq s r fuel hS hR hFuel
      hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel]
    left
    exact hChain
  -- union companion cases (motive3 = True)
  · intro x x1
    trivial
  · intro x x1 _
    trivial
  · intro s c1 fuel _ _ _
    trivial
  · intro s c1 c2 fuel _ _ _ _ _
    trivial
  · intro x x1 x2 _ _ _ _
    trivial

theorem StrInReConsumeInternal.consume_smt_value_rel_boolean_inv_local
    {b : native_Bool} {Y : SmtValue}
    (h : RuleProofs.smt_value_rel (SmtValue.Boolean b) Y) :
    Y = SmtValue.Boolean b := by
  have h' : __smtx_model_eval_eq (SmtValue.Boolean b) Y =
      SmtValue.Boolean true := h
  have h2 : __smtx_model_eval_eq (SmtValue.Boolean b) Y =
      SmtValue.Boolean (native_veq (SmtValue.Boolean b) Y) := by
    cases Y <;> rfl
  rw [h2] at h'
  injection h' with h3
  have h4 : SmtValue.Boolean b = Y := by
    have h5 : decide (SmtValue.Boolean b = Y) = true := by
      simpa [native_veq] using h3
    exact of_decide_eq_true h5
  exact h4.symm

theorem StrInReConsumeInternal.consume_eval_unrev_pair_inv_local (M : SmtModel)
    (A B : Term) (b : native_Bool)
    (h : __smtx_model_eval M
        (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local A B)) =
      SmtValue.Boolean b) :
    ∃ (sv : SmtSeq) (rv : SmtRegLan),
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A)) =
        SmtValue.Seq sv ∧
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B)) =
        SmtValue.RegLan rv ∧
      b = Smtm.native_str_in_re (native_unpack_seq sv) rv := by
  simp only [StrInReConsumeInternal.consume_unrev_pair_local] at h
  change __smtx_model_eval M
      (SmtTerm.str_in_re
        (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A))
        (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B))) =
    SmtValue.Boolean b at h
  have h' : __smtx_model_eval_str_in_re
      (__smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A)))
      (__smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B))) =
      SmtValue.Boolean b := by
    rw [show __smtx_model_eval M
        (SmtTerm.str_in_re
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A))
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B))) =
      __smtx_model_eval_str_in_re
        (__smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A)))
        (__smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B))) from by
      simp [__smtx_model_eval]] at h
    exact h
  cases hA : __smtx_model_eval M
      (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local A)) with
  | Seq sv =>
      cases hB : __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local B)) with
      | RegLan rv =>
          rw [hA, hB] at h'
          have h2 : SmtValue.Boolean
              (Smtm.native_str_in_re (native_unpack_seq sv) rv) =
            SmtValue.Boolean b := h'
          injection h2 with h3
          exact ⟨sv, rv, rfl, rfl, h3.symm⟩
      | _ =>
          rw [hA, hB] at h'
          exact absurd h' (by simp [__smtx_model_eval_str_in_re])
  | _ =>
      rw [hA] at h'
      exact absurd h' (by simp [__smtx_model_eval_str_in_re])

/--
Value-level bridge between the unrev transform of the first pass's
residual regex (plain reversal) and the algorithm's second-pass
`nextR` (which re-flattens the residual before reversing).  The
residual `memb_re first` is a suffix structure of `rFlat`, so its
chunks satisfy the same invariant as in
`StrInReConsumeInternal.eval_rev_flatten_rev_rflat_rel_local` and the extra flatten is
value-preserving.
-/
theorem StrInReConsumeInternal.eval_first_residual_unrev_rel_local
    (M : SmtModel) (s rSrc : Term)
    (hRFlatNe :
      __re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
        Term.Stuck)
    (nRv mRv : SmtRegLan)
    (hNEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__str_membership_re
                  (__str_re_consume_rec
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (__str_flatten (__eo_list_singleton_intro
                        (Term.UOp UserOp.str_concat) s)))
                    (__re_rev_map_rev
                      (__re_flatten (Term.Boolean true) rSrc)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String [])))
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (__str_flatten (__eo_list_singleton_intro
                        (Term.UOp UserOp.str_concat) s))))))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))) =
        SmtValue.RegLan nRv)
    (hMEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_map_rev
              (__str_membership_re
                (__str_re_consume_rec
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) rSrc)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))) =
        SmtValue.RegLan mRv) :
    RuleProofs.smt_value_rel (SmtValue.RegLan nRv)
      (SmtValue.RegLan mRv) := by
  have hChainRFlat :=
    StrInReConsumeInternal.consume_rev_flat_chain_rev_flatten_local rSrc
      (fun h => hRFlatNe h)
  rcases StrInReConsumeInternal.consume_rev_flat_chain_memb_re_rec_local
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s)))
      (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s)))
      hChainRFlat with hChainM | hStuck
  · exact (StrInReConsumeInternal.consume_core_rel_fuel_local M _ _
      (Nat.lt_succ_self _)).1 hChainM nRv mRv hNEval hMEval
  · exfalso
    rw [hStuck] at hMEval
    rw [StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local Term.Stuck _
      (by intro hh; cases hh) (by intro a b hh; cases hh)] at hMEval
    exact StrInReConsumeInternal.consume_eval_stuck_not_reglan_local hMEval

/--
A `false` result of the consume certifies a definite mismatch at a
length-1 literal chunk, so the string value of the FORWARD input is
nonempty.  (Flat orientation; companion of the nonemptiness conjunct
of the unrev no-suffix motive.)
-/
def StrInReConsumeInternal.str_re_consume_rec_false_nonempty_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    side = Term.Boolean false ->
    ∀ ssF,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        native_unpack_string ssF ≠ []

/--
Combined string-side motive: a `false` result certifies a nonempty
FORWARD string value (the mismatch witness is a definite length-1
literal chunk), and any rebuildable result's residual string value is
a suffix of the input's string value.  The two conclusions are proven
together because the `re_mult` and generic-concat cases derive
nonemptiness of the input from nonemptiness of the residual of an
inner consume plus the suffix decomposition of that inner consume.
-/
def StrInReConsumeInternal.str_re_consume_rec_nonempty_decomp_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    (side = Term.Boolean false ->
      ∀ ssF,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
          native_unpack_string ssF ≠ []) ∧
    (__str_membership_str side ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      ∀ ssF ssR,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ssR ->
          ∃ u,
            native_unpack_string ssF =
              u ++ native_unpack_string ssR)

def StrInReConsumeInternal.str_re_consume_union_nonempty_decomp_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_union s r fuel ->
    (side = Term.Boolean false ->
      ∀ ssF,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
          native_unpack_string ssF ≠ []) ∧
    (__str_membership_str side ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      ∀ ssF ssR,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ssR ->
          ∃ u,
            native_unpack_string ssF =
              u ++ native_unpack_string ssR)

def StrInReConsumeInternal.str_re_consume_inter_nonempty_decomp_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_inter s r fuel ->
    (side = Term.Boolean false ->
      ∀ ssF,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
          native_unpack_string ssF ≠ []) ∧
    (__str_membership_str side ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      ∀ ssF ssR,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ssR ->
          ∃ u,
            native_unpack_string ssF =
              u ++ native_unpack_string ssR)

theorem StrInReConsumeInternal.str_re_consume_rec_false_left_ne_stuck_consume_local
    (a b fuel : Term)
    (h : __str_re_consume_rec a b fuel = Term.Boolean false) :
    a ≠ Term.Stuck := by
  intro hBad
  subst a
  exact str_re_consume_rec_stuck_left_absurd b fuel _ rfl (by
    rw [h]
    intro hh
    cases hh)

theorem StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local
    (t : Term)
    (h : __str_membership_str t ≠ Term.Stuck) :
    t ≠ Term.Stuck := by
  intro hBad
  subst t
  simp [__str_membership_str] at h

/--
Word-level chain evaluation with end-term transport: the value of an
atom chain unpacks to a fixed word `W` (the concatenation of the
chunk words) followed by the end term's word, for EVERY end term.
String-side companion of `StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local`.
-/
theorem StrInReConsumeInternal.eval_atom_chain_unpack_flatten_consume_local
    (M : SmtModel) :
    ∀ (atoms : List Term) (e : Term) (v : SmtSeq),
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_atom_chain_term atoms e)) =
        SmtValue.Seq v ->
      (∃ eV,
        __smtx_model_eval M (__eo_to_smt e) = SmtValue.Seq eV) ∧
      ∃ W : native_String,
        ∀ e2 eV2,
          __smtx_model_eval M (__eo_to_smt e2) = SmtValue.Seq eV2 ->
          ∃ v2,
            __smtx_model_eval M
                (__eo_to_smt (StrInReConsumeInternal.consume_atom_chain_term atoms e2)) =
              SmtValue.Seq v2 ∧
            native_unpack_string v2 =
              W ++ native_unpack_string eV2 := by
  intro atoms
  induction atoms with
  | nil =>
      intro e v hV
      refine ⟨⟨v, hV⟩, [], ?_⟩
      intro e2 eV2 h2
      exact ⟨eV2, h2, by simp⟩
  | cons a as ih =>
      intro e v hV
      rw [StrInReConsumeInternal.consume_atom_chain_cons] at hV
      rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M a
          (StrInReConsumeInternal.consume_atom_chain_term as e) v hV with
        ⟨sa, sy, hA, hY, _hUnp⟩
      rcases ih e sy hY with ⟨hE, W, hTrans⟩
      refine ⟨hE, native_unpack_string sa ++ W, ?_⟩
      intro e2 eV2 h2
      rcases hTrans e2 eV2 h2 with ⟨y2, hy2, hUnp2⟩
      refine ⟨native_pack_seq (__smtx_elem_typeof_seq_value sa)
        (native_seq_concat (native_unpack_seq sa)
          (native_unpack_seq y2)), ?_, ?_⟩
      · rw [StrInReConsumeInternal.consume_atom_chain_cons]
        change __smtx_model_eval M
            (SmtTerm.str_concat (__eo_to_smt a)
              (__eo_to_smt (StrInReConsumeInternal.consume_atom_chain_term as e2))) = _
        simp [__smtx_model_eval, __smtx_model_eval_str_concat, hA, hy2]
      · rw [native_unpack_string_pack_seq_concat_local _ sa y2, hUnp2,
          List.append_assoc]

theorem StrInReConsumeInternal.ne_false_of_eo_is_eq_false_consume_local
    (t : Term)
    (h : __eo_is_eq t (Term.Boolean false) = Term.Boolean false) :
    t ≠ Term.Boolean false := by
  intro hBad
  subst t
  simp [__eo_is_eq, native_teq, SmtEval.native_and,
    SmtEval.native_not] at h

/-- Trivial instance of the conjunct pair for a rebuilt fallback
`str_in_re s rAtom` result. -/
theorem StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local
    (M : SmtModel) (s rAtom side : Term)
    (hSide :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) rAtom)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    (side = Term.Boolean false ->
      ∀ ssF,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
          native_unpack_string ssF ≠ []) ∧
    (__str_membership_str side ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      ∀ ssF ssR,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ssR ->
          ∃ u,
            native_unpack_string ssF =
              u ++ native_unpack_string ssR) := by
  constructor
  · intro hFalse
    rw [hSide] at hFalse
    simp at hFalse
  · intro _hMemNe
    rw [hSide]
    simp only [__str_membership_str]
    refine ⟨hSTy, ?_⟩
    intro ssF ssR h1 h2
    injection h1.symm.trans h2 with h
    exact ⟨[], by rw [h]; simp⟩

/-- Trivial instance of the conjunct pair for a stuck result. -/
theorem StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_stuck_local
    (M : SmtModel) (s side : Term)
    (hSide : side = Term.Stuck) :
    (side = Term.Boolean false ->
      ∀ ssF,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
          native_unpack_string ssF ≠ []) ∧
    (__str_membership_str side ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
        SmtType.Seq SmtType.Char ∧
      ∀ ssF ssR,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ssF ->
        __smtx_model_eval M
            (__eo_to_smt (__str_membership_str side)) =
          SmtValue.Seq ssR ->
          ∃ u,
            native_unpack_string ssF =
              u ++ native_unpack_string ssR) := by
  constructor
  · intro hFalse
    rw [hSide] at hFalse
    cases hFalse
  · intro hMemNe
    exfalso
    apply hMemNe
    rw [hSide]
    simp [__str_membership_str]

theorem StrInReConsumeInternal.str_re_consume_rec_nonempty_decomp_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_nonempty_decomp_motive M s0 r0 fuel0 := by
  intro s0 r0 fuel0
  refine __str_re_consume_rec.induct
    (StrInReConsumeInternal.str_re_consume_inter_nonempty_decomp_motive M)
    (StrInReConsumeInternal.str_re_consume_rec_nonempty_decomp_motive M)
    (StrInReConsumeInternal.str_re_consume_union_nonempty_decomp_motive M)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
  rotate_left 5
  · intro r fuel side hSTy _hRTy _hSide
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hSTy
    cases hSTy
  · intro s fuel hS side _hSTy hRTy _hSide
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hRTy
    cases hRTy
  · intro s r hS hR side _hSTy _hRTy hSide
    constructor
    · intro hFalse
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro hMemNe
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
        (StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side
          hMemNe)
  · intro s1 s2 r2 fuel hFuel ih side hSTy hRTy hSide
    have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) r2
        hRTy).2
    have hEq :=
      str_re_consume_rec_re_concat_empty_left_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r2 fuel (by simp) hFuel
    exact ih side hSTy hR2Ty (hSide.trans hEq)
  · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih side hSTy hRTy hSide
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.str_to_re) s3) r2 hRTy).2
    rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel] at hSide
    constructor
    · intro hFalse ssF hSEvalF
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hCondT | hCondF
      · rw [hCondT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        have hTail := (ih (Term.Boolean false) hS2Ty hR2Ty
          hIteFalse.symm).1 rfl
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M s1 s2 ssF
            hSEvalF with ⟨sx, sy, _hx, hy, hUnp⟩
        rw [hUnp]
        exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ (hTail sy hy)
      · rw [hCondF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hLenT | hLenF
        · rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, _hS3Len⟩
          rcases str_re_consume_string_singleton_of_seq_type_len_one s1
              hS1Ty hS1Len with ⟨c, rfl⟩
          rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M _ s2 ssF
              hSEvalF with ⟨sx, sy, hx, _hy, hUnp⟩
          rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
            ⟨ss1, hss1, hUnp1⟩
          injection hss1.symm.trans hx with hEq1
          rw [hUnp, ← hEq1, hUnp1]
          simp
        · rw [hLenF] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          simp at hIteFalse
    · intro hMemNe
      have hSideNe :=
        StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side hMemNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hCondT | hCondF
      · have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
          rw [hSide, hCondT, eo_ite_true]
        rcases (ih side hS2Ty hR2Ty hSide2).2 hMemNe with ⟨hMemTy, hDec⟩
        refine ⟨hMemTy, ?_⟩
        intro ssF ssR hSEvalF hMemEval
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M s1 s2 ssF
            hSEvalF with ⟨sx, sy, _hx, hy, hUnp⟩
        rcases hDec sy ssR hy hMemEval with ⟨u, hU⟩
        exact ⟨native_unpack_string sx ++ u, by
          rw [hUnp, hU, List.append_assoc]⟩
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hCondF, eo_ite_false, hBad]) with hLenT | hLenF
        · exfalso
          apply hMemNe
          rw [show side = Term.Boolean false by
            rw [hSide, hCondF, eo_ite_false, hLenT, eo_ite_true]]
          simp [__str_membership_str]
        · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s3))
              r2)
            side
            (by rw [hSide, hCondF, eo_ite_false, hLenF, eo_ite_false])
            hSTy).2 hMemNe
  · intro s1 s2 s3 s5 r2 fuel hFuel ih side hSTy hRTy hSide
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5) r2
        hRTy).2
    rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel] at hSide
    constructor
    · intro hFalse ssF hSEvalF
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hLenT | hLenF
      · rw [hLenT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, _hRest⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hS1Len with ⟨c, rfl⟩
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M _ s2 ssF
            hSEvalF with ⟨sx, sy, hx, _hy, hUnp⟩
        rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
          ⟨ss1, hss1, hUnp1⟩
        injection hss1.symm.trans hx with hEq1
        rw [hUnp, ← hEq1, hUnp1]
        simp
      · rw [hLenF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        simp at hIteFalse
    · intro hMemNe
      have hSideNe :=
        StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side hMemNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLenT | hLenF
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hLenT, eo_ite_true, hBad]) with hMatchT | hMatchF
        · have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
            rw [hSide, hLenT, eo_ite_true, hMatchT, eo_ite_true]
          rcases (ih side hS2Ty hR2Ty hSide2).2 hMemNe with ⟨hMemTy, hDec⟩
          refine ⟨hMemTy, ?_⟩
          intro ssF ssR hSEvalF hMemEval
          rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M s1 s2 ssF
              hSEvalF with ⟨sx, sy, _hx, hy, hUnp⟩
          rcases hDec sy ssR hy hMemEval with ⟨u, hU⟩
          exact ⟨native_unpack_string sx ++ u, by
            rw [hUnp, hU, List.append_assoc]⟩
        · exfalso
          apply hMemNe
          rw [show side = Term.Boolean false by
            rw [hSide, hLenT, eo_ite_true, hMatchF, eo_ite_false]]
          simp [__str_membership_str]
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5))
            r2)
          side
          (by rw [hSide, hLenF, eo_ite_false])
          hSTy).2 hMemNe
  · intro s1 s2 r2 fuel hFuel ih side hSTy hRTy hSide
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.UOp UserOp.re_allchar) r2 hRTy).2
    rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] at hSide
    constructor
    · intro hFalse ssF hSEvalF
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hCondT | hCondF
      · rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hCondT with ⟨c, rfl⟩
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M _ s2 ssF
            hSEvalF with ⟨sx, sy, hx, _hy, hUnp⟩
        rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
          ⟨ss1, hss1, hUnp1⟩
        injection hss1.symm.trans hx with hEq1
        rw [hUnp, ← hEq1, hUnp1]
        simp
      · rw [hCondF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        simp at hIteFalse
    · intro hMemNe
      have hSideNe :=
        StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side hMemNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hCondT | hCondF
      · have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
          rw [hSide, hCondT, eo_ite_true]
        rcases (ih side hS2Ty hR2Ty hSide2).2 hMemNe with ⟨hMemTy, hDec⟩
        refine ⟨hMemTy, ?_⟩
        intro ssF ssR hSEvalF hMemEval
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M s1 s2 ssF
            hSEvalF with ⟨sx, sy, _hx, hy, hUnp⟩
        rcases hDec sy ssR hy hMemEval with ⟨u, hU⟩
        exact ⟨native_unpack_string sx ++ u, by
          rw [hUnp, hU, List.append_assoc]⟩
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.UOp UserOp.re_allchar))
            r2)
          side
          (by rw [hSide, hCondF, eo_ite_false])
          hSTy).2 hMemNe
  · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
      ihLeft ihRight _ihLeftAgain ihResidual side hSTy hRTy hSide
    have hArgs :=
      StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 hRTy
    have hR3Ty : __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
      StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local r3 hArgs.1
    rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr] at hSide
    have hResolve :
        side ≠ Term.Stuck ->
        (side =
            __str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2)
              r2
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc)
                fr) ∨
          side =
            __str_re_consume_rec
              (__str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r3
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2)
              fr ∨
          side =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                  s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                r2)) := by
      intro hSideNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLF | hLF
      · exact Or.inl (by rw [hSide, hLF, eo_ite_true])
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hLF, eo_ite_false, hBad]) with hMem | hMem
        · rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                intro hBad
                apply hSideNe
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hBad])
              with hRF | hRF
          · rcases eo_ite_cases_of_ne_stuck _ _ _
                (by
                  intro hBad
                  apply hSideNe
                  rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                    eo_ite_true, hBad]) with hSame | hSame
            · exact Or.inr (Or.inr (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_true, hSame, eo_ite_true]))
            · exact Or.inr (Or.inl (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_true, hSame, eo_ite_false]))
          · exact Or.inr (Or.inr (by
              rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                eo_ite_false]))
        · exact Or.inr (Or.inr (by
            rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false]))
    constructor
    · intro hFalse ssF hSEvalF
      rcases hResolve (by
          rw [hFalse]
          intro h
          cases h) with hRt | hRes | hFb
      · exact (ihRight side hSTy hArgs.2 hRt).1 hFalse ssF hSEvalF
      · have hResidFalse := hRes.symm.trans hFalse
        have hMemLeftNe :=
          StrInReConsumeInternal.str_re_consume_rec_false_left_ne_stuck_consume_local _ _ _
            hResidFalse
        rcases (ihLeft _ hSTy hR3Ty rfl).2 hMemLeftNe with
          ⟨h5Ty, hDecL⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            _ h5Ty with ⟨ss5, hSs5⟩
        have hNe5 := (ihResidual (Term.Boolean false) h5Ty hRTy
          hResidFalse.symm).1 rfl ss5 hSs5
        rcases hDecL ssF ss5 hSEvalF hSs5 with ⟨u, hU⟩
        rw [hU]
        exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ hNe5
      · rw [hFb] at hFalse
        simp at hFalse
    · intro hMemNe
      have hSideNe :=
        StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side hMemNe
      rcases hResolve hSideNe with hRt | hRes | hFb
      · exact (ihRight side hSTy hArgs.2 hRt).2 hMemNe
      · have hMemLeftNe :
            __str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r3
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) fc) fr)) ≠
              Term.Stuck := by
          intro hBad
          rw [hBad] at hRes
          exact str_re_consume_rec_stuck_left_absurd _ _ _ hRes hSideNe
        rcases (ihLeft _ hSTy hR3Ty rfl).2 hMemLeftNe with
          ⟨h5Ty, hDecL⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            _ h5Ty with ⟨ss5, hSs5⟩
        rcases (ihResidual side h5Ty hRTy hRes).2 hMemNe with
          ⟨hMemTy, hDecR⟩
        refine ⟨hMemTy, ?_⟩
        intro ssF ssR hSEvalF hMemEval
        rcases hDecL ssF ss5 hSEvalF hSs5 with ⟨u1, hU1⟩
        rcases hDecR ss5 ssR hSs5 hMemEval with ⟨u2, hU2⟩
        exact ⟨u1 ++ u2, by rw [hU1, hU2, List.append_assoc]⟩
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3))
            r2)
          side hFb hSTy).2 hMemNe
  · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat side hSTy _hRTy hSide
    have hEq :=
      str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
        s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    exact StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M _ _ side
      (hSide.trans hEq) hSTy
  rotate_left
  · intro s r fuel hS hFuel _hNotConcat ih side hSTy hRTy hSide
    have hArgs :=
      StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) r hRTy
    have hEq :=
      str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel
    exact ih side hSTy hArgs.2 (hSide.trans hEq)
  · intro s r1 r2 fuel hS hFuel ih side hSTy hRTy hSide
    have hEq := str_re_consume_rec_re_inter_eq s r1 r2 fuel hS hFuel
    exact ih side hSTy hRTy (hSide.trans hEq)
  · intro s r1 r2 fuel hS hFuel ih side hSTy hRTy hSide
    have hEq := str_re_consume_rec_re_union_eq s r1 r2 fuel hS hFuel
    exact ih side hSTy hRTy (hSide.trans hEq)
  · intro s r fuel hS hR hFuel hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
      hNotRConcatEmpty hNotRInter hNotRUnion side hSTy _hRTy hSide
    have hEq :=
      str_re_consume_rec_default_eq s r fuel hS hR hFuel
        hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
        hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
        hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel
    exact StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M s r side
      (hSide.trans hEq) hSTy
  · intro r fuel side hSTy _hRTy _hSide
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hSTy
    cases hSTy
  · intro s r hS side _hSTy _hRTy hSide
    constructor
    · intro hFalse
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r side hS hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro hMemNe
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r side hS hSide
        (StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side
          hMemNe)
  rotate_left
  rotate_left
  · intro s r fuel hS hFuel hNotNone hNotUnion side _hSTy _hRTy hSide
    have hEq := str_re_consume_union_default_eq s r fuel hS hFuel
      hNotNone hNotUnion
    exact StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_stuck_local M s side
      (hSide.trans hEq)
  · intro r fuel side hSTy _hRTy _hSide
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hSTy
    cases hSTy
  · intro s r hS side _hSTy _hRTy hSide
    constructor
    · intro hFalse
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r side hS hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro hMemNe
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r side hS hSide
        (StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side
          hMemNe)
  rotate_left
  rotate_left
  · intro s r fuel hS hFuel hNotAll hNotInter side _hSTy _hRTy hSide
    have hEq := str_re_consume_inter_default_eq s r fuel hS hFuel
      hNotAll hNotInter
    exact StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_stuck_local M s side
      (hSide.trans hEq)
  rotate_left
  · intro s r fuel hS hFuel ih side hSTy hRTy hSide
    have hArgs := StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local r
      (Term.UOp UserOp.re_none) hRTy
    have hEq := str_re_consume_union_re_none_eq s r fuel hS hFuel
    exact ih side hSTy hArgs.1 (hSide.trans hEq)
  rotate_left
  · intro s r fuel hS hFuel ih side hSTy hRTy hSide
    have hArgs := StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local r
      (Term.UOp UserOp.re_all) hRTy
    have hEq := str_re_consume_inter_re_all_eq s r fuel hS hFuel
    exact ih side hSTy hArgs.1 (hSide.trans hEq)
  rotate_left
  · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
      hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
      ihResidual side hSTy hRTy hSide
    have hArgs := StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy
    rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
      hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult] at hSide
    have hResolve :
        side ≠ Term.Stuck ->
        ((__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2)
              r1 fuel = Term.Boolean false ∧
            side = Term.Boolean false) ∨
          side =
            __str_re_consume_rec
              (__str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel))
              r2 fuel ∨
          side =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                  s2))
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1)
                r2)) := by
      intro hSideNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLF | hLF
      · exact Or.inl ⟨eq_of_eo_is_eq_true_consume_local _ _ hLF,
          by rw [hSide, hLF, eo_ite_true]⟩
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hLF, eo_ite_false, hBad]) with hMem | hMem
        · exact Or.inr (Or.inl (by
            rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true]))
        · exact Or.inr (Or.inr (by
            rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false]))
    constructor
    · intro hFalse ssF hSEvalF
      rcases hResolve (by
          rw [hFalse]
          intro h
          cases h) with ⟨hLFalse, _⟩ | hRes | hFb
      · exact (ihLeft (Term.Boolean false) hSTy hArgs.1
          hLFalse.symm).1 rfl ssF hSEvalF
      · have hResidFalse := hRes.symm.trans hFalse
        have hMemLeftNe :=
          StrInReConsumeInternal.str_re_consume_rec_false_left_ne_stuck_consume_local _ _ _
            hResidFalse
        rcases (ihLeft _ hSTy hArgs.1 rfl).2 hMemLeftNe with
          ⟨h5Ty, hDecL⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            _ h5Ty with ⟨ss5, hSs5⟩
        have hNe5 := (ihResidual (Term.Boolean false) h5Ty hArgs.2
          hResidFalse.symm).1 rfl ss5 hSs5
        rcases hDecL ssF ss5 hSEvalF hSs5 with ⟨u, hU⟩
        rw [hU]
        exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ hNe5
      · rw [hFb] at hFalse
        simp at hFalse
    · intro hMemNe
      have hSideNe :=
        StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side hMemNe
      rcases hResolve hSideNe with ⟨_, hSideF⟩ | hRes | hFb
      · exfalso
        apply hMemNe
        rw [hSideF]
        simp [__str_membership_str]
      · have hMemLeftNe :
            __str_membership_str
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hRes
          exact str_re_consume_rec_stuck_left_absurd _ _ _ hRes hSideNe
        rcases (ihLeft _ hSTy hArgs.1 rfl).2 hMemLeftNe with
          ⟨h5Ty, hDecL⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            _ h5Ty with ⟨ss5, hSs5⟩
        rcases (ihResidual side h5Ty hArgs.2 hRes).2 hMemNe with
          ⟨hMemTy, hDecR⟩
        refine ⟨hMemTy, ?_⟩
        intro ssF ssR hSEvalF hMemEval
        rcases hDecL ssF ss5 hSEvalF hSs5 with ⟨u1, hU1⟩
        rcases hDecR ss5 ssR hSs5 hMemEval with ⟨u2, hU2⟩
        exact ⟨u1 ++ u2, by rw [hU1, hU2, List.append_assoc]⟩
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
          side hFb hSTy).2 hMemNe
  · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight side hSTy hRTy
      hSide
    have hArgs := StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hRTy
    rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel] at hSide
    have hResolve :
        side ≠ Term.Stuck ->
        (side = __str_re_consume_rec s c1 fuel ∨
          side = __str_re_consume_union s c2 fuel ∨
          side =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
                c2)) := by
      intro hSideNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLF | hLF
      · exact Or.inr (Or.inl (by rw [hSide, hLF, eo_ite_true]))
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hLF, eo_ite_false, hBad]) with hMem | hMem
        · rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                intro hBad
                apply hSideNe
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hBad])
              with hRF | hRF
          · exact Or.inl (by
              rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                eo_ite_true])
          · rcases eo_ite_cases_of_ne_stuck _ _ _
                (by
                  intro hBad
                  apply hSideNe
                  rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                    eo_ite_false, hBad]) with hSame | hSame
            · exact Or.inl (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_false, hSame, eo_ite_true])
            · exact Or.inr (Or.inr (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_false, hSame, eo_ite_false]))
        · exact Or.inr (Or.inr (by
            rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false]))
    constructor
    · intro hFalse ssF hSEvalF
      rcases hResolve (by
          rw [hFalse]
          intro h
          cases h) with hL | hR | hFb
      · exact (ihLeft side hSTy hArgs.1 hL).1 hFalse ssF hSEvalF
      · exact (ihRight side hSTy hArgs.2 hR).1 hFalse ssF hSEvalF
      · rw [hFb] at hFalse
        simp at hFalse
    · intro hMemNe
      rcases hResolve
          (StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side
            hMemNe) with hL | hR | hFb
      · exact (ihLeft side hSTy hArgs.1 hL).2 hMemNe
      · exact (ihRight side hSTy hArgs.2 hR).2 hMemNe
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M s _
          side hFb hSTy).2 hMemNe
  · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight side hSTy hRTy
      hSide
    have hArgs := StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hRTy
    rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel] at hSide
    have hResolve :
        side ≠ Term.Stuck ->
        ((__str_re_consume_rec s c1 fuel = Term.Boolean false ∧
            side = Term.Boolean false) ∨
          (__str_re_consume_inter s c2 fuel = Term.Boolean false ∧
            side = Term.Boolean false) ∨
          side = __str_re_consume_rec s c1 fuel ∨
          side =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                c2)) := by
      intro hSideNe
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLF | hLF
      · exact Or.inl ⟨eq_of_eo_is_eq_true_consume_local _ _ hLF,
          by rw [hSide, hLF, eo_ite_true]⟩
      · rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              intro hBad
              apply hSideNe
              rw [hSide, hLF, eo_ite_false, hBad]) with hMem | hMem
        · rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                intro hBad
                apply hSideNe
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hBad])
              with hRF | hRF
          · exact Or.inr (Or.inl
              ⟨eq_of_eo_is_eq_true_consume_local _ _ hRF,
                by
                  rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                    eo_ite_true]⟩)
          · rcases eo_ite_cases_of_ne_stuck _ _ _
                (by
                  intro hBad
                  apply hSideNe
                  rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                    eo_ite_false, hBad]) with hSame | hSame
            · exact Or.inr (Or.inr (Or.inl (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_false, hSame, eo_ite_true])))
            · exact Or.inr (Or.inr (Or.inr (by
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_true, hRF,
                  eo_ite_false, hSame, eo_ite_false])))
        · rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                intro hBad
                apply hSideNe
                rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false, hBad])
              with hRF | hRF
          · exact Or.inr (Or.inl
              ⟨eq_of_eo_is_eq_true_consume_local _ _ hRF,
                by
                  rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false, hRF,
                    eo_ite_true]⟩)
          · exact Or.inr (Or.inr (Or.inr (by
              rw [hSide, hLF, eo_ite_false, hMem, eo_ite_false, hRF,
                eo_ite_false])))
    constructor
    · intro hFalse ssF hSEvalF
      rcases hResolve (by
          rw [hFalse]
          intro h
          cases h) with ⟨hLFalse, _⟩ | ⟨hRFalse, _⟩ | hL | hFb
      · exact (ihRight (Term.Boolean false) hSTy hArgs.1
          hLFalse.symm).1 rfl ssF hSEvalF
      · exact (ihLeft (Term.Boolean false) hSTy hArgs.2
          hRFalse.symm).1 rfl ssF hSEvalF
      · exact (ihRight side hSTy hArgs.1 hL).1 hFalse ssF hSEvalF
      · rw [hFb] at hFalse
        simp at hFalse
    · intro hMemNe
      rcases hResolve
          (StrInReConsumeInternal.str_membership_str_ne_stuck_imp_ne_stuck_consume_local side
            hMemNe) with ⟨_, hSideF⟩ | ⟨_, hSideF⟩ | hL | hFb
      · exfalso
        apply hMemNe
        rw [hSideF]
        simp [__str_membership_str]
      · exfalso
        apply hMemNe
        rw [hSideF]
        simp [__str_membership_str]
      · exact (ihRight side hSTy hArgs.1 hL).2 hMemNe
      · exact (StrInReConsumeInternal.str_re_consume_nonempty_decomp_of_fallback_local M s _
          side hFb hSTy).2 hMemNe

theorem StrInReConsumeInternal.str_re_consume_rec_false_nonempty_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_false_nonempty_motive M s0 r0 fuel0 := by
  intro s0 r0 fuel0 side hSTy hRTy hSide hFalse ssF hEval
  exact (StrInReConsumeInternal.str_re_consume_rec_nonempty_decomp_local M hM s0 r0 fuel0
    side hSTy hRTy hSide).1 hFalse ssF hEval

/--
A nonempty word with no suffix in `r` is not in `(r)*`.
-/
theorem StrInReConsumeInternal.native_str_in_re_star_false_of_no_suffix_local
    (w : native_String) (r : SmtRegLan)
    (hNe : w ≠ [])
    (hNoSuffix :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf r = false) :
    native_str_in_re w (native_re_mult r) = false := by
  cases hMem : native_str_in_re w (native_re_mult r) with
  | false => rfl
  | true =>
      exfalso
      rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_local w r hMem hNe with
        ⟨pre, suf, hAppend, _hSufNe, hSufMem⟩
      have hFalse := hNoSuffix pre suf hAppend
      rw [hSufMem] at hFalse
      cases hFalse

/--
A nonempty word with no prefix in `r` is not in `(r)*`.
-/
theorem StrInReConsumeInternal.native_str_in_re_star_false_of_no_prefix_consume_local
    (w : native_String) (r : SmtRegLan)
    (hNe : w ≠ [])
    (hNoPrefix :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re pre r = false) :
    native_str_in_re w (native_re_mult r) = false := by
  cases hMem : native_str_in_re w (native_re_mult r) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid w = true := by
        cases h : native_string_valid w with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe w (native_re_mult r) = true := by
        simpa [native_str_in_re, hValid] using hMem
      rcases nativeListInRe_re_mult_nonempty_prefix_local w r hListMem
          hNe with
        ⟨pre, suf, hAppend, _hPreNe, hPreMem⟩
      have hPreValid : native_string_valid pre = true :=
        native_string_valid_append_left pre suf (by
          rw [hAppend]
          exact hValid)
      have hPreStrMem : native_str_in_re pre r = true := by
        simpa [native_str_in_re, hPreValid] using hPreMem
      rw [hNoPrefix pre suf hAppend] at hPreStrMem
      cases hPreStrMem

theorem StrInReConsumeInternal.eo_and_false_left_ne_true_consume_local
    (t : Term) :
    __eo_and (Term.Boolean false) t ≠ Term.Boolean true := by
  cases t <;> simp [__eo_and, SmtEval.native_and]

theorem StrInReConsumeInternal.eo_and_boolean_arg_boolean_consume_local
    (b c : native_Bool) (t : Term)
    (h : __eo_and (Term.Boolean b) t = Term.Boolean c) :
    ∃ d, t = Term.Boolean d := by
  cases t <;> simp [__eo_and] at h
  exact ⟨_, rfl⟩

theorem StrInReConsumeInternal.eo_not_boolean_arg_boolean_consume_local
    (b : native_Bool) (t : Term)
    (h : __eo_not t = Term.Boolean b) :
    ∃ c, t = Term.Boolean c := by
  cases t <;> simp [__eo_not] at h
  exact ⟨_, rfl⟩

theorem StrInReConsumeInternal.eo_eq_boolean_args_ne_stuck_consume_local
    (b : native_Bool) (x y : Term)
    (h : __eo_eq x y = Term.Boolean b) :
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck := by
  constructor
  · intro hBad
    subst x
    simp [__eo_eq] at h
  · intro hBad
    subst y
    cases x <;> simp [__eo_eq] at h

theorem StrInReConsumeInternal.str_membership_re_ne_stuck_imp_ne_stuck_consume_local
    (t : Term)
    (h : __str_membership_re t ≠ Term.Stuck) :
    t ≠ Term.Stuck := by
  intro hBad
  subst t
  simp [__str_membership_re] at h

theorem StrInReConsumeInternal.eo_eq_eq_of_ne_stuck_consume_local
    (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_eq x y = Term.Boolean (native_teq y x) := by
  unfold __eo_eq
  split
  · exact absurd rfl hx
  · exact absurd rfl hy
  · rfl

theorem StrInReConsumeInternal.consume_seq_valid_of_eval_typeof_local
    (M : SmtModel) (hM : model_wf M) (T : SmtTerm) (ss : SmtSeq)
    (hEval : __smtx_model_eval M T = SmtValue.Seq ss)
    (hTy : __smtx_typeof T = SmtType.Seq SmtType.Char) :
    native_string_valid (native_unpack_string ss) = true := by
  have hVal := smt_model_eval_preserves_type_of_non_none M hM T (by
    unfold term_has_non_none_type
    rw [hTy]
    simp)
  rw [hEval, hTy] at hVal
  exact native_unpack_string_valid_of_typeof_seq_char hVal

theorem StrInReConsumeInternal.consume_eval_re_all_local (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all)) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M SmtTerm.re_all = _
  simp [__smtx_model_eval]

theorem StrInReConsumeInternal.consume_str_in_re_concat_intro_local
    (x1 x2 : native_String) (r s : SmtRegLan)
    (hV : native_string_valid (x1 ++ x2) = true)
    (h1 : native_str_in_re x1 r = true)
    (h2 : native_str_in_re x2 s = true) :
    native_str_in_re (x1 ++ x2) (native_re_concat r s) = true := by
  have hV1 : native_string_valid x1 = true :=
    native_string_valid_append_left _ _ hV
  have hV2 : native_string_valid x2 = true :=
    native_string_valid_append_right _ _ hV
  have hL1 : nativeListInRe x1 r = true := by
    simpa [native_str_in_re, nativeListInRe, hV1] using h1
  have hL2 : nativeListInRe x2 s = true := by
    simpa [native_str_in_re, nativeListInRe, hV2] using h2
  have hL : nativeListInRe (x1 ++ x2) (native_re_mk_concat r s) =
      true :=
    (nativeListInRe_mk_concat_true_iff_exists_append (x1 ++ x2) r
      s).2 ⟨x1, x2, rfl, hL1, hL2⟩
  have hsimpa := hL
  try simp [native_str_in_re, hV, native_re_concat] at hsimpa ⊢
  exact hsimpa

theorem StrInReConsumeInternal.consume_str_in_re_concat_elim_local
    (w : native_String) (r s : SmtRegLan)
    (hV : native_string_valid w = true)
    (h : native_str_in_re w (native_re_concat r s) = true) :
    ∃ x1 x2 : native_String,
      x1 ++ x2 = w ∧ native_str_in_re x1 r = true ∧
        native_str_in_re x2 s = true := by
  have hL : nativeListInRe w (native_re_mk_concat r s) = true := by
    have hsimpa := h
    try simp [native_str_in_re, hV, native_re_concat] at hsimpa ⊢
    exact hsimpa
  rcases (nativeListInRe_mk_concat_true_iff_exists_append w r s).1 hL
    with ⟨x1, x2, hApp, hL1, hL2⟩
  subst hApp
  have hV1 : native_string_valid x1 = true :=
    native_string_valid_append_left _ _ hV
  have hV2 : native_string_valid x2 = true :=
    native_string_valid_append_right _ _ hV
  exact ⟨x1, x2, rfl,
    by simpa [native_str_in_re, nativeListInRe, hV1] using hL1,
    by simpa [native_str_in_re, nativeListInRe, hV2] using hL2⟩

/--
`w ∈ A* = w ∈ A*·B` when the pointwise language of `B` is that of `A`
and `w` decomposes as `wPre ++ u` with `u ∈ B` (covering the empty
word).
-/
theorem StrInReConsumeInternal.consume_star_concat_right_eq_local
    (w wPre u : native_String) (A B : SmtRegLan)
    (hWValid : native_string_valid w = true)
    (hPtwise : ∀ str, native_str_in_re str B = native_str_in_re str A)
    (hDecomp : w = wPre ++ u)
    (hUMem : native_str_in_re u B = true) :
    native_str_in_re w (native_re_mult A) =
      native_str_in_re w (native_re_concat (native_re_mult A) B) := by
  cases hL : native_str_in_re w (native_re_mult A) with
  | true =>
      by_cases hWNil : w = []
      · subst hWNil
        have hU : u = [] := (List.append_eq_nil_iff.mp hDecomp.symm).2
        subst hU
        symm
        exact StrInReConsumeInternal.consume_str_in_re_concat_intro_local [] [] _ _
          (by simpa using hWValid)
          (native_str_in_re_re_mult_empty_local A) hUMem
      · rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local w A hL
            hWNil with ⟨pre, suf, hApp, _hSufNe, hPre, hSuf⟩
        symm
        rw [← hApp]
        exact StrInReConsumeInternal.consume_str_in_re_concat_intro_local pre suf _ _
          (by rw [hApp]; exact hWValid) hPre
          (by rw [hPtwise]; exact hSuf)
  | false =>
      cases hR : native_str_in_re w
          (native_re_concat (native_re_mult A) B) with
      | false => rfl
      | true =>
          exfalso
          rcases StrInReConsumeInternal.consume_str_in_re_concat_elim_local w _ _ hWValid hR
            with ⟨x1, x2, hApp, hX1, hX2⟩
          have hX2A : native_str_in_re x2 A = true := by
            rw [← hPtwise]
            exact hX2
          have hW : native_str_in_re (x1 ++ x2)
              (native_re_mult A) = true :=
            StrInReConsumeInternal.native_str_in_re_star_append_local x1 x2 A hX1 hX2A
          rw [hApp] at hW
          rw [hW] at hL
          cases hL

/--
`w ∈ A* = w ∈ B·A*` when the pointwise language of `B` is that of `A`
and the empty word is in `B` whenever `w` is empty.
-/
theorem StrInReConsumeInternal.consume_star_concat_left_eq_local
    (w : native_String) (A B : SmtRegLan)
    (hWValid : native_string_valid w = true)
    (hPtwise : ∀ str, native_str_in_re str B = native_str_in_re str A)
    (hEpsB : w = [] -> native_str_in_re [] B = true) :
    native_str_in_re w (native_re_mult A) =
      native_str_in_re w (native_re_concat B (native_re_mult A)) := by
  cases hL : native_str_in_re w (native_re_mult A) with
  | true =>
      by_cases hWNil : w = []
      · subst hWNil
        symm
        exact StrInReConsumeInternal.consume_str_in_re_concat_intro_local [] [] _ _
          (by simpa using hWValid) (hEpsB rfl)
          (native_str_in_re_re_mult_empty_local A)
      · have hLL : nativeListInRe w (native_re_mult A) = true := by
          simpa [native_str_in_re, nativeListInRe, hWValid] using hL
        rcases nativeListInRe_re_mult_nonempty_prefix_decomp_local w A
            hLL hWNil with ⟨pre, suf, hApp, _hPreNe, hPreL, hSufL⟩
        have hWValid' : native_string_valid (pre ++ suf) = true := by
          rw [hApp]
          exact hWValid
        have hVpre : native_string_valid pre = true :=
          native_string_valid_append_left _ _ hWValid'
        have hVsuf : native_string_valid suf = true :=
          native_string_valid_append_right _ _ hWValid'
        have hPre : native_str_in_re pre A = true := by
          simpa [native_str_in_re, nativeListInRe, hVpre] using hPreL
        have hSuf : native_str_in_re suf (native_re_mult A) = true := by
          simpa [native_str_in_re, nativeListInRe, hVsuf] using hSufL
        symm
        rw [← hApp]
        exact StrInReConsumeInternal.consume_str_in_re_concat_intro_local pre suf _ _
          hWValid' (by rw [hPtwise]; exact hPre) hSuf
  | false =>
      cases hR : native_str_in_re w
          (native_re_concat B (native_re_mult A)) with
      | false => rfl
      | true =>
          exfalso
          rcases StrInReConsumeInternal.consume_str_in_re_concat_elim_local w _ _ hWValid hR
            with ⟨x1, x2, hApp, hX1, hX2⟩
          have hX1A : native_str_in_re x1 A = true := by
            rw [← hPtwise]
            exact hX1
          have hValid12 : native_string_valid (x1 ++ x2) = true := by
            rw [hApp]
            exact hWValid
          have hIn : native_str_in_re (x1 ++ x2)
              (native_re_concat A
                (native_re_concat (native_re_mult A)
                  (native_str_to_re []))) = true := by
            rw [StrInReConsumeInternal.consume_re_concat_eps_right_local]
            exact StrInReConsumeInternal.consume_str_in_re_concat_intro_local x1 x2 _ _
              hValid12 hX1A hX2
          have hIn2 := native_str_in_re_re_mult_concat_cons_local
            (x1 ++ x2) A (native_str_to_re []) hIn
          rw [StrInReConsumeInternal.consume_re_concat_eps_right_local] at hIn2
          rw [hApp] at hIn2
          rw [hIn2] at hL
          cases hL

end RuleProofs
