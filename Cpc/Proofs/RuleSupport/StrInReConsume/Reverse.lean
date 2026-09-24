module

public import Cpc.Proofs.RuleSupport.StrInReConsume.Forward
import all Cpc.Proofs.RuleSupport.StrInReConsume.Forward

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

def StrInReConsumeInternal.consume_unrev_str_local (t : Term) : Term :=
  __eo_list_rev (Term.UOp UserOp.str_concat) t

/--
NOTE: no inner `__re_flatten` here.  Two earlier candidate designs are
unusable:
* re-flattening inside the transform makes the transform of `rFlat`
  potentially stuck even though the whole pipeline succeeded
  (`__str_flatten (__eo_list_singleton_intro str_concat c)` calls
  `__eo_typeof c` on opaque chunks `c` that the first pass never
  typed), so the motives' typing hypotheses would be undischargeable;
* `__re_flatten true` is NOT the identity on
  `__re_rev_map_rev (__re_flatten true r) eps` outputs: `__str_flatten`
  keeps `seq_empty` atoms as chunks and the second flatten DROPS the
  resulting `str_to_re (seq_empty _)` chunks (value-preserving but not
  syntax-preserving), so a syntactic idempotence lemma is false.
With the plain reversal, the transform of `rFlat` is `__re_flatten
true r` by the proven involution
`StrInReConsumeInternal.re_flatten_true_action_double_eps_local`, and the residual mismatch
against the algorithm's re-flattened second pass is bridged by the
value-level lemmas below
(`StrInReConsumeInternal.eval_rev_flatten_rev_rflat_rel_local`,
`StrInReConsumeInternal.eval_first_residual_unrev_rel_local`).
-/
def StrInReConsumeInternal.consume_unrev_re_local (t : Term) : Term :=
  __re_rev_map_rev t
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))

def StrInReConsumeInternal.consume_unrev_pair_local (a b : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_in_re) (StrInReConsumeInternal.consume_unrev_str_local a))
    (StrInReConsumeInternal.consume_unrev_re_local b)

/--
Well-formedness of consume regexes, by position flag:
`0` = CHUNK position (must not be a raw `re_concat` — the unrev
transform's `__re_rev_comp` leaves those unreversed, breaking the
reversal semantics; the checker itself was fixed to never produce
them, but the induction motives quantify over all terms — and the
body of a `re_mult` chunk / the left components of `re_inter`/
`re_union` chunks must recursively be well-formed chains);
`1`/`2` = `re_inter`/`re_union` TAIL positions (permissive on
non-tree terms because the companion consume functions get stuck
there, making all motive conclusions vacuous);
`3` = CHAIN position (every chunk along the `re_concat` right spine
is a well-formed chunk; degenerates to chunk well-formedness on
non-`re_concat` terms, since the rec function also receives bare
chunks and `re_inter`/`re_union` trees directly).
-/
def StrInReConsumeInternal.consume_wf_local : Nat -> Term -> Prop
  | 3, Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b =>
      StrInReConsumeInternal.consume_wf_local 0 a ∧ StrInReConsumeInternal.consume_wf_local 3 b
  | 3, t => StrInReConsumeInternal.consume_wf_local 0 t
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) _) _ => False
  | 0, Term.Apply (Term.UOp UserOp.re_mult) body =>
      StrInReConsumeInternal.consume_wf_local 3 body
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =>
      StrInReConsumeInternal.consume_wf_local 3 c1 ∧ StrInReConsumeInternal.consume_wf_local 1 c2
  | 0, Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =>
      StrInReConsumeInternal.consume_wf_local 3 c1 ∧ StrInReConsumeInternal.consume_wf_local 2 c2
  | 1, Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2 =>
      StrInReConsumeInternal.consume_wf_local 3 c1 ∧ StrInReConsumeInternal.consume_wf_local 1 c2
  | 2, Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2 =>
      StrInReConsumeInternal.consume_wf_local 3 c1 ∧ StrInReConsumeInternal.consume_wf_local 2 c2
  | _, _ => True
termination_by flag t => (sizeOf t, flag)

abbrev StrInReConsumeInternal.consume_wf_chunk_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_wf_local 0 t
abbrev StrInReConsumeInternal.consume_wf_inter_tail_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_wf_local 1 t
abbrev StrInReConsumeInternal.consume_wf_union_tail_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_wf_local 2 t
abbrev StrInReConsumeInternal.consume_wf_chain_local (t : Term) : Prop :=
  StrInReConsumeInternal.consume_wf_local 3 t

theorem StrInReConsumeInternal.consume_wf_chain_concat_parts_local {a b : Term}
    (h : StrInReConsumeInternal.consume_wf_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) :
    StrInReConsumeInternal.consume_wf_chunk_local a ∧ StrInReConsumeInternal.consume_wf_chain_local b := by
  simpa [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chain_of_parts_local {a b : Term}
    (h1 : StrInReConsumeInternal.consume_wf_chunk_local a) (h2 : StrInReConsumeInternal.consume_wf_chain_local b) :
    StrInReConsumeInternal.consume_wf_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) := by
  simp only [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_local]
  exact ⟨h1, h2⟩

theorem StrInReConsumeInternal.consume_wf_inter_tail_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_inter_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) :
    StrInReConsumeInternal.consume_wf_chain_local c1 ∧ StrInReConsumeInternal.consume_wf_inter_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_union_tail_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_union_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_wf_chain_local c1 ∧ StrInReConsumeInternal.consume_wf_union_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chunk_inter_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) :
    StrInReConsumeInternal.consume_wf_chain_local c1 ∧ StrInReConsumeInternal.consume_wf_inter_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chunk_union_parts_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_chunk_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_wf_chain_local c1 ∧ StrInReConsumeInternal.consume_wf_union_tail_local c2 := by
  simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chain_inter_tree_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)) :
    StrInReConsumeInternal.consume_wf_inter_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
  simpa [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_inter_tail_local,
    StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chain_union_tree_local {c1 c2 : Term}
    (h : StrInReConsumeInternal.consume_wf_chain_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)) :
    StrInReConsumeInternal.consume_wf_union_tail_local
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
  simpa [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_union_tail_local,
    StrInReConsumeInternal.consume_wf_local] using h

theorem StrInReConsumeInternal.consume_wf_chain_mult_body_local {body : Term}
    (h : StrInReConsumeInternal.consume_wf_chunk_local
      (Term.Apply (Term.UOp UserOp.re_mult) body)) :
    StrInReConsumeInternal.consume_wf_chain_local body := by
  simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using h

/--
No-suffix motive: a `false` result of the reversed-pair consume means
that in the ORIGINAL orientation no suffix of the string value is in
the (unrev) regex value, and the string value is nonempty (the
mismatch witness is a definite length-1 literal chunk).  The
nonemptiness conjunct is what makes the `re_mult` (star) wrapper case
provable: `ε` is always in a star language.
-/
def StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    side = Term.Boolean false ->
    StrInReConsumeInternal.consume_wf_chain_local r ->
    ∀ ssU,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      (∀ rvU,
        __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r)) =
          SmtValue.RegLan rvU ->
          native_unpack_string ssU ≠ [] ∧
            ∀ pre suf : native_String,
              pre ++ suf = native_unpack_string ssU ->
                native_str_in_re suf rvU = false) ∧
      ((∀ a b : Term,
          r =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False) ->
        ∀ rvU,
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
            SmtValue.RegLan rvU ->
            native_unpack_string ssU ≠ [] ∧
              ∀ pre suf : native_String,
                pre ++ suf = native_unpack_string ssU ->
                  native_str_in_re suf rvU = false)

/--
Union/inter companions of the unrev no-suffix motive.  Their regexes
are `re_union`/`re_inter` trees (never chains), so the unrev transform
is `__re_rev_comp`, which distributes over the branches
(`rev_comp (union c1 c2) = union (rev_map_rev c1 eps) (rev_comp c2)`).
-/
def StrInReConsumeInternal.str_re_consume_union_unrev_no_suffix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_union s r fuel ->
    side = Term.Boolean false ->
    StrInReConsumeInternal.consume_wf_union_tail_local r ->
    ∀ ssU,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      ∀ rvU,
        __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
          SmtValue.RegLan rvU ->
          native_unpack_string ssU ≠ [] ∧
            ∀ pre suf : native_String,
              pre ++ suf = native_unpack_string ssU ->
                native_str_in_re suf rvU = false

def StrInReConsumeInternal.str_re_consume_inter_unrev_no_suffix_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_inter s r fuel ->
    side = Term.Boolean false ->
    StrInReConsumeInternal.consume_wf_inter_tail_local r ->
    ∀ ssU,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      ∀ rvU,
        __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
          SmtValue.RegLan rvU ->
          native_unpack_string ssU ≠ [] ∧
            ∀ pre suf : native_String,
              pre ++ suf = native_unpack_string ssU ->
                native_str_in_re suf rvU = false

/--
Left-continuation residual motive: when the reversed-pair consume
fully consumed the regex (residual regex `eps`), the consumed part is
an exact suffix of the original-orientation string value, so an
arbitrary continuation `q` composes on the LEFT.

The `StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck` hypothesis is REQUIRED
for the default (rebuilt `str_in_re s r`) case with `r = eps`: there
`memb_str side = s` for an arbitrary `s` of `Seq Char` type (e.g. a
sequence VARIABLE), whose `__eo_list_rev` transform is stuck, so the
unguarded typing conjunct would be false.  At every instantiation
site the transform of the input is known to evaluate, and in the
recursive cases the hypothesis for the tail follows from the
hypothesis for the cons via the `is_list` inversion.
-/
def StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    __str_membership_re side = StrInReConsumeInternal.re_empty_string_re_consume_local ->
    StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck ->
    StrInReConsumeInternal.consume_wf_chain_local r ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
    __smtx_typeof
        (__eo_to_smt
          (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
      SmtType.Seq SmtType.Char ∧
    ∀ ssU ssR,
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
        SmtValue.Seq ssR ->
      (∀ rvU,
        __smtx_model_eval M
            (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r)) =
          SmtValue.RegLan rvU ->
        (∃ u : native_String,
          native_unpack_string ssU = native_unpack_string ssR ++ u ∧
            native_str_in_re u rvU = true) ∧
        ∀ q qv,
          __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
            native_str_in_re (native_unpack_string ssU)
                (native_re_concat qv rvU) =
              native_str_in_re (native_unpack_string ssR) qv) ∧
      ((∀ a b : Term,
          r =
            Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False) ->
        ∀ rvU,
          __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
            SmtValue.RegLan rvU ->
          (∃ u : native_String,
            native_unpack_string ssU = native_unpack_string ssR ++ u ∧
              native_str_in_re u rvU = true) ∧
          ∀ q qv,
            __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
              native_str_in_re (native_unpack_string ssU)
                  (native_re_concat qv rvU) =
                native_str_in_re (native_unpack_string ssR) qv)

/--
Union/inter companions of the unrev residual motive (`__re_rev_comp`
form only, as for the no-suffix companions).
-/
def StrInReConsumeInternal.str_re_consume_union_unrev_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_union s r fuel ->
    __str_membership_re side = StrInReConsumeInternal.re_empty_string_re_consume_local ->
    StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck ->
    StrInReConsumeInternal.consume_wf_union_tail_local r ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
    __smtx_typeof
        (__eo_to_smt
          (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
      SmtType.Seq SmtType.Char ∧
    ∀ ssU ssR,
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
        SmtValue.Seq ssR ->
      ∀ rvU,
        __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
          SmtValue.RegLan rvU ->
        (∃ u : native_String,
          native_unpack_string ssU = native_unpack_string ssR ++ u ∧
            native_str_in_re u rvU = true) ∧
        ∀ q qv,
          __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
            native_str_in_re (native_unpack_string ssU)
                (native_re_concat qv rvU) =
              native_str_in_re (native_unpack_string ssR) qv

def StrInReConsumeInternal.str_re_consume_inter_unrev_residual_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_inter s r fuel ->
    __str_membership_re side = StrInReConsumeInternal.re_empty_string_re_consume_local ->
    StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck ->
    StrInReConsumeInternal.consume_wf_inter_tail_local r ->
    __smtx_typeof (__eo_to_smt (__str_membership_str side)) =
      SmtType.Seq SmtType.Char ∧
    __smtx_typeof
        (__eo_to_smt
          (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
      SmtType.Seq SmtType.Char ∧
    ∀ ssU ssR,
      __smtx_model_eval M
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ssU ->
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_str_local (__str_membership_str side))) =
        SmtValue.Seq ssR ->
      ∀ rvU,
        __smtx_model_eval M (__eo_to_smt (__re_rev_comp r)) =
          SmtValue.RegLan rvU ->
        (∃ u : native_String,
          native_unpack_string ssU = native_unpack_string ssR ++ u ∧
            native_str_in_re u rvU = true) ∧
        ∀ q qv,
          __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
            native_str_in_re (native_unpack_string ssU)
                (native_re_concat qv rvU) =
              native_str_in_re (native_unpack_string ssR) qv

/--
Rebuild relation motive: a non-`false` non-stuck consume result
rebuilds as `str_in_re (memb_str side) (memb_re side)`, and the unrev
transforms of that residual pair have the same truth value as the
unrev transforms of the input pair.  Instantiated at
`(sFlat, rFlat)`, the left side is the ORIGINAL membership (by the
involution lemmas) and the right side is exactly the second-pass
`str_in_re nextS nextR`.
-/
def StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_motive
    (M : SmtModel) (s r fuel : Term) : Prop :=
  ∀ side,
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ->
    __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
    side = __str_re_consume_rec s r fuel ->
    side ≠ Term.Stuck ->
    side ≠ Term.Boolean false ->
    __str_membership_re side ≠ Term.Stuck ->
    StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck ->
    (∃ rvU,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r)) =
        SmtValue.RegLan rvU) ->
    StrInReConsumeInternal.consume_wf_chain_local r ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local s r)))
      (__smtx_model_eval M
        (__eo_to_smt
          (StrInReConsumeInternal.consume_unrev_pair_local (__str_membership_str side)
            (__str_membership_re side))))

theorem StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local
    (M : SmtModel) (t : Term) (v : SmtRegLan)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan v) :
    t ≠ Term.Stuck := by
  intro hBad
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl] at h
  simp [__smtx_model_eval] at h

theorem StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local
    (t acc : Term)
    (hNotEps :
      t = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
        False)
    (hNotConcat :
      ∀ a b,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False) :
    __re_rev_map_rev t acc = Term.Stuck := by
  by_cases hAcc : acc = Term.Stuck
  · rw [hAcc]
    exact __re_rev_map_rev.eq_1 t
  · exact __re_rev_map_rev.eq_4 t acc hNotEps hNotConcat hAcc

/--
Accumulator factorization for `__re_rev_map_rev`: if the reversal of a
chain `t` onto some accumulator evaluates to a `RegLan` value, then
(a) the accumulator itself evaluates to a `RegLan` value and (b) there
is a fixed "reversed chunks" language `C` such that for EVERY
accumulator the reversal evaluates and its value is extensionally
`C · accV`.  This is the keystone that lets the unrev motive
inductions recurse: `__re_rev_map_rev (concat h r2) acc` changes the
accumulator (`eq_3`), so the fixed-at-eps unrev hypotheses of the
motives only line up after factoring the accumulator out.
Instantiating the transport at `acc2 := eps` recovers the eps-instance
(with `C · ε ~ C`).
-/
theorem StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local
    (M : SmtModel) :
    ∀ t acc v,
      __smtx_model_eval M (__eo_to_smt (__re_rev_map_rev t acc)) =
        SmtValue.RegLan v ->
      (∃ accV,
        __smtx_model_eval M (__eo_to_smt acc) = SmtValue.RegLan accV) ∧
      ∃ C : SmtRegLan,
        ∀ acc2 accV2,
          __smtx_model_eval M (__eo_to_smt acc2) =
            SmtValue.RegLan accV2 ->
          ∃ v2,
            __smtx_model_eval M
                (__eo_to_smt (__re_rev_map_rev t acc2)) =
              SmtValue.RegLan v2 ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan v2)
              (SmtValue.RegLan (native_re_concat C accV2)) := by
  suffices hMain :
      ∀ n t, sizeOf t ≤ n ->
        ∀ acc v,
          __smtx_model_eval M (__eo_to_smt (__re_rev_map_rev t acc)) =
            SmtValue.RegLan v ->
          (∃ accV,
            __smtx_model_eval M (__eo_to_smt acc) =
              SmtValue.RegLan accV) ∧
          ∃ C : SmtRegLan,
            ∀ acc2 accV2,
              __smtx_model_eval M (__eo_to_smt acc2) =
                SmtValue.RegLan accV2 ->
              ∃ v2,
                __smtx_model_eval M
                    (__eo_to_smt (__re_rev_map_rev t acc2)) =
                  SmtValue.RegLan v2 ∧
                RuleProofs.smt_value_rel (SmtValue.RegLan v2)
                  (SmtValue.RegLan (native_re_concat C accV2)) by
    intro t acc v hV
    exact hMain (sizeOf t) t (Nat.le_refl _) acc v hV
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht <;> omega
  | succ n ihn =>
      intro t hSize acc v hV
      by_cases hEps :
          t = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      · subst hEps
        have hAccNe : acc ≠ Term.Stuck := by
          intro hBad
          exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ v hV (by
            rw [hBad]
            exact __re_rev_map_rev.eq_1 _)
        rw [__re_rev_map_rev.eq_2 acc (fun h => hAccNe h)] at hV
        refine ⟨⟨v, hV⟩, native_str_to_re [], ?_⟩
        intro acc2 accV2 h2
        have hAcc2Ne :=
          StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ h2
        refine ⟨accV2, ?_, ?_⟩
        · rw [__re_rev_map_rev.eq_2 acc2 (fun h => hAcc2Ne h)]
          exact h2
        · rw [show native_re_concat (native_str_to_re []) accV2 = accV2
            from by cases accV2 <;> rfl]
          exact RuleProofs.smt_value_rel_refl _
      · by_cases hStuck :
            __re_rev_map_rev t acc = Term.Stuck
        · exfalso
          exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ v hV
            hStuck
        · have hConcat :
              ∃ a bb,
                t =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) a) bb := by
            rcases Classical.em (∃ a bb,
                t =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) a) bb) with
              h | h
            · exact h
            · exact absurd
                (StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ acc
                  (fun hh => hEps hh)
                  (fun a bb hh => h ⟨a, bb, hh⟩))
                hStuck
          rcases hConcat with ⟨a, bb, rfl⟩
          have hAccNe : acc ≠ Term.Stuck := by
            intro hBad
            apply hStuck
            rw [hBad]
            exact __re_rev_map_rev.eq_1 _
          rw [__re_rev_map_rev.eq_3 acc a bb (fun h => hAccNe h)] at hV
          rcases ihn bb (by
              simp at hSize
              omega) _ _ hV with ⟨⟨newAccV, hNewAccEval⟩, Cb, hTrans⟩
          have hNewAccNe :=
            StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hNewAccEval
          have hInnerNe :
              __eo_mk_apply (Term.UOp UserOp.re_concat)
                  (__re_rev_comp a) ≠ Term.Stuck :=
            eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hNewAccNe
          have hRcNe : __re_rev_comp a ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hInnerNe
          have hNewAccEq :
              __eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.re_concat)
                    (__re_rev_comp a)) acc =
                Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    (__re_rev_comp a)) acc := by
            rw [StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
              (Term.UOp UserOp.re_concat) (__re_rev_comp a)
              (by simp) hRcNe]
            exact StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local _ acc (by simp)
              hAccNe
          rw [hNewAccEq] at hNewAccEval
          have hNewAccEval' :
              __smtx_model_eval M
                  (SmtTerm.re_concat
                    (__eo_to_smt (__re_rev_comp a))
                    (__eo_to_smt acc)) =
                SmtValue.RegLan newAccV := hNewAccEval
          cases hRcEval :
              __smtx_model_eval M (__eo_to_smt (__re_rev_comp a)) <;>
            cases hAccEval : __smtx_model_eval M (__eo_to_smt acc) <;>
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hRcEval, hAccEval] at hNewAccEval'
          next rcAV accV =>
            refine ⟨⟨accV, rfl⟩, native_re_concat Cb rcAV, ?_⟩
            intro acc2 accV2 h2
            have hAcc2Ne :=
              StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ h2
            have hNewAcc2Eq :
                __eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_concat)
                      (__re_rev_comp a)) acc2 =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (__re_rev_comp a)) acc2 := by
              rw [StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local
                (Term.UOp UserOp.re_concat) (__re_rev_comp a)
                (by simp) hRcNe]
              exact StrInReConsumeInternal.eo_mk_apply_eq_apply_of_args_local _ acc2 (by simp)
                hAcc2Ne
            have hNewAcc2Eval :
                __smtx_model_eval M
                    (__eo_to_smt
                      (__eo_mk_apply
                        (__eo_mk_apply (Term.UOp UserOp.re_concat)
                          (__re_rev_comp a)) acc2)) =
                  SmtValue.RegLan (native_re_concat rcAV accV2) := by
              rw [hNewAcc2Eq]
              change __smtx_model_eval M
                  (SmtTerm.re_concat
                    (__eo_to_smt (__re_rev_comp a))
                    (__eo_to_smt acc2)) = _
              simp [__smtx_model_eval, __smtx_model_eval_re_concat,
                hRcEval, h2]
            rcases hTrans _ _ hNewAcc2Eval with ⟨v2, hV2, hRel2⟩
            refine ⟨v2, ?_, ?_⟩
            · rw [__re_rev_map_rev.eq_3 acc2 a bb (fun h => hAcc2Ne h)]
              exact hV2
            · exact RuleProofs.smt_value_rel_trans _ _ _ hRel2
                (RuleProofs.smt_value_rel_symm _ _
                  (smt_value_rel_re_concat_assoc_consume_local Cb rcAV
                    accV2))

theorem StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local
    (M : SmtModel) (x y : Term) (ss : SmtSeq)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq ss) :
    ∃ sx sy,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      native_unpack_string ss =
        native_unpack_string sx ++ native_unpack_string sy := by
  rcases StrInReConsumeInternal.eval_str_concat_seq_cases_consume_local M x y ss hEval with
    ⟨sx, sy, hx, hy, hss⟩
  refine ⟨sx, sy, hx, hy, ?_⟩
  rw [hss]
  exact native_unpack_string_pack_seq_concat_local _ sx sy

theorem StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local
    (M : SmtModel) (t : Term) (v : SmtSeq)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq v) :
    t ≠ Term.Stuck := by
  intro hBad
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl] at h
  simp [__smtx_model_eval] at h

theorem StrInReConsumeInternal.list_rev_rec_atom_eq_consume_local
    (t acc : Term)
    (hT : t ≠ Term.Stuck) (hAcc : acc ≠ Term.Stuck)
    (hNotApp :
      ∀ f x y, t = Term.Apply (Term.Apply f x) y -> False) :
    __eo_list_rev_rec t acc = acc := by
  rw [__eo_list_rev_rec.eq_def]
  split
  · exact absurd rfl hT
  · exact absurd rfl hAcc
  · exact ((hNotApp _ _ _ rfl).elim)
  · rfl

theorem StrInReConsumeInternal.eo_is_list_str_concat_cons_inv_consume_local
    (g x y : Term)
    (h :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) =
        Term.Boolean true) :
    g = Term.UOp UserOp.str_concat ∧
      __eo_is_list (Term.UOp UserOp.str_concat) y =
        Term.Boolean true := by
  have hOk :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) ≠ Term.Stuck := by
    intro hBad
    rw [show __eo_is_list (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply g x) y) =
        __eo_is_ok
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.Apply g x) y)) from rfl, hBad] at h
    simp [__eo_is_ok, native_teq, SmtEval.native_not] at h
  have hReqNe :
      __eo_requires (Term.UOp UserOp.str_concat) g
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) ≠
        Term.Stuck := by
    simpa [__eo_get_nil_rec] using hOk
  have hg : Term.UOp UserOp.str_concat = g :=
    eo_requires_eq_of_ne_stuck _ _ _ hReqNe
  have hRecNe :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) y ≠
        Term.Stuck := by
    intro hBad
    apply hReqNe
    rw [hBad]
    simp [__eo_requires, SmtEval.native_ite, SmtEval.native_not,
      native_teq]
  have hYNe : y ≠ Term.Stuck := by
    intro hBad
    apply hRecNe
    rw [hBad]
    simp [__eo_get_nil_rec]
  refine ⟨hg.symm, ?_⟩
  have hEq :
      __eo_is_list (Term.UOp UserOp.str_concat) y =
        __eo_is_ok
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) := by
    cases y <;> first | exact absurd rfl hYNe | rfl
  rw [hEq]
  simp [__eo_is_ok, native_teq, SmtEval.native_not, hRecNe]

/--
Accumulator factorization for `__eo_list_rev_rec` on `str_concat`
lists: string-side companion of
`StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local`.  The reversed word is a
fixed word `W` prepended to the accumulator's word, for EVERY
accumulator.
-/
theorem StrInReConsumeInternal.eval_list_rev_rec_acc_factor_consume_local
    (M : SmtModel) :
    ∀ t acc v,
      __eo_is_list (Term.UOp UserOp.str_concat) t = Term.Boolean true ->
      __smtx_model_eval M (__eo_to_smt (__eo_list_rev_rec t acc)) =
        SmtValue.Seq v ->
      (∃ accV,
        __smtx_model_eval M (__eo_to_smt acc) = SmtValue.Seq accV) ∧
      ∃ W : native_String,
        ∀ acc2 accV2,
          __smtx_model_eval M (__eo_to_smt acc2) =
            SmtValue.Seq accV2 ->
          ∃ v2,
            __smtx_model_eval M
                (__eo_to_smt (__eo_list_rev_rec t acc2)) =
              SmtValue.Seq v2 ∧
            native_unpack_string v2 =
              W ++ native_unpack_string accV2 := by
  suffices hMain :
      ∀ n t, sizeOf t ≤ n ->
        ∀ acc v,
          __eo_is_list (Term.UOp UserOp.str_concat) t =
            Term.Boolean true ->
          __smtx_model_eval M (__eo_to_smt (__eo_list_rev_rec t acc)) =
            SmtValue.Seq v ->
          (∃ accV,
            __smtx_model_eval M (__eo_to_smt acc) =
              SmtValue.Seq accV) ∧
          ∃ W : native_String,
            ∀ acc2 accV2,
              __smtx_model_eval M (__eo_to_smt acc2) =
                SmtValue.Seq accV2 ->
              ∃ v2,
                __smtx_model_eval M
                    (__eo_to_smt (__eo_list_rev_rec t acc2)) =
                  SmtValue.Seq v2 ∧
                native_unpack_string v2 =
                  W ++ native_unpack_string accV2 by
    intro t acc v hList hV
    exact hMain (sizeOf t) t (Nat.le_refl _) acc v hList hV
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht <;> omega
  | succ n ihn =>
      intro t hSize acc v hList hV
      have hTNe : t ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hList
        simp [__eo_is_list] at hList
      have hAccNe : acc ≠ Term.Stuck := by
        intro hBad
        apply StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ v hV
        rw [hBad]
        rw [__eo_list_rev_rec.eq_def]
        split
        · rfl
        · rfl
        · rfl
        · rfl
      rcases Classical.em (∃ f x y,
          t = Term.Apply (Term.Apply f x) y) with hApp | hApp
      · rcases hApp with ⟨f, x, y, rfl⟩
        rcases StrInReConsumeInternal.eo_is_list_str_concat_cons_inv_consume_local f x y
            hList with ⟨rfl, hListY⟩
        rw [eo_list_rev_rec_cons _ x y acc hAccNe] at hV
        rcases ihn y (by
            simp at hSize
            omega) _ _ hListY hV with ⟨⟨accV', hAcc'⟩, W, hTrans⟩
        rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M x acc
            accV' hAcc' with ⟨sx, sacc, hX, hAccEval, _hUnp'⟩
        refine ⟨⟨sacc, hAccEval⟩, W ++ native_unpack_string sx, ?_⟩
        intro acc2 accV2 h2
        have hAcc2Ne :=
          StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ h2
        have hCons2Eval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) x)
                    acc2)) =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value sx)
                  (native_seq_concat (native_unpack_seq sx)
                    (native_unpack_seq accV2))) := by
          change __smtx_model_eval M
              (SmtTerm.str_concat (__eo_to_smt x)
                (__eo_to_smt acc2)) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_concat, hX, h2]
        rcases hTrans _ _ hCons2Eval with ⟨v2, hv2, hUnp2⟩
        refine ⟨v2, ?_, ?_⟩
        · rw [eo_list_rev_rec_cons _ x y acc2 hAcc2Ne]
          exact hv2
        · rw [hUnp2,
            native_unpack_string_pack_seq_concat_local _ sx accV2,
            List.append_assoc]
      · have hAtomEq :
            __eo_list_rev_rec t acc = acc :=
          StrInReConsumeInternal.list_rev_rec_atom_eq_consume_local t acc hTNe hAccNe
            (fun f x y hh => hApp ⟨f, x, y, hh⟩)
        rw [hAtomEq] at hV
        refine ⟨⟨v, hV⟩, [], ?_⟩
        intro acc2 accV2 h2
        have hAcc2Ne :=
          StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ h2
        refine ⟨accV2, ?_, by simp⟩
        rw [StrInReConsumeInternal.list_rev_rec_atom_eq_consume_local t acc2 hTNe hAcc2Ne
          (fun f x y hh => hApp ⟨f, x, y, hh⟩)]
        exact h2

theorem StrInReConsumeInternal.native_string_valid_suffix_consume_local
    (pre suf : native_String)
    (h : native_string_valid (pre ++ suf) = true) :
    native_string_valid suf = true := by
  simp [native_string_valid, List.all_append] at h
  simpa [native_string_valid] using h.2

theorem StrInReConsumeInternal.native_string_valid_prefix_consume_local
    (pre suf : native_String)
    (h : native_string_valid (pre ++ suf) = true) :
    native_string_valid pre = true := by
  simp [native_string_valid, List.all_append] at h
  simpa [native_string_valid] using h.1

/--
Exact-word snoc cancellation for suffix families: if no suffix of `w`
is in `A`, then no suffix of `w ++ u` is in `A · {u}`.  The membership
analysis forces the split (the `str_to_re` factor matches exactly
`u`), so no case analysis on the suffix position is needed.
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_word_suffixes_false_local
    (w u : native_String) (A : SmtRegLan)
    (hAll :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf A = false) :
    ∀ pre suf : native_String,
      pre ++ suf = w ++ u ->
        native_str_in_re suf
            (native_re_concat A (native_str_to_re u)) =
          false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf
      (native_re_concat A (native_str_to_re u)) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf
              (native_re_mk_concat A (native_str_to_re u)) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          (native_str_to_re u)).1 hListMem with
        ⟨x, y, hSplit, hX, hY⟩
      have hXValid : native_string_valid x = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYStr : native_str_in_re y (native_str_to_re u) = true := by
        simpa [native_str_in_re, hYValid] using hY
      have hYU : y = u := native_str_in_re_str_to_re_eq hYValid hYStr
      subst hYU
      have hWX : (pre ++ x) ++ y = w ++ y := by
        rw [List.append_assoc, hSplit]
        exact hApp
      have hPreX : pre ++ x = w :=
        (List.append_inj' hWX rfl).1
      have hXFalse : native_str_in_re x A = false := hAll pre x hPreX
      have hXStr : native_str_in_re x A = true := by
        simpa [native_str_in_re, hXValid] using hX
      rw [hXFalse] at hXStr
      cases hXStr

/--
Length-one-class snoc cancellation for suffix families: covers the
char, range and allchar heads uniformly.  If every member of `H` has
length 1 and no suffix of `w` is in `A`, then no suffix of `w ++ u`
(for any length-1 `u`) is in `A · H`.
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_len_one_suffixes_false_local
    (w u : native_String) (A H : SmtRegLan)
    (hLen1 :
      ∀ x : native_String,
        nativeListInRe x H = true -> x.length = 1)
    (hU : u.length = 1)
    (hAll :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf A = false) :
    ∀ pre suf : native_String,
      pre ++ suf = w ++ u ->
        native_str_in_re suf (native_re_concat A H) = false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf (native_re_concat A H) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf (native_re_mk_concat A H) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          H).1 hListMem with
        ⟨x, y, hSplit, hX, hY⟩
      have hXValid : native_string_valid x = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYLen : y.length = 1 := hLen1 y hY
      have hWX : (pre ++ x) ++ y = w ++ u := by
        rw [List.append_assoc, hSplit]
        exact hApp
      have hPreX : pre ++ x = w :=
        (List.append_inj' hWX (by rw [hYLen, hU])).1
      have hXFalse : native_str_in_re x A = false := hAll pre x hPreX
      have hXStr : native_str_in_re x A = true := by
        simpa [native_str_in_re, hXValid] using hX
      rw [hXFalse] at hXStr
      cases hXStr

theorem StrInReConsumeInternal.eo_is_list_nil_str_concat_unpack_consume_local
    (M : SmtModel) (t : Term) (v : SmtSeq)
    (hNil : __eo_is_list_nil_str_concat t = Term.Boolean true)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq v) :
    native_unpack_string v = [] := by
  rw [__eo_is_list_nil_str_concat.eq_def] at hNil
  split at hNil
  · cases hNil
  · next T =>
      change __smtx_model_eval M
          (__eo_to_smt_seq_empty (__eo_to_smt_type T)) = SmtValue.Seq v
        at hEval
      cases hTy : __eo_to_smt_type T <;>
        simp [hTy, __eo_to_smt_seq_empty, __smtx_model_eval] at hEval
      rw [← hEval]
      simp [native_unpack_string, native_unpack_seq]
  · have hEq := eq_of_eo_eq_true t (Term.String []) hNil
      -- hEq : Term.String [] = t
    rw [← hEq] at hEval
    change __smtx_model_eval M (SmtTerm.String []) = SmtValue.Seq v
      at hEval
    rw [show __smtx_model_eval M (SmtTerm.String []) =
        SmtValue.Seq (native_pack_string []) from by
      simp only [__smtx_model_eval]] at hEval
    injection hEval with hv
    rw [← hv]
    simp [native_unpack_string, native_pack_string,
      Smtm.native_unpack_pack_seq]

theorem StrInReConsumeInternal.get_nil_rec_atom_eq_consume_local
    (t : Term)
    (hT : t ≠ Term.Stuck)
    (hNotApp :
      ∀ f x y, t = Term.Apply (Term.Apply f x) y -> False) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat) t =
      __eo_requires
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) t)
        (Term.Boolean true) t := by
  cases t
  case Stuck => exact absurd rfl hT
  case Apply a b =>
    cases a <;>
      first
        | exact ((hNotApp _ _ _ rfl).elim)
        | rfl
  all_goals rfl

theorem StrInReConsumeInternal.eo_is_list_nil_str_concat_red_consume_local
    (t : Term) (hT : t ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) t =
      __eo_is_list_nil_str_concat t := by
  cases t <;> first | exact absurd rfl hT | rfl

/--
The nil end of a `str_concat` list evaluates to the empty word.
-/
theorem StrInReConsumeInternal.get_nil_rec_unpack_nil_consume_local
    (M : SmtModel) :
    ∀ t v,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) t)) =
        SmtValue.Seq v ->
      native_unpack_string v = [] := by
  suffices hMain :
      ∀ n t, sizeOf t ≤ n ->
        ∀ v,
          __smtx_model_eval M
              (__eo_to_smt
                (__eo_get_nil_rec (Term.UOp UserOp.str_concat) t)) =
            SmtValue.Seq v ->
          native_unpack_string v = [] by
    intro t v hV
    exact hMain (sizeOf t) t (Nat.le_refl _) v hV
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht <;> omega
  | succ n ihn =>
      intro t hSize v hV
      have hGnrNe :=
        StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ hV
      have hTNe : t ≠ Term.Stuck := by
        intro hBad
        apply hGnrNe
        rw [hBad]
        rfl
      rcases Classical.em (∃ f x y,
          t = Term.Apply (Term.Apply f x) y) with hApp | hApp
      · rcases hApp with ⟨f, x, y, rfl⟩
        have hStep :
            __eo_get_nil_rec (Term.UOp UserOp.str_concat)
                (Term.Apply (Term.Apply f x) y) =
              __eo_requires (Term.UOp UserOp.str_concat) f
                (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) :=
          rfl
        rw [hStep] at hV hGnrNe
        have hResEq :=
          eo_requires_result_eq_of_ne_stuck _ _ _ hGnrNe
        rw [hResEq] at hV
        exact ihn y (by
            simp at hSize
            omega) v hV
      · have hAtom :=
          StrInReConsumeInternal.get_nil_rec_atom_eq_consume_local t hTNe
            (fun f x y hh => hApp ⟨f, x, y, hh⟩)
        rw [hAtom] at hV hGnrNe
        have hNilTrue :=
          eo_requires_eq_of_ne_stuck _ _ _ hGnrNe
        have hResEq :=
          eo_requires_result_eq_of_ne_stuck _ _ _ hGnrNe
        rw [hResEq] at hV
        rw [StrInReConsumeInternal.eo_is_list_nil_str_concat_red_consume_local t hTNe]
          at hNilTrue
        exact StrInReConsumeInternal.eo_is_list_nil_str_concat_unpack_consume_local M t v
          hNilTrue hV

/--
Snoc view of `__eo_list_rev` on a cons: the reversed word of
`concat s1 s2` is the reversed word of `s2` followed by the word of
`s1`.  This is the per-case string-side step of the unrev inductions.
-/
theorem StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local
    (M : SmtModel) (s1 s2 : Term) (ssU : SmtSeq)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2))) =
        SmtValue.Seq ssU) :
    ∃ ssU2 s1V,
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) =
        SmtValue.Seq ssU2 ∧
      __smtx_model_eval M (__eo_to_smt s1) = SmtValue.Seq s1V ∧
      native_unpack_string ssU =
        native_unpack_string ssU2 ++ native_unpack_string s1V := by
  have hRevNe :=
    StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ hEval
  have hReqNe :
      __eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              s2))
          (Term.Boolean true)
          (__eo_list_rev_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              s2)
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2))) ≠ Term.Stuck := hRevNe
  have hListCons :=
    eo_requires_eq_of_ne_stuck _ _ _ hReqNe
  rcases StrInReConsumeInternal.eo_is_list_str_concat_cons_inv_consume_local
      (Term.UOp UserOp.str_concat) s1 s2 hListCons with ⟨_, hListS2⟩
  have hUnfold :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            s2) =
        __eo_list_rev_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              s2)) :=
    eo_requires_result_eq_of_ne_stuck _ _ _ hReqNe
  rw [hUnfold] at hEval
  have hNilNe :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            s2) ≠ Term.Stuck := by
    intro hBad
    apply StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ hEval
    rw [hBad]
    simp [__eo_list_rev_rec]
  have hGnrStep :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            s2) =
        __eo_get_nil_rec (Term.UOp UserOp.str_concat) s2 := by
    rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
            s2) =
        __eo_requires (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2) from rfl]
    exact eo_requires_result_eq_of_ne_stuck _ _ _ (by
      rw [show __eo_requires (Term.UOp UserOp.str_concat)
            (Term.UOp UserOp.str_concat)
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2) =
          __eo_get_nil_rec (Term.UOp UserOp.str_concat)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          from rfl]
      exact hNilNe)
  rw [hGnrStep] at hEval hNilNe
  rw [eo_list_rev_rec_cons _ s1 s2 _ hNilNe] at hEval
  rcases StrInReConsumeInternal.eval_list_rev_rec_acc_factor_consume_local M s2 _ ssU hListS2
      hEval with ⟨⟨consV, hConsEval⟩, W, hTrans⟩
  rcases StrInReConsumeInternal.eval_str_concat_unpack_append_consume_local M s1 _ consV
      hConsEval with ⟨s1V, nilV, hS1V, hNilV, hConsUnp⟩
  have hNilW : native_unpack_string nilV = [] :=
    StrInReConsumeInternal.get_nil_rec_unpack_nil_consume_local M s2 nilV hNilV
  rcases hTrans _ _ hConsEval with ⟨v1, hV1, hV1Unp⟩
  injection hEval.symm.trans hV1 with hSsEq
  subst hSsEq
  rcases hTrans _ _ hNilV with ⟨v2, hV2, hV2Unp⟩
  refine ⟨v2, s1V, ?_, hS1V, ?_⟩
  · have hRevS2Ne :
        __eo_requires
            (__eo_is_list (Term.UOp UserOp.str_concat) s2)
            (Term.Boolean true)
            (__eo_list_rev_rec s2
              (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2)) ≠
          Term.Stuck := by
      rw [hListS2]
      rw [show __eo_requires (Term.Boolean true) (Term.Boolean true)
            (__eo_list_rev_rec s2
              (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2)) =
          __eo_list_rev_rec s2
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2) from by
        simp [__eo_requires, native_teq, SmtEval.native_ite,
          SmtEval.native_not]]
      exact StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ hV2
    have hUnfold2 :
        __eo_list_rev (Term.UOp UserOp.str_concat) s2 =
          __eo_list_rev_rec s2
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) s2) :=
      eo_requires_result_eq_of_ne_stuck _ _ _ hRevS2Ne
    rw [hUnfold2]
    exact hV2
  · rw [hV1Unp, hV2Unp, hConsUnp, hNilW]
    simp

theorem StrInReConsumeInternal.list_append_ne_nil_left_consume_local {α : Type}
    (xs ys : List α) (h : xs ≠ []) : xs ++ ys ≠ [] := by
  intro hBad
  apply h
  cases xs with
  | nil => rfl
  | cons a as => simp at hBad

/--
Mismatch-head snoc cancellation: if the appended character `[c]` is
not in the length-1-membered head `H`, then NO suffix of `w ++ [c]`
is in `A · H`, for ANY `A` (no induction hypothesis about `A`
needed — the last character rules everything out).
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_mismatch_suffixes_false_local
    (w : native_String) (c : native_Char) (A H : SmtRegLan)
    (hLen1 :
      ∀ x : native_String,
        nativeListInRe x H = true -> x.length = 1)
    (hNotIn : native_str_in_re [c] H = false) :
    ∀ pre suf : native_String,
      pre ++ suf = w ++ [c] ->
        native_str_in_re suf (native_re_concat A H) = false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf (native_re_concat A H) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf (native_re_mk_concat A H) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          H).1 hListMem with
        ⟨x, y, hSplit, _hX, hY⟩
      have hYLen : y.length = 1 := hLen1 y hY
      have hWX : (pre ++ x) ++ y = w ++ [c] := by
        rw [List.append_assoc, hSplit]
        exact hApp
      have hYC : y = [c] :=
        (List.append_inj' hWX (by rw [hYLen]; rfl)).2
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYStr : native_str_in_re y H = true := by
        simpa [native_str_in_re, hYValid] using hY
      rw [hYC, hNotIn] at hYStr
      cases hYStr

/-- `StrInReConsumeInternal.native_re_reverse_raw_consume_local` commutes with `mk_star`. -/
theorem StrInReConsumeInternal.native_re_reverse_raw_mk_star_consume_local
    (r : SmtRegLan) :
    StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_re_mk_star r) =
      native_re_mk_star (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
  cases r <;>
    simp [native_re_mk_star, native_re_mult,
      StrInReConsumeInternal.native_re_reverse_raw_consume_local]

/--
Right-decomposition of star membership: a nonempty member of
`(r)*` ends with a nonempty chunk in `r`.
-/
theorem StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_local
    (w : native_String) (r : SmtRegLan)
    (hMem : native_str_in_re w (native_re_mult r) = true)
    (hNe : w ≠ []) :
    ∃ pre suf : native_String,
      pre ++ suf = w ∧ suf ≠ [] ∧ native_str_in_re suf r = true := by
  have hValid : native_string_valid w = true := by
    cases h : native_string_valid w with
    | true => rfl
    | false => simp [native_str_in_re, h] at hMem
  have hRevValid : native_string_valid w.reverse = true := by
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local w] using hValid
  have hRevMem :
      native_str_in_re w.reverse
          (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
        true := by
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local w (native_re_mult r)
    rw [hEq] at hMem
    have hStarEq :
        StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_re_mult r) =
          native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
      have hsimpa :=
        StrInReConsumeInternal.native_re_reverse_raw_mk_star_consume_local r
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa
    rw [hStarEq] at hMem
    exact hMem
  have hRevListMem :
      nativeListInRe w.reverse
          (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
        true := by
    simpa [native_str_in_re, nativeListInRe, hRevValid] using hRevMem
  have hRevNe : w.reverse ≠ [] := by
    intro hBad
    apply hNe
    simpa using congrArg List.reverse hBad
  rcases nativeListInRe_re_mult_nonempty_prefix_local w.reverse
      (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) hRevListMem hRevNe with
    ⟨pre', suf', hAppend, hPreNe, hPreMem⟩
  refine ⟨suf'.reverse, pre'.reverse, ?_, ?_, ?_⟩
  · have h := congrArg List.reverse hAppend
    simpa using h
  · intro hBad
    apply hPreNe
    simpa using congrArg List.reverse hBad
  · have hPreValid : native_string_valid pre' = true :=
      native_string_valid_append_left pre' suf' (by
        rw [hAppend]
        exact hRevValid)
    have hPreRevValid : native_string_valid pre'.reverse = true := by
      simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local pre'] using
        hPreValid
    have hPreStrMem :
        native_str_in_re pre'
            (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
          true := by
      simpa [native_str_in_re, hPreValid] using hPreMem
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local pre'.reverse r
    rw [show pre'.reverse.reverse = pre' by simp] at hEq
    rw [hEq] at hPreStrMem
    exact hPreStrMem

/--
Star-head snoc cancellation: if no suffix of `w` is in `A` and no
suffix of `w` is in `B`, then no suffix of `w` is in `A · B*`.  The
star factor either contributes `ε` (reducing to the `A` case) or ends
with a nonempty `B`-chunk, which is itself a suffix of `w`.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_star_suffixes_false_local
    (w : native_String) (A B : SmtRegLan)
    (hAllA :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf A = false)
    (hAllB :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf B = false) :
    ∀ pre suf : native_String,
      pre ++ suf = w ->
        native_str_in_re suf (native_re_concat A (native_re_mult B)) =
          false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf
      (native_re_concat A (native_re_mult B)) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf
              (native_re_mk_concat A (native_re_mult B)) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          (native_re_mult B)).1 hListMem with
        ⟨x, y, hSplit, hX, hY⟩
      have hXValid : native_string_valid x = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      by_cases hYNil : y = []
      · subst hYNil
        have hXSuf : pre ++ x = w := by
          rw [← hApp, ← hSplit]
          simp
        have hXFalse := hAllA pre x hXSuf
        have hXStr : native_str_in_re x A = true := by
          simpa [native_str_in_re, hXValid] using hX
        rw [hXFalse] at hXStr
        cases hXStr
      · have hYStr :
            native_str_in_re y (native_re_mult B) = true := by
          simpa [native_str_in_re, hYValid] using hY
        rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_local y B hYStr
            hYNil with
          ⟨yPre, chunk, hYSplit, _hChunkNe, hChunkMem⟩
        have hChunkSuf : (pre ++ (x ++ yPre)) ++ chunk = w := by
          rw [← hApp, ← hSplit, ← hYSplit]
          simp
        have hChunkFalse :=
          hAllB (pre ++ (x ++ yPre)) chunk hChunkSuf
        rw [hChunkFalse] at hChunkMem
        cases hChunkMem

/-
The three unrev motives, to be proven by `__str_re_consume_rec.induct`
with companion `union`/`inter` motives, mirroring the proofs of
`hRecSemantic` and `hRecModelRel` in `str_re_consume_model_rel` below.
-/
/--
Equality version of the length-1-class snoc cancellation, for the
residual (∀q) conclusions: appending a length-1 word that IS in the
head class preserves and reflects membership.
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_len_one_eq_consume_local
    (w u : native_String) (A H : SmtRegLan)
    (hLen1 :
      ∀ x : native_String,
        nativeListInRe x H = true -> x.length = 1)
    (hU : u.length = 1)
    (hUin : native_str_in_re u H = true) :
    native_str_in_re (w ++ u) (native_re_concat A H) =
      native_str_in_re w A := by
  cases hWV : native_string_valid w with
  | false =>
      have hLHSInvalid : native_string_valid (w ++ u) = false := by
        cases h : native_string_valid (w ++ u) with
        | false => rfl
        | true =>
            have hPre := StrInReConsumeInternal.native_string_valid_prefix_consume_local w u h
            rw [hWV] at hPre
            cases hPre
      simp [native_str_in_re, hWV, hLHSInvalid]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hValid : native_string_valid (w ++ u) = true := by
          cases h : native_string_valid (w ++ u) with
          | true => rfl
          | false => simp [native_str_in_re, h] at hMem
        have hListMem :
            nativeListInRe (w ++ u) (native_re_mk_concat A H) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append _ A
            H).1 hListMem with
          ⟨x, y, hSplit, hX, hY⟩
        have hYLen := hLen1 y hY
        rcases List.append_inj' hSplit (by rw [hYLen, hU]) with
          ⟨rfl, rfl⟩
        simpa [native_str_in_re, hWV] using hX
      · intro hMem
        exact native_str_in_re_re_concat_intro w u A H hMem hUin

/--
Equality version of the exact-word snoc cancellation.
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_word_eq_consume_local
    (w u : native_String) (A : SmtRegLan)
    (hUValid : native_string_valid u = true) :
    native_str_in_re (w ++ u)
        (native_re_concat A (native_str_to_re u)) =
      native_str_in_re w A := by
  cases hWV : native_string_valid w with
  | false =>
      have hLHSInvalid : native_string_valid (w ++ u) = false := by
        cases h : native_string_valid (w ++ u) with
        | false => rfl
        | true =>
            have hPre := StrInReConsumeInternal.native_string_valid_prefix_consume_local w u h
            rw [hWV] at hPre
            cases hPre
      simp [native_str_in_re, hWV, hLHSInvalid]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hValid : native_string_valid (w ++ u) = true := by
          cases h : native_string_valid (w ++ u) with
          | true => rfl
          | false => simp [native_str_in_re, h] at hMem
        have hListMem :
            nativeListInRe (w ++ u)
                (native_re_mk_concat A (native_str_to_re u)) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append _ A
            (native_str_to_re u)).1 hListMem with
          ⟨x, y, hSplit, hX, hY⟩
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hValid)
        have hYStr : native_str_in_re y (native_str_to_re u) = true := by
          simpa [native_str_in_re, hYValid] using hY
        have hYU : y = u := native_str_in_re_str_to_re_eq hYValid hYStr
        subst hYU
        rcases List.append_inj' hSplit rfl with ⟨rfl, _⟩
        simpa [native_str_in_re, hWV] using hX
      · intro hMem
        exact native_str_in_re_re_concat_intro w u A
          (native_str_to_re u) hMem
          (native_str_in_re_str_to_re_self_local u hUValid)

theorem StrInReConsumeInternal.map_char_of_comp_char_consume_local :
    ∀ w : native_String,
      w.map (impl_native_ssm_char_of_value ∘ SmtValue.Char) = w
  | [] => rfl
  | c :: cs => by
      simp only [List.map_cons]
      rw [StrInReConsumeInternal.map_char_of_comp_char_consume_local cs]
      rfl

theorem StrInReConsumeInternal.eval_string_unpack_consume_local
    (M : SmtModel) (w : native_String) :
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt (Term.String w)) =
        SmtValue.Seq ss ∧
      native_unpack_string ss = w := by
  refine ⟨native_pack_string w, ?_, ?_⟩
  · change __smtx_model_eval M (SmtTerm.String w) = _
    simp only [__smtx_model_eval]
  · simp [native_unpack_string, impl_native_string_to_values,
     
      StrInReConsumeInternal.map_char_of_comp_char_consume_local]

theorem StrInReConsumeInternal.typed_seq_unpack_values_of_eval_local
    (M : SmtModel) (hM : model_wf M) (s : Term) (ss : SmtSeq)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss) :
    native_unpack_seq ss =
      impl_native_string_to_values (native_unpack_string ss) := by
  apply native_unpack_seq_eq_string_to_values_of_typeof_seq_char
  have h := smt_model_eval_preserves_type_of_non_none M hM
    (__eo_to_smt s) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)
  rw [hEval, hTy] at h
  have hsimpa := h
  try simp at hsimpa ⊢
  exact hsimpa

theorem StrInReConsumeInternal.typed_seq_value_of_eval_local
    (M : SmtModel) (hM : model_wf M) (s : SmtTerm) (ss : SmtSeq)
    (hTy : __smtx_typeof s = SmtType.Seq SmtType.Char)
    (hEval : __smtx_model_eval M s = SmtValue.Seq ss) :
    __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char := by
  rw [← hEval]
  simpa [hTy] using
    smt_model_eval_preserves_type_of_non_none M hM s (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

theorem StrInReConsumeInternal.list_append_ne_nil_right_consume_local {α : Type}
    (xs ys : List α) (h : ys ≠ []) : xs ++ ys ≠ [] := by
  intro hBad
  apply h
  cases xs with
  | nil => simpa using hBad
  | cons a as => simp at hBad

theorem StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
    {r1 r2 : SmtRegLan}
    (h : RuleProofs.smt_value_rel (SmtValue.RegLan r1)
      (SmtValue.RegLan r2))
    (str : native_String) :
    native_str_in_re str r1 = native_str_in_re str r2 := by
  cases hV : native_string_valid str with
  | true =>
      simpa [native_str_in_re_eq_model] using
        smt_value_rel_reglan_valid_eq h hV
  | false => simp [native_str_in_re, hV]

theorem StrInReConsumeInternal.native_str_in_re_nil_str_to_re_nil_consume_local :
    native_str_in_re [] (native_str_to_re []) = true := by
  simp [native_str_in_re, native_string_valid, native_str_to_re,
    impl_native_re_of_list, nativeListInRe, native_re_nullable]

theorem StrInReConsumeInternal.smt_value_rel_union_right_none_consume_local
    (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_union r native_re_none))
      (SmtValue.RegLan r) := by
  apply smt_value_rel_of_native_includes_local
  · exact native_includes_union_left r native_re_none
  · intro xs _hValid hMem
    simpa [native_str_in_re_re_union, native_str_in_re_re_none] using hMem

theorem StrInReConsumeInternal.smt_value_rel_inter_right_all_consume_local
    (r : SmtRegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan (native_re_inter r native_re_all))
      (SmtValue.RegLan r) := by
  apply smt_value_rel_of_native_includes_local
  · intro xs hValid hMem
    rw [native_str_in_re_re_inter]
    simp [hMem, native_str_in_re_re_all xs hValid]
  · exact native_includes_inter_left r native_re_all

/--
The unrev transform of the tail of a `str_concat` cons is non-stuck
whenever the transform of the cons is: discharges the guard hypothesis
of the unrev residual motive at the recursive IHs.
-/
theorem StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local
    (s1 s2 : Term)
    (h : StrInReConsumeInternal.consume_unrev_str_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2) ≠
      Term.Stuck) :
    StrInReConsumeInternal.consume_unrev_str_local s2 ≠ Term.Stuck := by
  simp only [StrInReConsumeInternal.consume_unrev_str_local] at h ⊢
  have hList := eo_list_rev_is_list_true_of_ne_stuck _ _ h
  rcases StrInReConsumeInternal.eo_is_list_str_concat_cons_inv_consume_local _ s1 s2 hList with
    ⟨_, hTail⟩
  exact eo_list_rev_ne_stuck_of_is_list_true _ _ hTail

/--
The unrev transform of a term is non-stuck as soon as it evaluates to
a sequence value.
-/
theorem StrInReConsumeInternal.consume_unrev_str_ne_stuck_of_eval_local
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (h :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ss) :
    StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck :=
  StrInReConsumeInternal.term_ne_stuck_of_eval_seq_consume_local M _ _ h

theorem StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
    (op : Term) (X Y : Term)
    (hOp : op ≠ Term.Stuck)
    (hX : X ≠ Term.Stuck) (hY : Y ≠ Term.Stuck) :
    __eo_mk_apply (__eo_mk_apply op X) Y =
      Term.Apply (Term.Apply op X) Y := by
  have h1 : __eo_mk_apply op X = Term.Apply op X := by
    cases op <;> first | exact absurd rfl hOp | skip
    all_goals cases X <;> first | exact absurd rfl hX | rfl
  rw [h1]
  cases Y <;> first | exact absurd rfl hY | rfl

/--
Exact-word snoc cancellation with a mismatching literal head: if the
last character differs from the exact word `[d]` demanded by the
`str_to_re` factor, NO suffix of `w ++ [c]` is in `A · {[d]}`, for any
`A`.
-/
theorem StrInReConsumeInternal.native_str_in_re_snoc_word_mismatch_suffixes_false_local
    (w : native_String) (c d : native_Char) (A : SmtRegLan)
    (hNe : c ≠ d) :
    ∀ pre suf : native_String,
      pre ++ suf = w ++ [c] ->
        native_str_in_re suf
            (native_re_concat A (native_str_to_re [d])) =
          false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf
      (native_re_concat A (native_str_to_re [d])) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf
              (native_re_mk_concat A (native_str_to_re [d])) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          (native_str_to_re [d])).1 hListMem with
        ⟨x, y, hSplit, _hX, hY⟩
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYStr : native_str_in_re y (native_str_to_re [d]) = true := by
        simpa [native_str_in_re, hYValid] using hY
      have hYD : y = [d] := native_str_in_re_str_to_re_eq hYValid hYStr
      subst hYD
      have hWX : (pre ++ x) ++ [d] = w ++ [c] := by
        rw [List.append_assoc, hSplit]
        exact hApp
      have hDC : [d] = [c] :=
        (List.append_inj' hWX rfl).2
      injection hDC with hdc
      exact hNe hdc.symm

/--
Snoc-view value bridge for a general (non-eps) head: the unrev
transform of `re_concat head r2` starts the accumulator at
`rev_comp head · ε`, so its value is (extensionally) the value of the
unrev transform of `r2` concatenated with the value of
`rev_comp head` on the RIGHT.
-/
theorem StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local
    (M : SmtModel) (head r2 : Term) (rvU headV : SmtRegLan)
    (hCompEval :
      __smtx_model_eval M (__eo_to_smt (__re_rev_comp head)) =
        SmtValue.RegLan headV)
    (hRvU :
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_re_local
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
                r2))) =
        SmtValue.RegLan rvU) :
    ∃ rvU2,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2)) =
        SmtValue.RegLan rvU2 ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan rvU)
        (SmtValue.RegLan (native_re_concat rvU2 headV)) := by
  simp only [StrInReConsumeInternal.consume_unrev_re_local] at hRvU ⊢
  rw [__re_rev_map_rev.eq_3
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    head r2 (by
      intro h
      cases h)] at hRvU
  have hCompNe : __re_rev_comp head ≠ Term.Stuck :=
    StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hCompEval
  have hAccEval2 :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_rev_comp head))
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])))) =
        SmtValue.RegLan
          (native_re_concat headV (native_str_to_re [])) := by
    rw [StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
      (Term.UOp UserOp.re_concat) _ _ (by
        intro h
        cases h) hCompNe (by
        intro h
        cases h)]
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt (__re_rev_comp head))
          (SmtTerm.str_to_re (SmtTerm.String []))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hCompEval,
     ]
  have hEpsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) = _
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M r2 _ rvU hRvU with
    ⟨⟨newAccV, hNewAccEval⟩, C, hTrans⟩
  rcases hTrans _ _ hAccEval2 with ⟨v1, hv1, hRel1⟩
  injection hRvU.symm.trans hv1 with hV1
  subst hV1
  rw [show native_re_concat headV (native_str_to_re []) = headV from by
    cases headV <;> rfl] at hRel1
  rcases hTrans _ _ hEpsEval with ⟨rvU2, hRvU2, hRel2⟩
  rw [show native_re_concat C (native_str_to_re []) = C from by
    cases C <;> rfl] at hRel2
  refine ⟨rvU2, hRvU2, ?_⟩
  exact RuleProofs.smt_value_rel_trans _ _ _ hRel1
    (smt_value_rel_re_concat_consume_local
      (RuleProofs.smt_value_rel_symm _ _ hRel2)
      (RuleProofs.smt_value_rel_refl _))

/--
ε-unit keystone massage for the eps-head cases: the unrev transform of
`re_concat eps r` extends the accumulator by `eps · eps`, which is
value-preserving, so its value is related to the value of the unrev
transform of `r`.
-/
theorem StrInReConsumeInternal.eval_unrev_re_concat_empty_left_bridge_local
    (M : SmtModel) (r : Term) (rvU : SmtRegLan)
    (hRvU :
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_re_local
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  StrInReConsumeInternal.re_empty_string_re_consume_local) r))) =
        SmtValue.RegLan rvU) :
    ∃ rvU2,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r)) =
        SmtValue.RegLan rvU2 ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan rvU)
        (SmtValue.RegLan rvU2) := by
  simp only [StrInReConsumeInternal.consume_unrev_re_local] at hRvU ⊢
  rw [__re_rev_map_rev.eq_3
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    StrInReConsumeInternal.re_empty_string_re_consume_local r (by
      intro h
      cases h)] at hRvU
  have hAccEval2 :
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_rev_comp StrInReConsumeInternal.re_empty_string_re_consume_local))
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])))) =
        SmtValue.RegLan
          (native_re_concat (native_str_to_re [])
            (native_str_to_re [])) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (SmtTerm.String []))
          (SmtTerm.str_to_re (SmtTerm.String []))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re,
     ]
  have hEpsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) = _
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M r _ rvU hRvU with
    ⟨⟨newAccV, hNewAccEval⟩, C, hTrans⟩
  rcases hTrans _ _ hAccEval2 with ⟨v1, hv1, hRel1⟩
  injection hRvU.symm.trans hv1 with hV1
  subst hV1
  rw [show native_re_concat C
      (native_re_concat (native_str_to_re []) (native_str_to_re [])) =
      C from by cases C <;> rfl] at hRel1
  rcases hTrans _ _ hEpsEval with ⟨rvU2, hRvU2, hRel2⟩
  rw [show native_re_concat C (native_str_to_re []) = C from by
    cases C <;> rfl] at hRel2
  exact ⟨rvU2, hRvU2,
    RuleProofs.smt_value_rel_trans _ _ _ hRel1
      (RuleProofs.smt_value_rel_symm _ _ hRel2)⟩

/--
Unrev semantic case for an eps head on the regex side (covers both the
concat-string and non-concat-string orientations, exactly like the
flat `str_re_consume_rec_re_concat_empty_left_semantic_from_ih`).
-/
theorem StrInReConsumeInternal.str_re_consume_rec_unrev_re_concat_empty_left_from_ih_local
    (M : SmtModel) (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (ih : StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s r fuel ∧
      StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s r fuel) :
    StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          StrInReConsumeInternal.re_empty_string_re_consume_local) r)
      fuel ∧
      StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            StrInReConsumeInternal.re_empty_string_re_consume_local) r)
        fuel := by
  have hEq :
      __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              StrInReConsumeInternal.re_empty_string_re_consume_local) r) fuel =
        __str_re_consume_rec s r fuel :=
    str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel
  constructor
  · intro side hSTy hRTy hSide hFalse hWf ssU hSsU
    have hRTy2 :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        StrInReConsumeInternal.re_empty_string_re_consume_local r hRTy).2
    have hSide' : side = __str_re_consume_rec s r fuel :=
      hSide.trans hEq
    refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
    intro rvU hRvU
    rcases StrInReConsumeInternal.eval_unrev_re_concat_empty_left_bridge_local M r rvU hRvU with
      ⟨rvU2, hRvU2, hRel⟩
    rcases (ih.1 side hSTy hRTy2 hSide' hFalse
        (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 ssU hSsU).1 rvU2
        hRvU2 with ⟨hNe, hSuf⟩
    refine ⟨hNe, ?_⟩
    intro pre suf hApp
    rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hRel]
    exact hSuf pre suf hApp
  · intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
    have hRTy2 :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        StrInReConsumeInternal.re_empty_string_re_consume_local r hRTy).2
    have hSide' : side = __str_re_consume_rec s r fuel :=
      hSide.trans hEq
    rcases ih.2 side hSTy hRTy2 hSide' hMemEps hUnrevNe
        (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 with
      ⟨hMemTyRaw, hMemTy, hRest⟩
    refine ⟨hMemTyRaw, hMemTy, ?_⟩
    intro ssU ssR hSsU hSsR
    refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
    intro rvU hRvU
    rcases StrInReConsumeInternal.eval_unrev_re_concat_empty_left_bridge_local M r rvU hRvU with
      ⟨rvU2, hRvU2, hRel⟩
    rcases (hRest ssU ssR hSsU hSsR).1 rvU2 hRvU2 with
      ⟨⟨u, hUdec, hUmem⟩, hQ⟩
    constructor
    · refine ⟨u, hUdec, ?_⟩
      rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hRel]
      exact hUmem
    · intro q qv hQv
      rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
        (smt_value_rel_re_concat_consume_local
          (RuleProofs.smt_value_rel_refl (SmtValue.RegLan qv)) hRel)]
      exact hQ q qv hQv

/--
A chunk that is not a raw `re_concat` is also a well-formed chain (the
chain predicate degenerates to the chunk predicate off the concat
spine).
-/
theorem StrInReConsumeInternal.consume_wf_chain_of_chunk_local {t : Term}
    (hNotConcat : ∀ a b,
      t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
        False)
    (h : StrInReConsumeInternal.consume_wf_chunk_local t) :
    StrInReConsumeInternal.consume_wf_chain_local t := by
  cases t <;>
    simpa [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_chunk_local,
      StrInReConsumeInternal.consume_wf_local] using h

/--
If no suffix of `w` is in `H`, then no suffix of `w` is in `A · H`
(the second factor of any witnessing split is itself a suffix).
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_no_suffix_right_false_local
    (w : native_String) (A H : SmtRegLan)
    (hAll :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf H = false) :
    ∀ pre suf : native_String,
      pre ++ suf = w ->
        native_str_in_re suf (native_re_concat A H) = false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf (native_re_concat A H) with
  | false => rfl
  | true =>
      exfalso
      have hValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf (native_re_mk_concat A H) = true := by
        have hsimpa := hMem
        try simp [native_str_in_re, native_re_concat, hValid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          H).1 hListMem with ⟨x, y, hSplit, _hX, hY⟩
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hValid)
      have hYStr : native_str_in_re y H = true := by
        simpa [native_str_in_re, hYValid] using hY
      have hYFalse := hAll (pre ++ x) y (by
        rw [List.append_assoc, hSplit]
        exact hApp)
      rw [hYFalse] at hYStr
      cases hYStr

/--
Variant of the head bridge that EXTRACTS the head value from the
evaluation of the whole unrev transform (used for the generic concat
head, where the head value is not known a priori).
-/
theorem StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local
    (M : SmtModel) (hM : model_wf M) (head r2 : Term)
    (rvU : SmtRegLan)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.RegLan)
    (hRvU :
      __smtx_model_eval M
          (__eo_to_smt
            (StrInReConsumeInternal.consume_unrev_re_local
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head)
                r2))) =
        SmtValue.RegLan rvU) :
    ∃ rvU2 headV,
      __smtx_model_eval M (__eo_to_smt (__re_rev_comp head)) =
        SmtValue.RegLan headV ∧
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2)) =
        SmtValue.RegLan rvU2 ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan rvU)
        (SmtValue.RegLan (native_re_concat rvU2 headV)) := by
  simp only [StrInReConsumeInternal.consume_unrev_re_local] at hRvU
  rw [__re_rev_map_rev.eq_3
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    head r2 (by
      intro h
      cases h)] at hRvU
  rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M r2 _ rvU hRvU with
    ⟨⟨newAccV, hNewAccEval⟩, C, hTrans⟩
  have hCompNe : __re_rev_comp head ≠ Term.Stuck := by
    intro hBad
    apply StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hNewAccEval
    rw [hBad]
    rfl
  have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
    (Term.UOp UserOp.re_concat) (__re_rev_comp head)
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (by
      intro h
      cases h) hCompNe (by
      intro h
      cases h)
  have hNewAccEval2 := hNewAccEval
  rw [hShape] at hNewAccEval2
  have hCompTy := StrInReConsumeInternal.re_rev_comp_type_local head hHeadTy hCompNe
  have hConcTy := smt_typeof_re_concat_of_reglan_consume_local
    (__re_rev_comp head)
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    hCompTy StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local
  rcases eval_re_concat_parts_consume_local M hM _ _ newAccV hConcTy
      hNewAccEval2 with
    ⟨headV, epsV, _hHTy2, _hETy2, hCompEval, hEpsEval2, hAccVEq⟩
  have hEpsEvalConc :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) = _
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
     ]
  have hEpsVEq : epsV = native_str_to_re [] := by
    injection hEpsEval2.symm.trans hEpsEvalConc
  subst hEpsVEq
  subst hAccVEq
  rcases hTrans _ _ hNewAccEval with ⟨v1, hv1, hRel1⟩
  injection hRvU.symm.trans hv1 with hV1Eq
  subst hV1Eq
  rw [show native_re_concat headV (native_str_to_re []) = headV from by
    cases headV <;> rfl] at hRel1
  rcases hTrans _ _ hEpsEvalConc with ⟨rvU2, hRvU2, hRel2⟩
  rw [show native_re_concat C (native_str_to_re []) = C from by
    cases C <;> rfl] at hRel2
  refine ⟨rvU2, headV, hCompEval, hRvU2, ?_⟩
  exact RuleProofs.smt_value_rel_trans _ _ _ hRel1
    (smt_value_rel_re_concat_consume_local
      (RuleProofs.smt_value_rel_symm _ _ hRel2)
      (RuleProofs.smt_value_rel_refl _))

/--
No-suffix composition for the generic concat head: the tail residual's
LEFT-continuation ∀q equality (instantiated at prefix-singleton
continuations `{pre} · rvU2`) turns a witnessing suffix split of
`w' ++ u` in `rvU2 · headV` into a suffix of `w'` in `rvU2`,
contradicting the tail's no-suffix conclusion.
-/
theorem StrInReConsumeInternal.consume_no_suffix_concat_of_residual_local
    (M : SmtModel)
    (w' u : native_String) (rvU2 headV : SmtRegLan) (r2 : Term)
    (hRvU2 :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2)) =
        SmtValue.RegLan rvU2)
    (hWValid : native_string_valid (w' ++ u) = true)
    (hSufR2 :
      ∀ pre suf : native_String,
        pre ++ suf = w' -> native_str_in_re suf rvU2 = false)
    (hQ :
      ∀ q qv,
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (w' ++ u) (native_re_concat qv headV) =
            native_str_in_re w' qv) :
    ∀ pre suf : native_String,
      pre ++ suf = w' ++ u ->
        native_str_in_re suf (native_re_concat rvU2 headV) = false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf (native_re_concat rvU2 headV) with
  | false => rfl
  | true =>
      exfalso
      have hPreValid : native_string_valid pre = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local pre suf (by
          rw [hApp]
          exact hWValid)
      have hQEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String pre)))
                  (StrInReConsumeInternal.consume_unrev_re_local r2))) =
            SmtValue.RegLan
              (native_re_concat (native_str_to_re pre) rvU2) := by
        change __smtx_model_eval M
            (SmtTerm.re_concat
              (SmtTerm.str_to_re (SmtTerm.String pre))
              (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2))) = _
        simp [__smtx_model_eval, __smtx_model_eval_re_concat,
          __smtx_model_eval_str_to_re, hRvU2,
         ]
      have hEq := hQ _ _ hQEval
      have hLhs :
          native_str_in_re (w' ++ u)
              (native_re_concat
                (native_re_concat (native_str_to_re pre) rvU2)
                headV) =
            true := by
        rw [← hApp]
        rw [native_str_in_re_re_concat_assoc_consume_local]
        exact native_str_in_re_re_concat_intro pre suf _ _
          (native_str_in_re_str_to_re_self_local pre hPreValid) hMem
      rw [hEq] at hLhs
      have hW'Valid : native_string_valid w' = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local w' u hWValid
      have hListMem :
          nativeListInRe w'
              (native_re_mk_concat (native_str_to_re pre) rvU2) =
            true := by
        have hsimpa := hLhs
        try simp [native_str_in_re, native_re_concat, hW'Valid] at hsimpa ⊢
        exact hsimpa
      rcases (nativeListInRe_mk_concat_true_iff_exists_append w' _
          _).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
      have hXValid : native_string_valid x = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
          rw [hSplit]
          exact hW'Valid)
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hW'Valid)
      have hXStr :
          native_str_in_re x (native_str_to_re pre) = true := by
        simpa [native_str_in_re, hXValid] using hX
      have hXPre : x = pre := native_str_in_re_str_to_re_eq hXValid hXStr
      subst hXPre
      have hYStr : native_str_in_re y rvU2 = true := by
        simpa [native_str_in_re, hYValid] using hY
      rw [hSufR2 x y hSplit] at hYStr
      cases hYStr

/--
Unrev semantic case for the generic (non-eps/str_to_re/range/allchar/
mult) concat head: the well-formedness guard forces the head to be a
non-concat chunk, so its `__re_rev_comp` conclusions from the left IH
apply, and the tail residual composes via the LEFT-continuation ∀q
equalities.
-/
theorem StrInReConsumeInternal.str_re_consume_rec_unrev_str_concat_re_concat_from_ih_local
    (M : SmtModel) (hM : model_wf M)
    (s1 s2 r1 r2 fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hR1Empty :
      r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    (hR1StrToRe :
      ∀ s3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.str_to_re) s3)
    (hR1Range :
      ∀ s3 s5 : Term,
        r1 ≠ Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
    (hR1Allchar : r1 ≠ Term.UOp UserOp.re_allchar)
    (hFuelMult :
      ∀ r3 fc fr : Term,
        fuel = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr ->
        r1 = Term.Apply (Term.UOp UserOp.re_mult) r3 ->
        False)
    (hR1Mult :
      ∀ r3 : Term, r1 ≠ Term.Apply (Term.UOp UserOp.re_mult) r3)
    (ihLeft :
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          r1 fuel ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          r1 fuel)
    (ihResidual :
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2)
              r1 fuel))
          r2 fuel ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M
          (__str_membership_str
            (__str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2)
              r1 fuel))
          r2 fuel) :
    StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel ∧
      StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        fuel := by
  constructor
  · -- no-suffix component
    intro side hSTy hRTy hSide hFalse hWf ssU hSsU
    have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
    have hR1NotConcat : ∀ a b,
        r1 = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False := by
      intro a b hEq
      rw [hEq] at hWfParts
      have hBad := hWfParts.1
      simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using hBad
    have hWfR1 : StrInReConsumeInternal.consume_wf_chain_local r1 :=
      StrInReConsumeInternal.consume_wf_chain_of_chunk_local hR1NotConcat hWfParts.1
    have hR1Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).1
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).2
    rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
      hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult] at hSide
    have hIteFalse := hSide.symm.trans hFalse
    refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
    intro rvU hRvU
    rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM r1 r2
        rvU hR1Ty hRvU with ⟨rvU2, headV, hCompEval, hRvU2, hRvURel⟩
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [hIteFalse]
          intro h
          cases h) with hLF | hLNF
    · -- left result is false: the head alone kills every suffix
      have hLeftEqFalse :
          __str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                s2)
              r1 fuel = Term.Boolean false :=
        eq_of_eo_is_eq_true_consume_local _ _ hLF
      rcases (ihLeft.1 (Term.Boolean false) hSTy hR1Ty
          hLeftEqFalse.symm rfl hWfR1 ssU hSsU).2 hR1NotConcat headV
          hCompEval with ⟨hNe1, hSufHead⟩
      refine ⟨hNe1, ?_⟩
      intro pre suf hApp
      rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hRvURel
        suf]
      exact StrInReConsumeInternal.native_str_in_re_concat_no_suffix_right_false_local
        (native_unpack_string ssU) rvU2 headV hSufHead pre suf hApp
    · rw [hLNF] at hIteFalse
      simp only [eo_ite_false] at hIteFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hME | hMNE
      · -- head fully consumed, tail consume returned false
        rw [hME] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        have hMemEpsEq :
            __str_membership_re
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel) =
              StrInReConsumeInternal.re_empty_string_re_consume_local :=
          eq_of_eo_is_eq_true_consume_local _ _ hME
        have hUnrevNeS :
            StrInReConsumeInternal.consume_unrev_str_local
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                  s1) s2) ≠ Term.Stuck :=
          StrInReConsumeInternal.consume_unrev_str_ne_stuck_of_eval_local M _ ssU hSsU
        rcases ihLeft.2 _ hSTy hR1Ty rfl hMemEpsEq hUnrevNeS hWfR1 with
          ⟨hMemTyRawL, hMemTy, hRestL⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M
            hM _ hMemTy with ⟨ssR', hSsR'⟩
        rcases hRestL ssU ssR' hSsU hSsR' with ⟨_hChainVer, hCompVer⟩
        rcases hCompVer hR1NotConcat headV hCompEval with
          ⟨⟨u, hUdec, hUmem⟩, hQ⟩
        rcases (ihResidual.1 (Term.Boolean false) hMemTyRawL hR2Ty
            hIteFalse.symm rfl hWfParts.2 ssR' hSsR').1 rvU2 hRvU2 with
          ⟨hNeR2, hSufR2⟩
        have hUnrevTy :
            __smtx_typeof
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_str_local
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) s1)
                      s2))) =
              SmtType.Seq SmtType.Char := by
          simp only [StrInReConsumeInternal.consume_unrev_str_local]
          exact smt_typeof_list_rev_str_concat_of_seq _ SmtType.Char
            (eo_list_rev_is_list_true_of_ne_stuck _ _
              (by simpa [StrInReConsumeInternal.consume_unrev_str_local] using hUnrevNeS))
            hSTy (by simpa [StrInReConsumeInternal.consume_unrev_str_local] using hUnrevNeS)
        have hWValid :
            native_string_valid (native_unpack_string ssU) = true := by
          have h := smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt
              (StrInReConsumeInternal.consume_unrev_str_local
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)))
            (by
              unfold term_has_non_none_type
              rw [hUnrevTy]
              simp)
          rw [hSsU, hUnrevTy] at h
          exact native_unpack_string_valid_of_typeof_seq_char h
        refine ⟨?_, ?_⟩
        · rw [hUdec]
          exact StrInReConsumeInternal.list_append_ne_nil_left_consume_local _ _ hNeR2
        · intro pre suf hApp
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel suf]
          have hQ' : ∀ q qv,
              __smtx_model_eval M (__eo_to_smt q) =
                SmtValue.RegLan qv ->
              native_str_in_re (native_unpack_string ssR' ++ u)
                  (native_re_concat qv headV) =
                native_str_in_re (native_unpack_string ssR') qv := by
            intro q qv hQv
            have h := hQ q qv hQv
            rw [hUdec] at h
            exact h
          have hWValid' :
              native_string_valid
                  (native_unpack_string ssR' ++ u) = true := by
            rw [← hUdec]
            exact hWValid
          have hApp' : pre ++ suf = native_unpack_string ssR' ++ u := by
            rw [← hUdec]
            exact hApp
          exact StrInReConsumeInternal.consume_no_suffix_concat_of_residual_local M
            (native_unpack_string ssR') u rvU2 headV r2 hRvU2
            hWValid' hSufR2 hQ' pre suf hApp'
      · -- fallback rebuild cannot be `false`
        exfalso
        rw [hMNE] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        cases hIteFalse
  · -- residual component
    intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
    have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
    have hR1NotConcat : ∀ a b,
        r1 = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False := by
      intro a b hEq
      rw [hEq] at hWfParts
      have hBad := hWfParts.1
      simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using hBad
    have hWfR1 : StrInReConsumeInternal.consume_wf_chain_local r1 :=
      StrInReConsumeInternal.consume_wf_chain_of_chunk_local hR1NotConcat hWfParts.1
    have hR1Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).1
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).2
    rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
      hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult] at hSide
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEps
      simp [__str_membership_re] at hMemEps
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hLF | hLNF
    · exfalso
      rw [hLF] at hSide
      simp only [eo_ite_true] at hSide
      rw [hSide] at hMemEps
      simp [__str_membership_re] at hMemEps
    · rw [hLNF] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hME | hMNE
      · rw [hME] at hSide
        simp only [eo_ite_true] at hSide
        have hMemEpsEqL :
            __str_membership_re
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel) =
              StrInReConsumeInternal.re_empty_string_re_consume_local :=
          eq_of_eo_is_eq_true_consume_local _ _ hME
        rcases ihLeft.2 _ hSTy hR1Ty rfl hMemEpsEqL hUnrevNe hWfR1 with
          ⟨hMemTyRawL, hMemTyL, hRestL⟩
        have hMemTransNeL :
            StrInReConsumeInternal.consume_unrev_str_local
                (__str_membership_str
                  (__str_re_consume_rec
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                    r1 fuel)) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hMemTyL
          rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl]
            at hMemTyL
          rw [TranslationProofs.smtx_typeof_none] at hMemTyL
          cases hMemTyL
        rcases ihResidual.2 side hMemTyRawL hR2Ty hSide hMemEps
            hMemTransNeL hWfParts.2 with ⟨hMemTyRawR, hMemTyR, hRestR⟩
        refine ⟨hMemTyRawR, hMemTyR, ?_⟩
        intro ssU ssR hSsU hSsR
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM r1
            r2 rvU hR1Ty hRvU with
          ⟨rvU2, headV, hCompEval, hRvU2, hRvURel⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M
            hM _ hMemTyL with ⟨ssR', hSsR'⟩
        rcases hRestL ssU ssR' hSsU hSsR' with ⟨_hChainL, hCompVerL⟩
        rcases hCompVerL hR1NotConcat headV hCompEval with
          ⟨⟨u1, hU1dec, hU1mem⟩, hQ1⟩
        rcases hRestR ssR' ssR hSsR' hSsR with ⟨hChainVerR, _⟩
        rcases hChainVerR rvU2 hRvU2 with ⟨⟨u2, hU2dec, hU2mem⟩, hQ2⟩
        constructor
        · refine ⟨u2 ++ u1, ?_, ?_⟩
          · rw [hU1dec, hU2dec, List.append_assoc]
          · rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel]
            exact native_str_in_re_re_concat_intro u2 u1 rvU2 headV
              hU2mem hU1mem
        · intro q qv hQv
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_refl _) hRvURel) _]
          rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_assoc_consume_local qv rvU2
              headV) _]
          have hQ'Eval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat) q)
                      (StrInReConsumeInternal.consume_unrev_re_local r2))) =
                SmtValue.RegLan (native_re_concat qv rvU2) := by
            change __smtx_model_eval M
                (SmtTerm.re_concat (__eo_to_smt q)
                  (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2))) = _
            simp [__smtx_model_eval, __smtx_model_eval_re_concat,
              hQv, hRvU2]
          rw [hQ1 _ _ hQ'Eval]
          exact hQ2 q qv hQv
      · exfalso
        rw [hMNE] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide] at hMemEps
        simp [__str_membership_re] at hMemEps

/--
Value decomposition of `__re_rev_comp` on a union tree: the left
component is the CHAIN transform of `c1`, the right is `__re_rev_comp`
of the tail.
-/
theorem StrInReConsumeInternal.re_rev_comp_union_decomp_local
    (M : SmtModel) (hM : model_wf M) (c1 c2 : Term)
    (rvU : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
              c2)) =
        SmtType.RegLan)
    (hRvU :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
                c2))) =
        SmtValue.RegLan rvU) :
    ∃ v1 v2,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local c1)) =
        SmtValue.RegLan v1 ∧
      __smtx_model_eval M (__eo_to_smt (__re_rev_comp c2)) =
        SmtValue.RegLan v2 ∧
      rvU = native_re_union v1 v2 := by
  have hNe := StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
  have hLeftNe :
      __re_rev_map_rev c1 StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck := by
    intro hBad
    apply hNe
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_union)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = Term.Stuck
    rw [show __re_rev_map_rev c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Stuck from hBad]
    rfl
  have hRightNe : __re_rev_comp c2 ≠ Term.Stuck := by
    intro hBad
    apply hNe
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_union)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = Term.Stuck
    rw [hBad]
    cases __eo_mk_apply (Term.UOp UserOp.re_union)
        (__re_rev_map_rev c1
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) <;>
      rfl
  have hShape :
      __re_rev_comp
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp c2) := by
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_union)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = _
    exact StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
      (Term.UOp UserOp.re_union) _ _ (by
        intro h
        cases h) hLeftNe hRightNe
  rw [hShape] at hRvU
  have hC1Ty :=
    (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hTy).1
  have hC2Ty :=
    (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hTy).2
  have hLeftTy :=
    (StrInReConsumeInternal.re_rev_map_rev_type_facts_local c1 _ hC1Ty
      StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
      StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hLeftNe).2.1
  have hRightTy := StrInReConsumeInternal.re_rev_comp_type_local c2 hC2Ty hRightNe
  have hUnionTy := smt_typeof_re_union_of_reglan_consume_local _ _
    hLeftTy hRightTy
  rcases eval_re_union_parts_consume_local M hM _ _ rvU hUnionTy
      hRvU with ⟨v1, v2, _hT1, _hT2, hV1, hV2, hEq⟩
  exact ⟨v1, v2, hV1, hV2, hEq⟩

/--
Value decomposition of `__re_rev_comp` on an inter tree.
-/
theorem StrInReConsumeInternal.re_rev_comp_inter_decomp_local
    (M : SmtModel) (hM : model_wf M) (c1 c2 : Term)
    (rvU : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
              c2)) =
        SmtType.RegLan)
    (hRvU :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
                c2))) =
        SmtValue.RegLan rvU) :
    ∃ v1 v2,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local c1)) =
        SmtValue.RegLan v1 ∧
      __smtx_model_eval M (__eo_to_smt (__re_rev_comp c2)) =
        SmtValue.RegLan v2 ∧
      rvU = native_re_inter v1 v2 := by
  have hNe := StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
  have hLeftNe :
      __re_rev_map_rev c1 StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck := by
    intro hBad
    apply hNe
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_inter)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = Term.Stuck
    rw [show __re_rev_map_rev c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Stuck from hBad]
    rfl
  have hRightNe : __re_rev_comp c2 ≠ Term.Stuck := by
    intro hBad
    apply hNe
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_inter)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = Term.Stuck
    rw [hBad]
    cases __eo_mk_apply (Term.UOp UserOp.re_inter)
        (__re_rev_map_rev c1
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) <;>
      rfl
  have hShape :
      __re_rev_comp
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp c2) := by
    show __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.re_inter)
          (__re_rev_map_rev c1
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (__re_rev_comp c2) = _
    exact StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
      (Term.UOp UserOp.re_inter) _ _ (by
        intro h
        cases h) hLeftNe hRightNe
  rw [hShape] at hRvU
  have hC1Ty :=
    (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hTy).1
  have hC2Ty :=
    (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hTy).2
  have hLeftTy :=
    (StrInReConsumeInternal.re_rev_map_rev_type_facts_local c1 _ hC1Ty
      StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
      StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hLeftNe).2.1
  have hRightTy := StrInReConsumeInternal.re_rev_comp_type_local c2 hC2Ty hRightNe
  have hInterTy := smt_typeof_re_inter_of_reglan_consume_local _ _
    hLeftTy hRightTy
  rcases eval_re_inter_parts_consume_local M hM _ _ rvU hInterTy
      hRvU with ⟨v1, v2, _hT1, _hT2, hV1, hV2, hEq⟩
  exact ⟨v1, v2, hV1, hV2, hEq⟩

/--
∀q composition through a union whose LEFT branch admits no suffix of
`w`: membership through the union must go through the right branch.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_union_left_no_suffix_eq_local
    (w w' : native_String) (qv v1 v2 : SmtRegLan)
    (hNoSuf :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf v1 = false)
    (hEq :
      native_str_in_re w (native_re_concat qv v2) =
        native_str_in_re w' qv) :
    native_str_in_re w (native_re_concat qv (native_re_union v1 v2)) =
      native_str_in_re w' qv := by
  cases hWV : native_string_valid w with
  | false =>
      have hLhs :
          native_str_in_re w
              (native_re_concat qv (native_re_union v1 v2)) = false := by
        simp [native_str_in_re, hWV]
      have hLhs2 :
          native_str_in_re w (native_re_concat qv v2) = false := by
        simp [native_str_in_re, hWV]
      rw [hLhs, ← hEq, hLhs2]
  | true =>
      rw [← hEq]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat qv (native_re_union v1 v2)) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            _).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYStr :
            native_str_in_re y (native_re_union v1 v2) = true := by
          simpa [native_str_in_re, hYValid] using hY
        rw [native_str_in_re_re_union] at hYStr
        cases hY1 : native_str_in_re y v1 with
        | true =>
            exfalso
            have hBad := hNoSuf x y hSplit
            rw [hBad] at hY1
            cases hY1
        | false =>
            rw [hY1] at hYStr
            simp at hYStr
            have hXStr : native_str_in_re x qv = true := by
              simpa [native_str_in_re, hXValid] using hX
            rw [← hSplit]
            exact native_str_in_re_re_concat_intro x y qv v2 hXStr
              hYStr
      · intro hMem
        have hListMem :
            nativeListInRe w (native_re_mk_concat qv v2) = true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            v2).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYU :
            native_str_in_re y (native_re_union v1 v2) = true := by
          rw [native_str_in_re_re_union]
          rw [show native_str_in_re y v2 = true from by
            simpa [native_str_in_re, hYValid] using hY]
          simp
        have hXStr : native_str_in_re x qv = true := by
          simpa [native_str_in_re, hXValid] using hX
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro x y qv _ hXStr hYU

/--
Mirror of the previous lemma with the union branches swapped.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_union_right_no_suffix_eq_local
    (w w' : native_String) (qv v1 v2 : SmtRegLan)
    (hNoSuf :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf v2 = false)
    (hEq :
      native_str_in_re w (native_re_concat qv v1) =
        native_str_in_re w' qv) :
    native_str_in_re w (native_re_concat qv (native_re_union v1 v2)) =
      native_str_in_re w' qv := by
  cases hWV : native_string_valid w with
  | false =>
      have hLhs :
          native_str_in_re w
              (native_re_concat qv (native_re_union v1 v2)) = false := by
        simp [native_str_in_re, hWV]
      have hLhs2 :
          native_str_in_re w (native_re_concat qv v1) = false := by
        simp [native_str_in_re, hWV]
      rw [hLhs, ← hEq, hLhs2]
  | true =>
      rw [← hEq]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat qv (native_re_union v1 v2)) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            _).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYStr :
            native_str_in_re y (native_re_union v1 v2) = true := by
          simpa [native_str_in_re, hYValid] using hY
        rw [native_str_in_re_re_union] at hYStr
        cases hY2 : native_str_in_re y v2 with
        | true =>
            exfalso
            have hBad := hNoSuf x y hSplit
            rw [hBad] at hY2
            cases hY2
        | false =>
            rw [hY2] at hYStr
            simp at hYStr
            have hXStr : native_str_in_re x qv = true := by
              simpa [native_str_in_re, hXValid] using hX
            rw [← hSplit]
            exact native_str_in_re_re_concat_intro x y qv v1 hXStr
              hYStr
      · intro hMem
        have hListMem :
            nativeListInRe w (native_re_mk_concat qv v1) = true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            v1).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYU :
            native_str_in_re y (native_re_union v1 v2) = true := by
          rw [native_str_in_re_re_union]
          rw [show native_str_in_re y v1 = true from by
            simpa [native_str_in_re, hYValid] using hY]
          simp
        have hXStr : native_str_in_re x qv = true := by
          simpa [native_str_in_re, hXValid] using hX
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro x y qv _ hXStr hYU

/--
∀q composition through a union when BOTH branches satisfy the same
residual equality.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_union_both_eq_local
    (w w' : native_String) (qv v1 v2 : SmtRegLan)
    (hEq1 :
      native_str_in_re w (native_re_concat qv v1) =
        native_str_in_re w' qv)
    (hEq2 :
      native_str_in_re w (native_re_concat qv v2) =
        native_str_in_re w' qv) :
    native_str_in_re w (native_re_concat qv (native_re_union v1 v2)) =
      native_str_in_re w' qv := by
  cases hWV : native_string_valid w with
  | false =>
      have hLhs :
          native_str_in_re w
              (native_re_concat qv (native_re_union v1 v2)) = false := by
        simp [native_str_in_re, hWV]
      have hLhs2 :
          native_str_in_re w (native_re_concat qv v1) = false := by
        simp [native_str_in_re, hWV]
      rw [hLhs, ← hEq1, hLhs2]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat qv (native_re_union v1 v2)) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            _).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYStr :
            native_str_in_re y (native_re_union v1 v2) = true := by
          simpa [native_str_in_re, hYValid] using hY
        have hXStr : native_str_in_re x qv = true := by
          simpa [native_str_in_re, hXValid] using hX
        rw [native_str_in_re_re_union] at hYStr
        cases hY1 : native_str_in_re y v1 with
        | true =>
            have hW1 :
                native_str_in_re w (native_re_concat qv v1) = true := by
              rw [← hSplit]
              exact native_str_in_re_re_concat_intro x y qv v1 hXStr
                hY1
            rw [hEq1] at hW1
            rw [hW1]
        | false =>
            rw [hY1] at hYStr
            simp at hYStr
            have hW2 :
                native_str_in_re w (native_re_concat qv v2) = true := by
              rw [← hSplit]
              exact native_str_in_re_re_concat_intro x y qv v2 hXStr
                hYStr
            rw [hEq2] at hW2
            rw [hW2]
      · intro hMem
        have hW1 :
            native_str_in_re w (native_re_concat qv v1) = true := by
          rw [hEq1]
          exact hMem
        have hListMem :
            nativeListInRe w (native_re_mk_concat qv v1) = true := by
          have hsimpa := hW1
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            v1).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYU :
            native_str_in_re y (native_re_union v1 v2) = true := by
          rw [native_str_in_re_re_union]
          rw [show native_str_in_re y v1 = true from by
            simpa [native_str_in_re, hYValid] using hY]
          simp
        have hXStr : native_str_in_re x qv = true := by
          simpa [native_str_in_re, hXValid] using hX
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro x y qv _ hXStr hYU

/--
∀q composition through an intersection when the residual word is a
member of BOTH branches and the LEFT branch satisfies the residual
equality.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_inter_both_eq_local
    (w w' u : native_String) (qv v1 v2 : SmtRegLan)
    (hWdec : w = w' ++ u)
    (hU1 : native_str_in_re u v1 = true)
    (hU2 : native_str_in_re u v2 = true)
    (hEq1 :
      native_str_in_re w (native_re_concat qv v1) =
        native_str_in_re w' qv) :
    native_str_in_re w (native_re_concat qv (native_re_inter v1 v2)) =
      native_str_in_re w' qv := by
  cases hWV : native_string_valid w with
  | false =>
      have hLhs :
          native_str_in_re w
              (native_re_concat qv (native_re_inter v1 v2)) = false := by
        simp [native_str_in_re, hWV]
      have hLhs2 :
          native_str_in_re w (native_re_concat qv v1) = false := by
        simp [native_str_in_re, hWV]
      rw [hLhs, ← hEq1, hLhs2]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat qv (native_re_inter v1 v2)) =
              true := by
          have hsimpa := hMem
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            _).1 hListMem with ⟨x, y, hSplit, hX, hY⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYStr :
            native_str_in_re y (native_re_inter v1 v2) = true := by
          simpa [native_str_in_re, hYValid] using hY
        rw [native_str_in_re_re_inter] at hYStr
        have hY1 : native_str_in_re y v1 = true := by
          cases h1 : native_str_in_re y v1 with
          | true => rfl
          | false =>
              rw [h1] at hYStr
              simp at hYStr
        have hXStr : native_str_in_re x qv = true := by
          simpa [native_str_in_re, hXValid] using hX
        have hW1 :
            native_str_in_re w (native_re_concat qv v1) = true := by
          rw [← hSplit]
          exact native_str_in_re_re_concat_intro x y qv v1 hXStr hY1
        rw [hEq1] at hW1
        rw [hW1]
      · intro hMem
        have hUInter :
            native_str_in_re u (native_re_inter v1 v2) = true := by
          rw [native_str_in_re_re_inter, hU1, hU2]
          rfl
        rw [hWdec]
        exact native_str_in_re_re_concat_intro w' u qv _ hMem hUInter

/--
Unrev semantic case for the union combinator.
-/
theorem StrInReConsumeInternal.str_re_consume_union_unrev_from_ih_local
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_none)
    (ihLeft :
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s c1 fuel ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s c1 fuel)
    (ihRight :
      StrInReConsumeInternal.str_re_consume_union_unrev_no_suffix_motive M s c2 fuel ∧
        StrInReConsumeInternal.str_re_consume_union_unrev_residual_motive M s c2 fuel) :
    StrInReConsumeInternal.str_re_consume_union_unrev_no_suffix_motive M s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel ∧
      StrInReConsumeInternal.str_re_consume_union_unrev_residual_motive M s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2)
        fuel := by
  constructor
  · -- no-suffix component
    intro side hSTy hRTy hSide hFalse hWf ssU hSsU rvU hRvU
    have hWfParts := StrInReConsumeInternal.consume_wf_union_tail_parts_local hWf
    have hC1Ty :=
      (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hRTy).1
    have hC2Ty :=
      (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hRTy).2
    rcases StrInReConsumeInternal.re_rev_comp_union_decomp_local M hM c1 c2 rvU hRTy hRvU with
      ⟨v1, v2, hV1, hV2, hRvUEq⟩
    subst hRvUEq
    rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
      at hSide
    have hIteFalse := hSide.symm.trans hFalse
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [hIteFalse]
          intro h
          cases h) with hLFT | hLFF
    · rw [hLFT] at hIteFalse
      simp only [eo_ite_true] at hIteFalse
      have hLeftEqFalse := eq_of_eo_is_eq_true_consume_local _ _ hLFT
      rcases (ihLeft.1 (Term.Boolean false) hSTy hC1Ty
          hLeftEqFalse.symm rfl hWfParts.1 ssU hSsU).1 v1 hV1 with
        ⟨hNe1, hSuf1⟩
      rcases ihRight.1 (Term.Boolean false) hSTy hC2Ty hIteFalse.symm
          rfl hWfParts.2 ssU hSsU v2 hV2 with ⟨_hNe2, hSuf2⟩
      refine ⟨hNe1, ?_⟩
      intro pre suf hApp
      rw [native_str_in_re_re_union, hSuf1 pre suf hApp,
        hSuf2 pre suf hApp]
      rfl
    · rw [hLFF] at hIteFalse
      simp only [eo_ite_false] at hIteFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hMT | hMF
      · rw [hMT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hRFT | hRFF
        · exfalso
          rw [hRFT] at hIteFalse
          simp only [eo_ite_true] at hIteFalse
          rw [hIteFalse] at hLFF
          simp [__eo_is_eq, native_teq, native_and, native_not,
            SmtEval.native_and, SmtEval.native_not] at hLFF
        · rw [hRFF] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [hIteFalse]
                intro h
                cases h) with hST | hSF
          · exfalso
            rw [hST] at hIteFalse
            simp only [eo_ite_true] at hIteFalse
            rw [hIteFalse] at hLFF
            simp [__eo_is_eq, native_teq, native_and, native_not,
              SmtEval.native_and, SmtEval.native_not] at hLFF
          · exfalso
            rw [hSF] at hIteFalse
            simp only [eo_ite_false] at hIteFalse
            cases hIteFalse
      · exfalso
        rw [hMF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        cases hIteFalse
  · -- residual component
    intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
    have hWfParts := StrInReConsumeInternal.consume_wf_union_tail_parts_local hWf
    have hC1Ty :=
      (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hRTy).1
    have hC2Ty :=
      (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2 hRTy).2
    rw [__str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
      at hSide
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEps
      simp [__str_membership_re] at hMemEps
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hLFT | hLFF
    · -- side is the right (union-tail) result
      rw [hLFT] at hSide
      simp only [eo_ite_true] at hSide
      have hLeftEqFalse := eq_of_eo_is_eq_true_consume_local _ _ hLFT
      rcases ihRight.2 side hSTy hC2Ty hSide hMemEps hUnrevNe
          hWfParts.2 with ⟨hMemTyRaw, hMemTy, hRest⟩
      refine ⟨hMemTyRaw, hMemTy, ?_⟩
      intro ssU ssR hSsU hSsR rvU hRvU
      rcases StrInReConsumeInternal.re_rev_comp_union_decomp_local M hM c1 c2 rvU hRTy
          hRvU with ⟨v1, v2, hV1, hV2, hRvUEq⟩
      subst hRvUEq
      rcases (ihLeft.1 (Term.Boolean false) hSTy hC1Ty
          hLeftEqFalse.symm rfl hWfParts.1 ssU hSsU).1 v1 hV1 with
        ⟨_hNe1, hSuf1⟩
      rcases hRest ssU ssR hSsU hSsR v2 hV2 with
        ⟨⟨u, hUdec, hUmem⟩, hQ⟩
      constructor
      · refine ⟨u, hUdec, ?_⟩
        rw [native_str_in_re_re_union, hUmem]
        simp
      · intro q qv hQv
        exact StrInReConsumeInternal.native_str_in_re_concat_union_left_no_suffix_eq_local
          (native_unpack_string ssU) (native_unpack_string ssR) qv
          v1 v2 hSuf1 (hQ q qv hQv)
    · rw [hLFF] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hMT | hMF
      · rw [hMT] at hSide
        simp only [eo_ite_true] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hRFT | hRFF
        · -- side is the left (rec) result; right consume was false
          rw [hRFT] at hSide
          simp only [eo_ite_true] at hSide
          have hRightEqFalse :=
            eq_of_eo_is_eq_true_consume_local _ _ hRFT
          rcases ihLeft.2 side hSTy hC1Ty hSide hMemEps hUnrevNe
              hWfParts.1 with ⟨hMemTyRaw, hMemTy, hRest⟩
          refine ⟨hMemTyRaw, hMemTy, ?_⟩
          intro ssU ssR hSsU hSsR rvU hRvU
          rcases StrInReConsumeInternal.re_rev_comp_union_decomp_local M hM c1 c2 rvU hRTy
              hRvU with ⟨v1, v2, hV1, hV2, hRvUEq⟩
          subst hRvUEq
          rcases ihRight.1 (Term.Boolean false) hSTy hC2Ty
              hRightEqFalse.symm rfl hWfParts.2 ssU hSsU v2 hV2 with
            ⟨_hNe2, hSuf2⟩
          rcases (hRest ssU ssR hSsU hSsR).1 v1 hV1 with
            ⟨⟨u, hUdec, hUmem⟩, hQ⟩
          constructor
          · refine ⟨u, hUdec, ?_⟩
            rw [native_str_in_re_re_union, hUmem]
            simp
          · intro q qv hQv
            exact
              StrInReConsumeInternal.native_str_in_re_concat_union_right_no_suffix_eq_local
                (native_unpack_string ssU) (native_unpack_string ssR)
                qv v1 v2 hSuf2 (hQ q qv hQv)
        · rw [hRFF] at hSide
          simp only [eo_ite_false] at hSide
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [← hSide]
                exact hSideNe) with hST | hSF
          · -- both branches produced the SAME rebuilt result
            rw [hST] at hSide
            simp only [eo_ite_true] at hSide
            have hSameEq :
                __str_re_consume_rec s c1 fuel =
                  __str_re_consume_union s c2 fuel :=
              (eq_of_eo_eq_true _ _ hST).symm
            rcases ihLeft.2 side hSTy hC1Ty hSide hMemEps hUnrevNe
                hWfParts.1 with ⟨hMemTyRaw, hMemTy, hRestL⟩
            rcases ihRight.2 side hSTy hC2Ty (hSide.trans hSameEq)
                hMemEps hUnrevNe hWfParts.2 with ⟨_, _, hRestR⟩
            refine ⟨hMemTyRaw, hMemTy, ?_⟩
            intro ssU ssR hSsU hSsR rvU hRvU
            rcases StrInReConsumeInternal.re_rev_comp_union_decomp_local M hM c1 c2 rvU hRTy
                hRvU with ⟨v1, v2, hV1, hV2, hRvUEq⟩
            subst hRvUEq
            rcases (hRestL ssU ssR hSsU hSsR).1 v1 hV1 with
              ⟨⟨u1, hU1dec, hU1mem⟩, hQ1⟩
            rcases hRestR ssU ssR hSsU hSsR v2 hV2 with
              ⟨⟨u2, hU2dec, hU2mem⟩, hQ2⟩
            have hU12 : u1 = u2 :=
              List.append_cancel_left (hU1dec.symm.trans hU2dec)
            subst hU12
            constructor
            · refine ⟨u1, hU1dec, ?_⟩
              rw [native_str_in_re_re_union, hU1mem]
              simp
            · intro q qv hQv
              exact StrInReConsumeInternal.native_str_in_re_concat_union_both_eq_local
                (native_unpack_string ssU) (native_unpack_string ssR)
                qv v1 v2 (hQ1 q qv hQv) (hQ2 q qv hQv)
          · exfalso
            rw [hSF] at hSide
            simp only [eo_ite_false] at hSide
            rw [hSide] at hMemEps
            simp [__str_membership_re] at hMemEps
      · exfalso
        rw [hMF] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide] at hMemEps
        simp [__str_membership_re] at hMemEps

/--
Unrev semantic case for the inter combinator.
-/
theorem StrInReConsumeInternal.str_re_consume_inter_unrev_from_ih_local
    (M : SmtModel) (hM : model_wf M)
    (s c1 c2 fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hC2Ne : c2 ≠ Term.UOp UserOp.re_all)
    (ihRec :
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s c1 fuel ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s c1 fuel)
    (ihInter :
      StrInReConsumeInternal.str_re_consume_inter_unrev_no_suffix_motive M s c2 fuel ∧
        StrInReConsumeInternal.str_re_consume_inter_unrev_residual_motive M s c2 fuel) :
    StrInReConsumeInternal.str_re_consume_inter_unrev_no_suffix_motive M s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel ∧
      StrInReConsumeInternal.str_re_consume_inter_unrev_residual_motive M s
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2)
        fuel := by
  constructor
  · -- no-suffix component
    intro side hSTy hRTy hSide hFalse hWf ssU hSsU rvU hRvU
    have hWfParts := StrInReConsumeInternal.consume_wf_inter_tail_parts_local hWf
    have hC1Ty :=
      (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hRTy).1
    have hC2Ty :=
      (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hRTy).2
    rcases StrInReConsumeInternal.re_rev_comp_inter_decomp_local M hM c1 c2 rvU hRTy hRvU with
      ⟨v1, v2, hV1, hV2, hRvUEq⟩
    subst hRvUEq
    rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
      at hSide
    have hIteFalse := hSide.symm.trans hFalse
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [hIteFalse]
          intro h
          cases h) with hV3FT | hV3FF
    · -- left (rec) result is false
      have hLeftEqFalse := eq_of_eo_is_eq_true_consume_local _ _ hV3FT
      rcases (ihRec.1 (Term.Boolean false) hSTy hC1Ty
          hLeftEqFalse.symm rfl hWfParts.1 ssU hSsU).1 v1 hV1 with
        ⟨hNe1, hSuf1⟩
      refine ⟨hNe1, ?_⟩
      intro pre suf hApp
      rw [native_str_in_re_re_inter, hSuf1 pre suf hApp]
      rfl
    · rw [hV3FF] at hIteFalse
      simp only [eo_ite_false] at hIteFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hMT | hMF
      · rw [hMT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hV2T | hV2F
        · -- right (inter-tail) consume is false
          have hRightEqFalse :=
            eq_of_eo_is_eq_true_consume_local _ _ hV2T
          rcases ihInter.1 (Term.Boolean false) hSTy hC2Ty
              hRightEqFalse.symm rfl hWfParts.2 ssU hSsU v2 hV2 with
            ⟨hNe2, hSuf2⟩
          refine ⟨hNe2, ?_⟩
          intro pre suf hApp
          rw [native_str_in_re_re_inter, hSuf2 pre suf hApp]
          simp
        · rw [hV2F] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [hIteFalse]
                intro h
                cases h) with hST | hSF
          · exfalso
            rw [hST] at hIteFalse
            simp only [eo_ite_true] at hIteFalse
            rw [hIteFalse] at hV3FF
            simp [__eo_is_eq, native_teq, native_and, native_not,
              SmtEval.native_and, SmtEval.native_not] at hV3FF
          · exfalso
            rw [hSF] at hIteFalse
            simp only [eo_ite_false] at hIteFalse
            cases hIteFalse
      · rw [hMF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hV2T | hV2F
        · -- right (inter-tail) consume is false
          have hRightEqFalse :=
            eq_of_eo_is_eq_true_consume_local _ _ hV2T
          rcases ihInter.1 (Term.Boolean false) hSTy hC2Ty
              hRightEqFalse.symm rfl hWfParts.2 ssU hSsU v2 hV2 with
            ⟨hNe2, hSuf2⟩
          refine ⟨hNe2, ?_⟩
          intro pre suf hApp
          rw [native_str_in_re_re_inter, hSuf2 pre suf hApp]
          simp
        · exfalso
          rw [hV2F] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          cases hIteFalse
  · -- residual component
    intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
    have hWfParts := StrInReConsumeInternal.consume_wf_inter_tail_parts_local hWf
    have hC1Ty :=
      (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hRTy).1
    have hC2Ty :=
      (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2 hRTy).2
    rw [__str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel]
      at hSide
    have hSideNe : side ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hMemEps
      simp [__str_membership_re] at hMemEps
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hV3FT | hV3FF
    · exfalso
      rw [hV3FT] at hSide
      simp only [eo_ite_true] at hSide
      rw [hSide] at hMemEps
      simp [__str_membership_re] at hMemEps
    · rw [hV3FF] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hMT | hMF
      · rw [hMT] at hSide
        simp only [eo_ite_true] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hV2T | hV2F
        · exfalso
          rw [hV2T] at hSide
          simp only [eo_ite_true] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
        · rw [hV2F] at hSide
          simp only [eo_ite_false] at hSide
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [← hSide]
                exact hSideNe) with hST | hSF
          · -- side is the rec result, equal to the inter-tail result
            rw [hST] at hSide
            simp only [eo_ite_true] at hSide
            have hSameEq :
                __str_re_consume_inter s c2 fuel =
                  __str_re_consume_rec s c1 fuel :=
              eq_of_eo_eq_true _ _ hST
            rcases ihRec.2 side hSTy hC1Ty hSide hMemEps hUnrevNe
                hWfParts.1 with ⟨hMemTyRaw, hMemTy, hRestL⟩
            rcases ihInter.2 side hSTy hC2Ty (hSide.trans
                hSameEq.symm) hMemEps hUnrevNe hWfParts.2 with
              ⟨_, _, hRestR⟩
            refine ⟨hMemTyRaw, hMemTy, ?_⟩
            intro ssU ssR hSsU hSsR rvU hRvU
            rcases StrInReConsumeInternal.re_rev_comp_inter_decomp_local M hM c1 c2 rvU hRTy
                hRvU with ⟨v1, v2, hV1, hV2, hRvUEq⟩
            subst hRvUEq
            rcases (hRestL ssU ssR hSsU hSsR).1 v1 hV1 with
              ⟨⟨u1, hU1dec, hU1mem⟩, hQ1⟩
            rcases hRestR ssU ssR hSsU hSsR v2 hV2 with
              ⟨⟨u2, hU2dec, hU2mem⟩, hQ2⟩
            have hU12 : u1 = u2 :=
              List.append_cancel_left (hU1dec.symm.trans hU2dec)
            subst hU12
            constructor
            · refine ⟨u1, hU1dec, ?_⟩
              rw [native_str_in_re_re_inter, hU1mem, hU2mem]
              rfl
            · intro q qv hQv
              exact StrInReConsumeInternal.native_str_in_re_concat_inter_both_eq_local
                (native_unpack_string ssU) (native_unpack_string ssR)
                u1 qv v1 v2 hU1dec hU1mem hU2mem (hQ1 q qv hQv)
          · exfalso
            rw [hSF] at hSide
            simp only [eo_ite_false] at hSide
            rw [hSide] at hMemEps
            simp [__str_membership_re] at hMemEps
      · rw [hMF] at hSide
        simp only [eo_ite_false] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hV2T | hV2F
        · exfalso
          rw [hV2T] at hSide
          simp only [eo_ite_true] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
        · exfalso
          rw [hV2F] at hSide
          simp only [eo_ite_false] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps

theorem StrInReConsumeInternal.consume_wf_chain_stuck_local :
    StrInReConsumeInternal.consume_wf_chain_local Term.Stuck := by
  simp [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_local]

theorem StrInReConsumeInternal.consume_wf_chain_eps_local :
    StrInReConsumeInternal.consume_wf_chain_local
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  simp [StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_local]

def StrInReConsumeInternal.consume_wf_rev_map_motive_local (t acc : Term) : Prop :=
  StrInReConsumeInternal.consume_wf_chain_local t ->
  StrInReConsumeInternal.consume_wf_chain_local acc ->
  StrInReConsumeInternal.consume_wf_chain_local (__re_rev_map_rev t acc)

def StrInReConsumeInternal.consume_wf_rev_comp_motive_local (c : Term) : Prop :=
  (StrInReConsumeInternal.consume_wf_chunk_local c ->
    StrInReConsumeInternal.consume_wf_chunk_local (__re_rev_comp c)) ∧
  (StrInReConsumeInternal.consume_wf_inter_tail_local c ->
    StrInReConsumeInternal.consume_wf_inter_tail_local (__re_rev_comp c)) ∧
  (StrInReConsumeInternal.consume_wf_union_tail_local c ->
    StrInReConsumeInternal.consume_wf_union_tail_local (__re_rev_comp c))

/-- `__eo_mk_apply` only inspects whether its arguments are `Term.Stuck`, so a
proof about `__eo_mk_apply op x` needs two cases, not one per `Term`
constructor. -/
private theorem StrInReConsumeInternal.mk_apply_unop_cases_local
    {op x : Term} {P : Term -> Prop} (hop : op ≠ Term.Stuck)
    (hStuck : P Term.Stuck) (hApply : P (Term.Apply op x)) :
    P (__eo_mk_apply op x) := by
  by_cases hx : x = Term.Stuck
  · subst hx
    rw [show __eo_mk_apply op Term.Stuck = Term.Stuck by cases op <;> rfl]
    exact hStuck
  · rw [show __eo_mk_apply op x = Term.Apply op x by
      cases op <;> cases x <;> simp_all [__eo_mk_apply]]
    exact hApply

/-- The binary counterpart: three cases instead of 25 x 25. -/
private theorem StrInReConsumeInternal.mk_apply_binop_cases_local
    {op x y : Term} {P : Term -> Prop} (hop : op ≠ Term.Stuck)
    (hStuck : P Term.Stuck)
    (hApply : P (Term.Apply (Term.Apply op x) y)) :
    P (__eo_mk_apply (__eo_mk_apply op x) y) := by
  by_cases hx : x = Term.Stuck
  · subst hx
    rw [show __eo_mk_apply op Term.Stuck = Term.Stuck by cases op <;> rfl]
    exact hStuck
  · rw [show __eo_mk_apply op x = Term.Apply op x by
      cases op <;> cases x <;> simp_all [__eo_mk_apply]]
    exact StrInReConsumeInternal.mk_apply_unop_cases_local (by simp) hStuck hApply

/--
Well-formedness is preserved by `__re_rev_map_rev` / `__re_rev_comp`:
the reversal only reorders chunks and recurses into combinator
components, never creating raw `re_concat` chunks from well-formed
inputs.
-/
theorem StrInReConsumeInternal.consume_wf_rev_facts_local :
    (∀ t acc, StrInReConsumeInternal.consume_wf_rev_map_motive_local t acc) ∧
      (∀ c, StrInReConsumeInternal.consume_wf_rev_comp_motive_local c) := by
  have case1 : ∀ t, StrInReConsumeInternal.consume_wf_rev_map_motive_local t Term.Stuck := by
    intro t _ _
    rw [__re_rev_map_rev.eq_1]
    exact StrInReConsumeInternal.consume_wf_chain_stuck_local
  have case2 : ∀ acc, (acc = Term.Stuck -> False) ->
      StrInReConsumeInternal.consume_wf_rev_map_motive_local
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) acc := by
    intro acc hAccNe _ hAcc
    rw [__re_rev_map_rev.eq_2 acc hAccNe]
    exact hAcc
  have case3 : ∀ a b acc, (acc = Term.Stuck -> False) ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local a ->
      StrInReConsumeInternal.consume_wf_rev_map_motive_local b
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_concat) (__re_rev_comp a))
          acc) ->
      StrInReConsumeInternal.consume_wf_rev_map_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)
        acc := by
    intro a b acc hAccNe ihComp ihTail hChain hAcc
    have hParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hChain
    rw [__re_rev_map_rev.eq_3 acc a b hAccNe]
    by_cases hCompNe : __re_rev_comp a = Term.Stuck
    · have hAccStuck :
          __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_concat)
                (__re_rev_comp a)) acc = Term.Stuck := by
        rw [hCompNe]
        rfl
      rw [hAccStuck]
      rw [__re_rev_map_rev.eq_1]
      exact StrInReConsumeInternal.consume_wf_chain_stuck_local
    · have hAccNe' : acc ≠ Term.Stuck := fun h => hAccNe h
      have hShape := StrInReConsumeInternal.eo_mk_apply_binop_shape_consume_local
        (Term.UOp UserOp.re_concat) (__re_rev_comp a) acc (by
          intro h
          cases h) hCompNe hAccNe'
      rw [hShape] at ihTail ⊢
      exact ihTail hParts.2
        (StrInReConsumeInternal.consume_wf_chain_of_parts_local (ihComp.1 hParts.1) hAcc)
  have case4 : ∀ t x, (x = Term.Stuck -> False) ->
      (t = Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
        False) ->
      (∀ a b,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False) ->
      StrInReConsumeInternal.consume_wf_rev_map_motive_local t x := by
    intro t x _hXNe hNotEps hNotConcat _ _
    rw [StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local t x hNotEps
      hNotConcat]
    exact StrInReConsumeInternal.consume_wf_chain_stuck_local
  have case5 : StrInReConsumeInternal.consume_wf_rev_comp_motive_local Term.Stuck := by
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      simp [__re_rev_comp, StrInReConsumeInternal.consume_wf_chunk_local,
        StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_union_tail_local,
        StrInReConsumeInternal.consume_wf_local]
  have case6 :
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local (Term.UOp UserOp.re_all) :=
    ⟨fun h => h, fun h => h, fun h => h⟩
  have case7 :
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local (Term.UOp UserOp.re_none) :=
    ⟨fun h => h, fun h => h, fun h => h⟩
  have case8 : ∀ body,
      StrInReConsumeInternal.consume_wf_rev_map_motive_local body
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local
        (Term.Apply (Term.UOp UserOp.re_mult) body) := by
    intro body ihBody
    refine ⟨fun hChunk => ?_, fun _ => ?_, fun _ => ?_⟩
    · have hRev := ihBody (StrInReConsumeInternal.consume_wf_chain_mult_body_local hChunk)
        StrInReConsumeInternal.consume_wf_chain_eps_local
      show StrInReConsumeInternal.consume_wf_chunk_local
        (__eo_mk_apply (Term.UOp UserOp.re_mult)
          (__re_rev_map_rev body
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
      exact StrInReConsumeInternal.mk_apply_unop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local])
        (by simp only [StrInReConsumeInternal.consume_wf_local]; exact hRev)
    · show StrInReConsumeInternal.consume_wf_inter_tail_local
        (__eo_mk_apply (Term.UOp UserOp.re_mult)
          (__re_rev_map_rev body
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
      exact StrInReConsumeInternal.mk_apply_unop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local])
    · show StrInReConsumeInternal.consume_wf_union_tail_local
        (__eo_mk_apply (Term.UOp UserOp.re_mult)
          (__re_rev_map_rev body
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
      exact StrInReConsumeInternal.mk_apply_unop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local])
  have case9 : ∀ c1 c2,
      StrInReConsumeInternal.consume_wf_rev_map_motive_local c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local c2 ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2) := by
    intro c1 c2 ihC1 ihC2
    have hBoth : ∀ (hC1 : StrInReConsumeInternal.consume_wf_chain_local c1)
        (hC2 : StrInReConsumeInternal.consume_wf_inter_tail_local c2),
        StrInReConsumeInternal.consume_wf_chain_local
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) ∧
          StrInReConsumeInternal.consume_wf_inter_tail_local (__re_rev_comp c2) :=
      fun hC1 hC2 =>
        ⟨ihC1 hC1 StrInReConsumeInternal.consume_wf_chain_eps_local, ihC2.2.1 hC2⟩
    refine ⟨fun hChunk => ?_, fun hTail => ?_, fun _ => ?_⟩
    · rcases hBoth (StrInReConsumeInternal.consume_wf_chunk_inter_parts_local hChunk).1
          (StrInReConsumeInternal.consume_wf_chunk_inter_parts_local hChunk).2 with
        ⟨hLeft, hRight⟩
      show StrInReConsumeInternal.consume_wf_chunk_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local])
        (by simp only [StrInReConsumeInternal.consume_wf_local]; exact ⟨hLeft, hRight⟩)
    · rcases hBoth (StrInReConsumeInternal.consume_wf_inter_tail_parts_local hTail).1
          (StrInReConsumeInternal.consume_wf_inter_tail_parts_local hTail).2 with
        ⟨hLeft, hRight⟩
      show StrInReConsumeInternal.consume_wf_inter_tail_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp only [StrInReConsumeInternal.consume_wf_local]; exact ⟨hLeft, hRight⟩)
    · show StrInReConsumeInternal.consume_wf_union_tail_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local])
  have case10 : ∀ c1 c2,
      StrInReConsumeInternal.consume_wf_rev_map_motive_local c1
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local c2 ->
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2) := by
    intro c1 c2 ihC1 ihC2
    have hBoth : ∀ (hC1 : StrInReConsumeInternal.consume_wf_chain_local c1)
        (hC2 : StrInReConsumeInternal.consume_wf_union_tail_local c2),
        StrInReConsumeInternal.consume_wf_chain_local
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))) ∧
          StrInReConsumeInternal.consume_wf_union_tail_local (__re_rev_comp c2) :=
      fun hC1 hC2 =>
        ⟨ihC1 hC1 StrInReConsumeInternal.consume_wf_chain_eps_local, ihC2.2.2 hC2⟩
    refine ⟨fun hChunk => ?_, fun _ => ?_, fun hTail => ?_⟩
    · rcases hBoth (StrInReConsumeInternal.consume_wf_chunk_union_parts_local hChunk).1
          (StrInReConsumeInternal.consume_wf_chunk_union_parts_local hChunk).2 with
        ⟨hLeft, hRight⟩
      show StrInReConsumeInternal.consume_wf_chunk_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local])
        (by simp only [StrInReConsumeInternal.consume_wf_local]; exact ⟨hLeft, hRight⟩)
    · show StrInReConsumeInternal.consume_wf_inter_tail_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp [StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_local])
    · rcases hBoth (StrInReConsumeInternal.consume_wf_union_tail_parts_local hTail).1
          (StrInReConsumeInternal.consume_wf_union_tail_parts_local hTail).2 with
        ⟨hLeft, hRight⟩
      show StrInReConsumeInternal.consume_wf_union_tail_local
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev c1
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))
          (__re_rev_comp c2))
      exact StrInReConsumeInternal.mk_apply_binop_cases_local (by simp)
        (by simp [StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local])
        (by simp only [StrInReConsumeInternal.consume_wf_local]; exact ⟨hLeft, hRight⟩)
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
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local c := by
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
    rw [StrInReConsumeInternal.consume_wf_rev_comp_motive_local, hEq]
    exact ⟨fun h => h, fun h => h, fun h => h⟩
  constructor
  · intro t acc
    exact __re_rev_map_rev.induct
      StrInReConsumeInternal.consume_wf_rev_map_motive_local
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 t acc
  · intro c
    exact __re_rev_comp.induct
      StrInReConsumeInternal.consume_wf_rev_map_motive_local
      StrInReConsumeInternal.consume_wf_rev_comp_motive_local
      case1 case2 case3 case4 case5 case6 case7 case8 case9 case10
      case11 c

/--
Well-formedness of the split of a flat string chunk list.
-/
theorem StrInReConsumeInternal.consume_wf_chain_split_str_to_re_local :
    ∀ parts tail,
      StrInReConsumeInternal.consume_wf_chain_local tail ->
      StrInReConsumeInternal.consume_wf_chain_local (__re_split_str_to_re parts tail) := by
  intro parts tail
  induction parts, tail using __re_split_str_to_re.induct with
  | case1 x =>
      intro _
      exact StrInReConsumeInternal.consume_wf_chain_stuck_local
  | case2 t ht =>
      intro _
      have hEq : __re_split_str_to_re t Term.Stuck = Term.Stuck := by
        cases t <;> rfl
      rw [hEq]
      exact StrInReConsumeInternal.consume_wf_chain_stuck_local
  | case3 c s tail hTailNe ih =>
      intro hTail
      have hStep :
          __re_split_str_to_re
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
                s) tail =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) c))
              (__re_split_str_to_re s tail) := by
        cases tail
        case Stuck => exact absurd rfl hTailNe
        all_goals rfl
      rw [hStep]
      have hRec := ih hTail
      cases hX : __re_split_str_to_re s tail <;>
        rw [hX] at hRec <;>
        simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chain_local,
          StrInReConsumeInternal.consume_wf_local]
  | case4 c tail hCNe hTailNe hNotCons =>
      intro hTail
      have hEq : __re_split_str_to_re c tail = tail := by
        cases tail <;>
          try exact absurd rfl hTailNe
        all_goals cases c
        all_goals try exact absurd rfl hCNe
        all_goals try rfl
        all_goals (rename_i f x; cases f)
        all_goals try rfl
        all_goals (rename_i g y; cases g)
        all_goals try rfl
        all_goals (rename_i op; cases op)
        all_goals try rfl
        all_goals exact ((hNotCons _ _ rfl).elim)
      rw [hEq]
      exact hTail

/--
Well-formedness of `__eo_list_concat_rec` on `re_concat` lists.
-/
theorem StrInReConsumeInternal.consume_wf_chain_list_concat_rec_local :
    ∀ x z,
      __eo_is_list (Term.UOp UserOp.re_concat) x = Term.Boolean true ->
      StrInReConsumeInternal.consume_wf_chain_local x ->
      StrInReConsumeInternal.consume_wf_chain_local z ->
      StrInReConsumeInternal.consume_wf_chain_local (__eo_list_concat_rec x z) := by
  intro x z
  induction x, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hList _ _
      simp [__eo_is_list] at hList
  | case2 t ht =>
      intro _ _ _
      have hEq : __eo_list_concat_rec t Term.Stuck = Term.Stuck := by
        cases t <;> rfl
      rw [hEq]
      exact StrInReConsumeInternal.consume_wf_chain_stuck_local
  | case3 f hd tl z hz ih =>
      intro hList hChain hZ
      have hf := eo_is_list_cons_head_eq_of_true
        (Term.UOp UserOp.re_concat) f hd tl hList
      subst hf
      have hTailList := eo_is_list_tail_true_of_cons_self
        (Term.UOp UserOp.re_concat) hd tl hList
      have hParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hChain
      have hStep :
          __eo_list_concat_rec
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) hd) tl) z =
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.re_concat) hd)
              (__eo_list_concat_rec tl z) := by
        cases z
        case Stuck => exact absurd rfl hz
        all_goals rfl
      rw [hStep]
      have hRec := ih hTailList hParts.2 hZ
      have hChunkHd := hParts.1
      cases hX : __eo_list_concat_rec tl z <;>
        rw [hX] at hRec <;>
        simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chain_local,
          StrInReConsumeInternal.consume_wf_local]
  | case4 nil z hns hzs hncons =>
      intro _ _ hZ
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq]
      exact hZ

/--
Well-formedness of `__re_flatten` outputs: list mode yields a
well-formed chain, component mode yields a well-formed chunk (on
non-`re_concat` inputs) whose inter/union tail views are also
well-formed.
-/
theorem StrInReConsumeInternal.consume_wf_flatten_facts_local :
    ∀ mode r,
      (mode = Term.Boolean true ->
        StrInReConsumeInternal.consume_wf_chain_local (__re_flatten mode r)) ∧
      (mode = Term.Boolean false ->
        ((∀ a b,
            r = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a)
              b -> False) ->
          StrInReConsumeInternal.consume_wf_chunk_local (__re_flatten mode r)) ∧
        StrInReConsumeInternal.consume_wf_inter_tail_local (__re_flatten mode r) ∧
        StrInReConsumeInternal.consume_wf_union_tail_local (__re_flatten mode r)) := by
  intro mode r
  induction mode, r using __re_flatten.induct with
  | case1 x =>
      have hRed : __re_flatten x Term.Stuck = Term.Stuck := by
        simp [__re_flatten]
      rw [hRed]
      constructor
      · intro _
        exact StrInReConsumeInternal.consume_wf_chain_stuck_local
      · intro _
        refine ⟨fun _ => ?_, ?_, ?_⟩ <;>
          simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_inter_tail_local,
            StrInReConsumeInternal.consume_wf_union_tail_local, StrInReConsumeInternal.consume_wf_local]
  | case2 =>
      constructor
      · intro _
        have hRed : __re_flatten (Term.Boolean true)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
            Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
          simp [__re_flatten]
        rw [hRed]
        exact StrInReConsumeInternal.consume_wf_chain_eps_local
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
        exact StrInReConsumeInternal.consume_wf_chain_split_str_to_re_local _ _ (ih.1 rfl)
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
        by_cases hXL : __eo_is_list (Term.UOp UserOp.re_concat)
            (__re_flatten (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a1)
                a2)) = Term.Boolean true
        · by_cases hZL : __eo_is_list (Term.UOp UserOp.re_concat)
              (__re_flatten (Term.Boolean true) b) = Term.Boolean true
          · have hRed2 : __eo_list_concat (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean true)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
                (__re_flatten (Term.Boolean true) b) =
                __eo_list_concat_rec
                  (__re_flatten (Term.Boolean true)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
                  (__re_flatten (Term.Boolean true) b) := by
              show __eo_requires _ _ _ = _
              rw [hXL, hZL]
              simp [__eo_requires, native_teq, SmtEval.native_ite,
                SmtEval.native_not]
            rw [hRed2]
            exact StrInReConsumeInternal.consume_wf_chain_list_concat_rec_local _ _ hXL
              (ih1.1 rfl) (ih2.1 rfl)
          · have hRed2 : __eo_list_concat (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean true)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
                (__re_flatten (Term.Boolean true) b) = Term.Stuck := by
              show __eo_requires _ _ _ = _
              rw [hXL]
              simp [__eo_requires, native_teq, SmtEval.native_ite,
                SmtEval.native_not, hZL]
            rw [hRed2]
            exact StrInReConsumeInternal.consume_wf_chain_stuck_local
        · have hRed2 : __eo_list_concat (Term.UOp UserOp.re_concat)
              (__re_flatten (Term.Boolean true)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) a1) a2))
              (__re_flatten (Term.Boolean true) b) = Term.Stuck := by
            show __eo_requires _ _ _ = _
            simp [__eo_requires, native_teq, SmtEval.native_ite,
              hXL]
          rw [hRed2]
          exact StrInReConsumeInternal.consume_wf_chain_stuck_local
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
        have hChunk := (ihA.2 rfl).1 (fun x y h => hNotNested x y h)
        have hChain := ihB.1 rfl
        cases hX : __re_flatten (Term.Boolean false) a <;>
          rw [hX] at hChunk <;>
          cases hY : __re_flatten (Term.Boolean true) b <;>
          rw [hY] at hChain <;>
          simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chain_local,
            StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
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
        exact StrInReConsumeInternal.consume_wf_chain_split_str_to_re_local _ _
          StrInReConsumeInternal.consume_wf_chain_eps_local
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
        have hChunk := (ih.2 rfl).1 (fun a b h => hConcat a b h)
        cases hX : __re_flatten (Term.Boolean false) c <;>
          rw [hX] at hChunk <;>
          simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chain_local,
            StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
      · intro hMode
        simp at hMode
  | case8 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        refine ⟨fun _ => ?_, ?_, ?_⟩ <;>
          simp [__re_flatten, StrInReConsumeInternal.consume_wf_chunk_local,
            StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_union_tail_local,
            StrInReConsumeInternal.consume_wf_local]
  | case9 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        refine ⟨fun _ => ?_, ?_, ?_⟩ <;>
          simp [__re_flatten, StrInReConsumeInternal.consume_wf_chunk_local,
            StrInReConsumeInternal.consume_wf_inter_tail_local, StrInReConsumeInternal.consume_wf_union_tail_local,
            StrInReConsumeInternal.consume_wf_local]
  | case10 body ih =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hChain := ih.1 rfl
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.UOp UserOp.re_mult) body) =
            __eo_mk_apply (Term.UOp UserOp.re_mult)
              (__re_flatten (Term.Boolean true) body) := by
          simp [__re_flatten]
        rw [hRed]
        refine ⟨fun _ => ?_, ?_, ?_⟩
        · cases hX : __re_flatten (Term.Boolean true) body <;>
            rw [hX] at hChain <;>
            simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chunk_local,
              StrInReConsumeInternal.consume_wf_chain_local, StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) body <;>
            simp [__eo_mk_apply, StrInReConsumeInternal.consume_wf_inter_tail_local,
              StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) body <;>
            simp [__eo_mk_apply, StrInReConsumeInternal.consume_wf_union_tail_local,
              StrInReConsumeInternal.consume_wf_local]
  | case11 c1 c2 ih1 ih2 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hChain := ih1.1 rfl
        have hTail := (ih2.2 rfl).2.1
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1)
              c2) =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_inter)
                (__re_flatten (Term.Boolean true) c1))
              (__re_flatten (Term.Boolean false) c2) := by
          simp [__re_flatten]
        rw [hRed]
        refine ⟨fun _ => ?_, ?_, ?_⟩
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            rw [hX] at hChain <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            rw [hY] at hTail <;>
            simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chunk_local,
              StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            rw [hX] at hChain <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            rw [hY] at hTail <;>
            simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_inter_tail_local,
              StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            simp [__eo_mk_apply, StrInReConsumeInternal.consume_wf_union_tail_local,
              StrInReConsumeInternal.consume_wf_local]
  | case12 c1 c2 ih1 ih2 =>
      constructor
      · intro hMode
        simp at hMode
      · intro _
        have hChain := ih1.1 rfl
        have hTail := (ih2.2 rfl).2.2
        have hRed : __re_flatten (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1)
              c2) =
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.re_union)
                (__re_flatten (Term.Boolean true) c1))
              (__re_flatten (Term.Boolean false) c2) := by
          simp [__re_flatten]
        rw [hRed]
        refine ⟨fun _ => ?_, ?_, ?_⟩
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            rw [hX] at hChain <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            rw [hY] at hTail <;>
            simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_chunk_local,
              StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            simp [__eo_mk_apply, StrInReConsumeInternal.consume_wf_inter_tail_local,
              StrInReConsumeInternal.consume_wf_local]
        · cases hX : __re_flatten (Term.Boolean true) c1 <;>
            rw [hX] at hChain <;>
            cases hY : __re_flatten (Term.Boolean false) c2 <;>
            rw [hY] at hTail <;>
            simp_all [__eo_mk_apply, StrInReConsumeInternal.consume_wf_union_tail_local,
              StrInReConsumeInternal.consume_wf_local]
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
        refine ⟨fun hNotConcat => ?_, ?_, ?_⟩
        · cases c
          case Apply f x =>
            cases f
            case UOp op =>
              cases op <;>
                first
                  | exact ((hMult _ rfl).elim)
                  | simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hNotConcat _ _ rfl).elim)
                    | exact ((hInter _ _ rfl).elim)
                    | exact ((hUnion _ _ rfl).elim)
                    | simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
              all_goals simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
            all_goals simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
          all_goals simp [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local]
        · cases c
          case Apply f x =>
            cases f
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hInter _ _ rfl).elim)
                    | simp [StrInReConsumeInternal.consume_wf_inter_tail_local,
                        StrInReConsumeInternal.consume_wf_local]
              all_goals simp [StrInReConsumeInternal.consume_wf_inter_tail_local,
                StrInReConsumeInternal.consume_wf_local]
            all_goals simp [StrInReConsumeInternal.consume_wf_inter_tail_local,
              StrInReConsumeInternal.consume_wf_local]
          all_goals simp [StrInReConsumeInternal.consume_wf_inter_tail_local,
            StrInReConsumeInternal.consume_wf_local]
        · cases c
          case Apply f x =>
            cases f
            case Apply g y =>
              cases g
              case UOp op2 =>
                cases op2 <;>
                  first
                    | exact ((hUnion _ _ rfl).elim)
                    | simp [StrInReConsumeInternal.consume_wf_union_tail_local,
                        StrInReConsumeInternal.consume_wf_local]
              all_goals simp [StrInReConsumeInternal.consume_wf_union_tail_local,
                StrInReConsumeInternal.consume_wf_local]
            all_goals simp [StrInReConsumeInternal.consume_wf_union_tail_local,
              StrInReConsumeInternal.consume_wf_local]
          all_goals simp [StrInReConsumeInternal.consume_wf_union_tail_local,
            StrInReConsumeInternal.consume_wf_local]
  | case14 x x_1 hTreeNe hEmpty hConcatStr hNested hConcat hStr hTrue
      hAll hNone hMult hInter hUnion hFalse =>
      constructor
      · intro hMode
        exact absurd hMode (fun h => hTrue h)
      · intro hMode
        exact absurd hMode (fun h => hFalse h)

/--
Well-formedness of the residual chain of the algorithm's second pass:
`__re_rev_map_rev (__re_flatten true r) eps` is a well-formed chain
for EVERY `r`.
-/
theorem StrInReConsumeInternal.consume_wf_chain_rev_flatten_local
    (r : Term) :
    StrInReConsumeInternal.consume_wf_chain_local
      (__re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) :=
  StrInReConsumeInternal.consume_wf_rev_facts_local.1 _ _
    ((StrInReConsumeInternal.consume_wf_flatten_facts_local (Term.Boolean true) r).1 rfl)
    StrInReConsumeInternal.consume_wf_chain_eps_local

theorem StrInReConsumeInternal.native_re_concat_right_empty_consume_local
    (X : SmtRegLan) :
    native_re_concat X (native_str_to_re []) = X := by
  cases X <;> rfl

/--
Right-decomposition of star membership keeping BOTH memberships: a
nonempty member of `(r)*` splits as a star member followed by a
nonempty `r`-chunk.
-/
theorem StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local
    (w : native_String) (r : SmtRegLan)
    (hMem : native_str_in_re w (native_re_mult r) = true)
    (hNe : w ≠ []) :
    ∃ pre suf : native_String,
      pre ++ suf = w ∧ suf ≠ [] ∧
      native_str_in_re pre (native_re_mult r) = true ∧
      native_str_in_re suf r = true := by
  have hValid : native_string_valid w = true := by
    cases h : native_string_valid w with
    | true => rfl
    | false => simp [native_str_in_re, h] at hMem
  have hRevValid : native_string_valid w.reverse = true := by
    simpa [StrInReConsumeInternal.native_string_valid_reverse_consume_local w] using hValid
  have hRevMem :
      native_str_in_re w.reverse
          (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
        true := by
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local w (native_re_mult r)
    rw [hEq] at hMem
    have hStarEq :
        StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_re_mult r) =
          native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
      have hsimpa :=
        StrInReConsumeInternal.native_re_reverse_raw_mk_star_consume_local r
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa
    rw [hStarEq] at hMem
    exact hMem
  have hRevListMem :
      nativeListInRe w.reverse
          (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
        true := by
    simpa [native_str_in_re, nativeListInRe, hRevValid] using hRevMem
  have hRevNe : w.reverse ≠ [] := by
    intro hBad
    apply hNe
    simpa using congrArg List.reverse hBad
  rcases nativeListInRe_re_mult_nonempty_prefix_decomp_local w.reverse
      (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) hRevListMem hRevNe with
    ⟨pre', suf', hAppend, hPreNe, hPreMem, hSufMem⟩
  have hPreValid : native_string_valid pre' = true :=
    native_string_valid_append_left pre' suf' (by
      rw [hAppend]
      exact hRevValid)
  have hSufValid : native_string_valid suf' = true :=
    StrInReConsumeInternal.native_string_valid_suffix_consume_local pre' suf' (by
      rw [hAppend]
      exact hRevValid)
  refine ⟨suf'.reverse, pre'.reverse, ?_, ?_, ?_, ?_⟩
  · have h := congrArg List.reverse hAppend
    simpa using h
  · intro hBad
    apply hPreNe
    simpa using congrArg List.reverse hBad
  · have hSufStrMem :
        native_str_in_re suf'
            (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r)) =
          true := by
      simpa [native_str_in_re, hSufValid] using hSufMem
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local suf'.reverse
        (native_re_mult r)
    rw [show suf'.reverse.reverse = suf' by simp] at hEq
    have hStarEq :
        StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_re_mult r) =
          native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) := by
      have hsimpa :=
        StrInReConsumeInternal.native_re_reverse_raw_mk_star_consume_local r
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa
    rw [hStarEq] at hEq
    rw [← hEq]
    exact hSufStrMem
  · have hPreStrMem :
        native_str_in_re pre'
            (StrInReConsumeInternal.native_re_reverse_raw_consume_local r) =
          true := by
      simpa [native_str_in_re, hPreValid] using hPreMem
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_reverse_re_consume_local pre'.reverse r
    rw [show pre'.reverse.reverse = pre' by simp] at hEq
    rw [← hEq]
    exact hPreStrMem

/--
Right-append closure of star membership.
-/
theorem StrInReConsumeInternal.native_str_in_re_star_append_local
    (bs u : native_String) (B : SmtRegLan)
    (hBs : native_str_in_re bs (native_re_mult B) = true)
    (hU : native_str_in_re u B = true) :
    native_str_in_re (bs ++ u) (native_re_mult B) = true := by
  have hBsValid : native_string_valid bs = true := by
    cases h : native_string_valid bs with
    | true => rfl
    | false => simp [native_str_in_re, h] at hBs
  have hUValid : native_string_valid u = true := by
    cases h : native_string_valid u with
    | true => rfl
    | false => simp [native_str_in_re, h] at hU
  -- go to the reversed world, use left-cons absorption, come back
  have hStarEq :
      StrInReConsumeInternal.native_re_reverse_raw_consume_local (native_re_mult B) =
        native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local B) := by
    have hsimpa :=
      StrInReConsumeInternal.native_re_reverse_raw_mk_star_consume_local B
    try simp [native_re_mult] at hsimpa ⊢
    exact hsimpa
  have hBsRev :
      native_str_in_re bs.reverse
          (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local B)) =
        true := by
    have hEq :=
      StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local bs (native_re_mult B)
    rw [hEq, hStarEq] at hBs
    exact hBs
  have hURev :
      native_str_in_re u.reverse
          (StrInReConsumeInternal.native_re_reverse_raw_consume_local B) = true := by
    have hEq := StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local u B
    rw [hEq] at hU
    exact hU
  have hBsRev' :
      native_str_in_re bs.reverse
          (native_re_concat
            (native_re_mult (StrInReConsumeInternal.native_re_reverse_raw_consume_local B))
            (native_str_to_re [])) = true := by
    rw [StrInReConsumeInternal.native_re_concat_right_empty_consume_local]
    exact hBsRev
  have hConsMem := native_str_in_re_re_concat_intro u.reverse
    bs.reverse _ _ hURev hBsRev'
  have hAbsorb :=
    native_str_in_re_re_mult_concat_cons_local
      (u.reverse ++ bs.reverse)
      (StrInReConsumeInternal.native_re_reverse_raw_consume_local B)
      (native_str_to_re []) hConsMem
  rw [StrInReConsumeInternal.native_re_concat_right_empty_consume_local] at hAbsorb
  -- transfer back
  have hEq :=
    StrInReConsumeInternal.native_str_in_re_eq_reverse_re_consume_local (bs ++ u)
      (native_re_mult B)
  rw [hEq, hStarEq]
  rw [show (bs ++ u).reverse = u.reverse ++ bs.reverse by simp]
  exact hAbsorb

/--
Right-append absorption for `A · B*`.
-/
theorem StrInReConsumeInternal.native_str_in_re_concat_star_absorb_local
    (x u : native_String) (A B : SmtRegLan)
    (hX :
      native_str_in_re x (native_re_concat A (native_re_mult B)) =
        true)
    (hU : native_str_in_re u B = true) :
    native_str_in_re (x ++ u)
        (native_re_concat A (native_re_mult B)) = true := by
  have hXValid : native_string_valid x = true := by
    cases h : native_string_valid x with
    | true => rfl
    | false => simp [native_str_in_re, h] at hX
  have hListMem :
      nativeListInRe x
          (native_re_mk_concat A (native_re_mult B)) = true := by
    simpa [native_str_in_re, nativeListInRe, hXValid] using hX
  rcases (nativeListInRe_mk_concat_true_iff_exists_append x A
      _).1 hListMem with ⟨a, bs, hSplit, hA, hBs⟩
  have hAValid : native_string_valid a = true :=
    StrInReConsumeInternal.native_string_valid_prefix_consume_local a bs (by
      rw [hSplit]
      exact hXValid)
  have hBsValid : native_string_valid bs = true :=
    StrInReConsumeInternal.native_string_valid_suffix_consume_local a bs (by
      rw [hSplit]
      exact hXValid)
  have hAStr : native_str_in_re a A = true := by
    simpa [native_str_in_re, hAValid] using hA
  have hBsStr : native_str_in_re bs (native_re_mult B) = true := by
    simpa [native_str_in_re, hBsValid] using hBs
  have hApp :
      native_str_in_re (bs ++ u) (native_re_mult B) = true :=
    StrInReConsumeInternal.native_str_in_re_star_append_local bs u B hBsStr hU
  rw [show x ++ u = a ++ (bs ++ u) from by
    rw [← hSplit, List.append_assoc]]
  exact native_str_in_re_re_concat_intro a (bs ++ u) A _ hAStr hApp

/--
∀q composition for the mult case's left-false branch: the tail-only
residual equality lifts to `A · B*` when no suffix of `w` is in `B`.
-/
theorem StrInReConsumeInternal.consume_mult_left_false_residual_eq_local
    (w w3 : native_String) (qv A B : SmtRegLan)
    (hNoSufB :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf B = false)
    (hEq :
      native_str_in_re w (native_re_concat qv A) =
        native_str_in_re w3 qv) :
    native_str_in_re w
        (native_re_concat qv (native_re_concat A (native_re_mult B))) =
      native_str_in_re w3 qv := by
  cases hWV : native_string_valid w with
  | false =>
      have hLhs :
          native_str_in_re w
              (native_re_concat qv
                (native_re_concat A (native_re_mult B))) = false := by
        simp [native_str_in_re, hWV]
      have hLhs2 :
          native_str_in_re w (native_re_concat qv A) = false := by
        simp [native_str_in_re, hWV]
      rw [hLhs, ← hEq, hLhs2]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat qv
                  (native_re_concat A (native_re_mult B))) = true := by
          simpa [native_str_in_re, nativeListInRe, hWV] using hMem
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            _).1 hListMem with ⟨α, δ, hSplit, hAl, hDe⟩
        have hAlValid : native_string_valid α = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local α δ (by
            rw [hSplit]
            exact hWV)
        have hDeValid : native_string_valid δ = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local α δ (by
            rw [hSplit]
            exact hWV)
        have hDeStr :
            native_str_in_re δ
                (native_re_concat A (native_re_mult B)) = true := by
          simpa [native_str_in_re, hDeValid] using hDe
        have hDeList :
            nativeListInRe δ
                (native_re_mk_concat A (native_re_mult B)) = true := by
          simpa [native_str_in_re, nativeListInRe, hDeValid] using
            hDeStr
        rcases (nativeListInRe_mk_concat_true_iff_exists_append δ A
            _).1 hDeList with ⟨x, y, hSplit2, hXm, hYm⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit2]
            exact hDeValid)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit2]
            exact hDeValid)
        have hYStr :
            native_str_in_re y (native_re_mult B) = true := by
          simpa [native_str_in_re, hYValid] using hYm
        by_cases hYNil : y = []
        · subst hYNil
          have hAlStr : native_str_in_re α qv = true := by
            simpa [native_str_in_re, hAlValid] using hAl
          have hXStr : native_str_in_re x A = true := by
            simpa [native_str_in_re, hXValid] using hXm
          have hW1 :
              native_str_in_re w (native_re_concat qv A) = true := by
            rw [show w = α ++ x from by
              rw [← hSplit, ← hSplit2]
              simp]
            exact native_str_in_re_re_concat_intro α x qv A hAlStr
              hXStr
          rw [hEq] at hW1
          rw [hW1]
        · rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local y B
              hYStr hYNil with ⟨y1, yk, hYSplit, _hYkNe, _hY1Mem,
                hYkMem⟩
          exfalso
          have hYkSuf := hNoSufB (α ++ (x ++ y1)) yk (by
            rw [List.append_assoc, List.append_assoc, hYSplit,
              hSplit2, hSplit])
          rw [hYkSuf] at hYkMem
          cases hYkMem
      · intro hMem
        have hW1 :
            native_str_in_re w (native_re_concat qv A) = true := by
          rw [hEq]
          exact hMem
        have hListMem :
            nativeListInRe w (native_re_mk_concat qv A) = true := by
          have hsimpa := hW1
          try simp [native_str_in_re, native_re_concat, hWV] at hsimpa ⊢
          exact hsimpa
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w qv
            A).1 hListMem with ⟨α, x, hSplit, hAl, hXm⟩
        have hAlValid : native_string_valid α = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local α x (by
            rw [hSplit]
            exact hWV)
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local α x (by
            rw [hSplit]
            exact hWV)
        have hAlStr : native_str_in_re α qv = true := by
          simpa [native_str_in_re, hAlValid] using hAl
        have hXStr : native_str_in_re x A = true := by
          simpa [native_str_in_re, hXValid] using hXm
        have hXExt :
            native_str_in_re x
                (native_re_concat A (native_re_mult B)) = true := by
          have h := native_str_in_re_re_concat_intro x [] A
            (native_re_mult B) hXStr
            (native_str_in_re_re_mult_empty_local B)
          simpa using h
        rw [← hSplit]
        exact native_str_in_re_re_concat_intro α x qv _ hAlStr hXExt

/--
No-suffix composition for the mult case's retry branch: no suffix of
the whole word is in the tail chain, no suffix of the residual word is
in `A · B*`, and the star-body residual equality turns any witnessing
split into a suffix of the residual word.
-/
theorem StrInReConsumeInternal.consume_mult_retry_no_suffix_local
    (M : SmtModel) (w5 u : native_String)
    (A B : SmtRegLan) (r2t multt : Term)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t)) =
        SmtValue.RegLan A)
    (hMultEval :
      __smtx_model_eval M (__eo_to_smt multt) =
        SmtValue.RegLan (native_re_mult B))
    (hWValid : native_string_valid (w5 ++ u) = true)
    (hNoSufA :
      ∀ pre suf : native_String,
        pre ++ suf = w5 ++ u -> native_str_in_re suf A = false)
    (hNoSufRetry :
      ∀ pre suf : native_String,
        pre ++ suf = w5 ->
          native_str_in_re suf
              (native_re_concat A (native_re_mult B)) = false)
    (hQ :
      ∀ q qv,
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (w5 ++ u) (native_re_concat qv B) =
            native_str_in_re w5 qv) :
    ∀ pre suf : native_String,
      pre ++ suf = w5 ++ u ->
        native_str_in_re suf
            (native_re_concat A (native_re_mult B)) = false := by
  intro pre suf hApp
  cases hMem : native_str_in_re suf
      (native_re_concat A (native_re_mult B)) with
  | false => rfl
  | true =>
      exfalso
      have hSufValid : native_string_valid suf = true := by
        cases h : native_string_valid suf with
        | true => rfl
        | false => simp [native_str_in_re, h] at hMem
      have hListMem :
          nativeListInRe suf
              (native_re_mk_concat A (native_re_mult B)) = true := by
        simpa [native_str_in_re, nativeListInRe, hSufValid] using
          hMem
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf A
          _).1 hListMem with ⟨x, y, hSplit, hXm, hYm⟩
      have hXValid : native_string_valid x = true :=
        StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
          rw [hSplit]
          exact hSufValid)
      have hYValid : native_string_valid y = true :=
        StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
          rw [hSplit]
          exact hSufValid)
      have hXStr : native_str_in_re x A = true := by
        simpa [native_str_in_re, hXValid] using hXm
      have hYStr : native_str_in_re y (native_re_mult B) = true := by
        simpa [native_str_in_re, hYValid] using hYm
      by_cases hYNil : y = []
      · subst hYNil
        have hXSuf := hNoSufA (pre) (x) (by
          rw [← hApp, ← hSplit]
          simp)
        rw [hXSuf] at hXStr
        cases hXStr
      · rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local y B
            hYStr hYNil with ⟨y1, yk, hYSplit, _hYkNe, hY1Mem, hYkMem⟩
        have hPreValid : native_string_valid pre = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local pre suf (by
            rw [hApp]
            exact hWValid)
        have hQEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String pre)))
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat)
                        (StrInReConsumeInternal.consume_unrev_re_local r2t))
                      multt))) =
              SmtValue.RegLan
                (native_re_concat (native_str_to_re pre)
                  (native_re_concat A (native_re_mult B))) := by
          change __smtx_model_eval M
              (SmtTerm.re_concat
                (SmtTerm.str_to_re (SmtTerm.String pre))
                (SmtTerm.re_concat
                  (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t))
                  (__eo_to_smt multt))) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_concat,
            __smtx_model_eval_str_to_re, hAEval, hMultEval,
           ]
        have hEq := hQ _ _ hQEval
        have hSufSplit : suf = (x ++ y1) ++ yk := by
          rw [List.append_assoc, hYSplit, hSplit]
        have hLhs :
            native_str_in_re (w5 ++ u)
                (native_re_concat
                  (native_re_concat (native_str_to_re pre)
                    (native_re_concat A (native_re_mult B)))
                  B) = true := by
          rw [← hApp]
          rw [native_str_in_re_re_concat_assoc_consume_local]
          refine native_str_in_re_re_concat_intro pre suf _ _
            (native_str_in_re_str_to_re_self_local pre hPreValid) ?_
          rw [hSufSplit]
          refine native_str_in_re_re_concat_intro (x ++ y1) yk _ _
            ?_ hYkMem
          exact native_str_in_re_re_concat_intro x y1 _ _ hXStr
            hY1Mem
        rw [hEq] at hLhs
        -- hLhs : w5 ∈ {pre}·(A·B*) — extract the suffix in A·B*
        have hW5Valid : native_string_valid w5 = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local w5 u hWValid
        have hListMem2 :
            nativeListInRe w5
                (native_re_mk_concat (native_str_to_re pre)
                  (native_re_concat A (native_re_mult B))) = true := by
          simpa [native_str_in_re, nativeListInRe, hW5Valid] using
            hLhs
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w5 _
            _).1 hListMem2 with ⟨p2, δ, hSplit3, hP2, hDe⟩
        have hP2Valid : native_string_valid p2 = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local p2 δ (by
            rw [hSplit3]
            exact hW5Valid)
        have hDeValid : native_string_valid δ = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local p2 δ (by
            rw [hSplit3]
            exact hW5Valid)
        have hDeStr :
            native_str_in_re δ
                (native_re_concat A (native_re_mult B)) = true := by
          simpa [native_str_in_re, hDeValid] using hDe
        have hBad := hNoSufRetry p2 δ hSplit3
        rw [hBad] at hDeStr
        cases hDeStr

/--
∀q composition for the mult case's retry branch (residual form).
-/
theorem StrInReConsumeInternal.consume_mult_retry_residual_eq_local
    (M : SmtModel) (w5 u u2 w2 : native_String)
    (A B : SmtRegLan) (r2t multt : Term)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t)) =
        SmtValue.RegLan A)
    (hMultEval :
      __smtx_model_eval M (__eo_to_smt multt) =
        SmtValue.RegLan (native_re_mult B))
    (hNoSufA :
      ∀ pre suf : native_String,
        pre ++ suf = w5 ++ u -> native_str_in_re suf A = false)
    (hU : native_str_in_re u B = true)
    (hDec2 : w5 = w2 ++ u2)
    (hU2 :
      native_str_in_re u2
          (native_re_concat A (native_re_mult B)) = true)
    (hQ1 :
      ∀ q qv,
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (w5 ++ u) (native_re_concat qv B) =
            native_str_in_re w5 qv)
    (hQ2 :
      ∀ q qv,
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re w5
              (native_re_concat qv
                (native_re_concat A (native_re_mult B))) =
            native_str_in_re w2 qv)
    (q qv : _)
    (hQv : __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv) :
    native_str_in_re (w5 ++ u)
        (native_re_concat qv
          (native_re_concat A (native_re_mult B))) =
      native_str_in_re w2 qv := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    have hWuValid : native_string_valid (w5 ++ u) = true := by
      cases h : native_string_valid (w5 ++ u) with
      | true => rfl
      | false => simp [native_str_in_re, h] at hMem
    have hListMem :
        nativeListInRe (w5 ++ u)
            (native_re_mk_concat qv
              (native_re_concat A (native_re_mult B))) = true := by
      simpa [native_str_in_re, nativeListInRe, hWuValid] using hMem
    rcases (nativeListInRe_mk_concat_true_iff_exists_append _ qv
        _).1 hListMem with ⟨α, δ, hSplit, hAl, hDe⟩
    have hAlValid : native_string_valid α = true :=
      StrInReConsumeInternal.native_string_valid_prefix_consume_local α δ (by
        rw [hSplit]
        exact hWuValid)
    have hDeValid : native_string_valid δ = true :=
      StrInReConsumeInternal.native_string_valid_suffix_consume_local α δ (by
        rw [hSplit]
        exact hWuValid)
    have hAlStr : native_str_in_re α qv = true := by
      simpa [native_str_in_re, hAlValid] using hAl
    have hDeStr :
        native_str_in_re δ
            (native_re_concat A (native_re_mult B)) = true := by
      simpa [native_str_in_re, hDeValid] using hDe
    have hDeList :
        nativeListInRe δ
            (native_re_mk_concat A (native_re_mult B)) = true := by
      simpa [native_str_in_re, nativeListInRe, hDeValid] using
        hDeStr
    rcases (nativeListInRe_mk_concat_true_iff_exists_append δ A
        _).1 hDeList with ⟨x, y, hSplit2, hXm, hYm⟩
    have hXValid : native_string_valid x = true :=
      StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
        rw [hSplit2]
        exact hDeValid)
    have hYValid : native_string_valid y = true :=
      StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
        rw [hSplit2]
        exact hDeValid)
    have hXStr : native_str_in_re x A = true := by
      simpa [native_str_in_re, hXValid] using hXm
    have hYStr : native_str_in_re y (native_re_mult B) = true := by
      simpa [native_str_in_re, hYValid] using hYm
    by_cases hYNil : y = []
    · subst hYNil
      exfalso
      have hXSuf := hNoSufA α x (by
        rw [← hSplit, ← hSplit2]
        simp)
      rw [hXSuf] at hXStr
      cases hXStr
    · rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local y B
          hYStr hYNil with ⟨y1, yk, hYSplit, _hYkNe, hY1Mem, hYkMem⟩
      have hQ'Eval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat) q)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (StrInReConsumeInternal.consume_unrev_re_local r2t))
                    multt))) =
            SmtValue.RegLan
              (native_re_concat qv
                (native_re_concat A (native_re_mult B))) := by
        change __smtx_model_eval M
            (SmtTerm.re_concat (__eo_to_smt q)
              (SmtTerm.re_concat
                (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t))
                (__eo_to_smt multt))) = _
        simp [__smtx_model_eval, __smtx_model_eval_re_concat, hQv,
          hAEval, hMultEval]
      have hEq1 := hQ1 _ _ hQ'Eval
      have hLhs :
          native_str_in_re (w5 ++ u)
              (native_re_concat
                (native_re_concat qv
                  (native_re_concat A (native_re_mult B)))
                B) = true := by
        rw [show w5 ++ u = (α ++ (x ++ y1)) ++ yk from by
          rw [List.append_assoc, List.append_assoc, hYSplit, hSplit2,
            hSplit]]
        refine native_str_in_re_re_concat_intro _ yk _ _ ?_ hYkMem
        refine native_str_in_re_re_concat_intro α (x ++ y1) _ _
          hAlStr ?_
        exact native_str_in_re_re_concat_intro x y1 _ _ hXStr hY1Mem
      rw [hEq1] at hLhs
      rw [hQ2 q qv hQv] at hLhs
      exact hLhs
  · intro hMem
    have hW5Mem :
        native_str_in_re w5
            (native_re_concat qv
              (native_re_concat A (native_re_mult B))) = true := by
      rw [hQ2 q qv hQv]
      exact hMem
    have hW5Valid : native_string_valid w5 = true := by
      cases h : native_string_valid w5 with
      | true => rfl
      | false => simp [native_str_in_re, h] at hW5Mem
    have hListMem :
        nativeListInRe w5
            (native_re_mk_concat qv
              (native_re_concat A (native_re_mult B))) = true := by
      simpa [native_str_in_re, nativeListInRe, hW5Valid] using
        hW5Mem
    rcases (nativeListInRe_mk_concat_true_iff_exists_append w5 qv
        _).1 hListMem with ⟨α, δ, hSplit, hAl, hDe⟩
    have hAlValid : native_string_valid α = true :=
      StrInReConsumeInternal.native_string_valid_prefix_consume_local α δ (by
        rw [hSplit]
        exact hW5Valid)
    have hDeValid : native_string_valid δ = true :=
      StrInReConsumeInternal.native_string_valid_suffix_consume_local α δ (by
        rw [hSplit]
        exact hW5Valid)
    have hAlStr : native_str_in_re α qv = true := by
      simpa [native_str_in_re, hAlValid] using hAl
    have hDeStr :
        native_str_in_re δ
            (native_re_concat A (native_re_mult B)) = true := by
      simpa [native_str_in_re, hDeValid] using hDe
    have hDeU :
        native_str_in_re (δ ++ u)
            (native_re_concat A (native_re_mult B)) = true :=
      StrInReConsumeInternal.native_str_in_re_concat_star_absorb_local δ u A B hDeStr hU
    rw [show w5 ++ u = α ++ (δ ++ u) from by
      rw [← hSplit, List.append_assoc]]
    exact native_str_in_re_re_concat_intro α (δ ++ u) qv _ hAlStr
      hDeU

/--
Value decomposition of `__re_rev_comp` on a `re_mult` chunk.
-/
theorem StrInReConsumeInternal.re_rev_comp_mult_decomp_local
    (M : SmtModel) (hM : model_wf M) (r3 : Term)
    (headV : SmtRegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r3)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__re_rev_comp (Term.Apply (Term.UOp UserOp.re_mult) r3))) =
        SmtValue.RegLan headV) :
    ∃ v3,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r3)) =
        SmtValue.RegLan v3 ∧
      headV = native_re_mult v3 := by
  have hNe := StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hEval
  have hBodyNe :
      __re_rev_map_rev r3 StrInReConsumeInternal.re_empty_string_re_consume_local ≠
        Term.Stuck := by
    intro hBad
    apply hNe
    show __eo_mk_apply (Term.UOp UserOp.re_mult)
        (__re_rev_map_rev r3
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      Term.Stuck
    rw [show __re_rev_map_rev r3
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
        Term.Stuck from hBad]
    rfl
  have hShape :
      __re_rev_comp (Term.Apply (Term.UOp UserOp.re_mult) r3) =
        Term.Apply (Term.UOp UserOp.re_mult)
          (__re_rev_map_rev r3
            (Term.Apply (Term.UOp UserOp.str_to_re)
              (Term.String []))) := by
    show __eo_mk_apply (Term.UOp UserOp.re_mult)
        (__re_rev_map_rev r3
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
      _
    cases hX : __re_rev_map_rev r3
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    case Stuck => exact absurd hX hBodyNe
    all_goals rfl
  rw [hShape] at hEval
  have hR3Ty :=
    RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan r3
      hTy
  have hBodyTy :=
    (StrInReConsumeInternal.re_rev_map_rev_type_facts_local r3 _ hR3Ty
      StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
      StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hBodyNe).2.1
  rcases smt_model_eval_reglan_of_type M hM _ hBodyTy with ⟨v3, hV3⟩
  have hRecomp :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.re_mult)
              (__re_rev_map_rev r3
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String []))))) =
        SmtValue.RegLan (native_re_mult v3) := by
    change __smtx_model_eval M
        (SmtTerm.re_mult
          (__eo_to_smt
            (__re_rev_map_rev r3
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String []))))) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_mult, hV3]
  have hEq : headV = native_re_mult v3 := by
    injection hEval.symm.trans hRecomp
  exact ⟨v3, hV3, hEq⟩

/--
Combined unrev semantic induction (no-suffix ∧ residual), to be proven
by ONE `__str_re_consume_rec.induct` with the union/inter companion
motive pairs: the `re_mult` residual-retry branch of the no-suffix
part consumes the ∀q/decomposition conclusions of the residual part,
exactly as in the flat `hRecSemantic` (`no_prefix ∧ residual`).
-/
theorem StrInReConsumeInternal.str_re_consume_rec_unrev_semantic_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s0 r0 fuel0 ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s0 r0 fuel0 := by
  intro s0 r0 fuel0
  refine __str_re_consume_rec.induct
    (fun s r fuel =>
      StrInReConsumeInternal.str_re_consume_inter_unrev_no_suffix_motive M s r fuel ∧
        StrInReConsumeInternal.str_re_consume_inter_unrev_residual_motive M s r fuel)
    (fun s r fuel =>
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s r fuel ∧
        StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s r fuel)
    (fun s r fuel =>
      StrInReConsumeInternal.str_re_consume_union_unrev_no_suffix_motive M s r fuel ∧
        StrInReConsumeInternal.str_re_consume_union_unrev_residual_motive M s r fuel)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
  rotate_left 5
  · intro r fuel
    constructor
    all_goals
      intro side hSTy
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
  · intro s fuel hS
    constructor
    all_goals
      intro side _hSTy hRTy
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hRTy
      cases hRTy
  · intro s r hS hR
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
        (by
          intro hBad
          rw [hBad] at hMemEps
          simp [__str_membership_re] at hMemEps)
  · -- eps-head with concat string: ε-unit keystone massage.
    intro s1 s2 r2 fuel hFuel ih
    exact StrInReConsumeInternal.str_re_consume_rec_unrev_re_concat_empty_left_from_ih_local M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2) r2
      fuel (by
        intro h
        cases h) hFuel ih
  · -- str_to_re head: snoc view + keystone + exact-word cores.
    intro s1 s2 s3 r2 fuel hFuel hS3Ne ih
    have hHeadCompEq :
        __re_rev_comp (Term.Apply (Term.UOp UserOp.str_to_re) s3) =
          Term.Apply (Term.UOp UserOp.str_to_re) s3 := rfl
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hHeadTy :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.UOp UserOp.str_to_re) s3) r2 hRTy).1
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.UOp UserOp.str_to_re) s3) r2 hRTy).2
      have hS3Ty :
          __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
        have hNN : term_has_non_none_type
            (SmtTerm.str_to_re (__eo_to_smt s3)) := by
          unfold term_has_non_none_type
          change __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_re) s3)) ≠
            SmtType.None
          rw [hHeadTy]
          simp
        exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
          (typeof_str_to_re_eq (__eo_to_smt s3)) hNN
      rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel]
        at hSide
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hEqT | hEqF
      · -- s1 = s3 syntactically: head consumed the exact word of s1
        have hS1Eq : s1 = s3 := (eq_of_eo_eq_true s1 s3 hEqT).symm
        subst hS1Eq
        rw [hEqT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
        rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M s1 s2 ssU
            hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
        have hCompEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_comp
                    (Term.Apply (Term.UOp UserOp.str_to_re) s1))) =
              SmtValue.RegLan
                (native_str_to_re (native_unpack_string s1V)) := by
          rw [hHeadCompEq]
          change __smtx_model_eval M
              (SmtTerm.str_to_re (__eo_to_smt s1)) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1V,
            StrInReConsumeInternal.typed_seq_unpack_values_of_eval_local
              M hM s1 s1V hS1Ty hS1V]
        rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
            hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
        rcases (ih.1 (Term.Boolean false) hS2Ty hR2Ty hIteFalse.symm
            rfl (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 ssU2 (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact hSsU2)).1 rvU2 hRvU2 with ⟨hNe2, hSuf2⟩
        constructor
        · rw [hUnp]
          exact StrInReConsumeInternal.list_append_ne_nil_left_consume_local _ _ hNe2
        · intro pre suf hApp
          rw [hUnp] at hApp
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel suf]
          exact StrInReConsumeInternal.native_str_in_re_snoc_word_suffixes_false_local
            (native_unpack_string ssU2) (native_unpack_string s1V)
            rvU2 hSuf2 pre suf hApp
      · rw [hEqF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hLenT | hLenF
        · -- definite length-1 mismatch: last character clash
          rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, hS3Len⟩
          rcases str_re_consume_string_singleton_of_seq_type_len_one
              s1 hS1Ty hS1Len with ⟨c, rfl⟩
          rcases str_re_consume_string_singleton_of_seq_type_len_one
              s3 hS3Ty hS3Len with ⟨d, rfl⟩
          have hCharNe : c ≠ d := by
            intro hcd
            subst hcd
            simp [__eo_eq, native_teq] at hEqF
          refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
          intro rvU hRvU
          simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
          rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
              hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
          rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
            ⟨ss1', hss1', hUnp1⟩
          injection hS1V.symm.trans hss1' with hEq1
          have hS1W : native_unpack_string s1V = [c] := by
            rw [hEq1]
            exact hUnp1
          have hCompEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__re_rev_comp
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String [d])))) =
                SmtValue.RegLan (native_str_to_re [d]) := by
            change __smtx_model_eval M
                (SmtTerm.str_to_re (SmtTerm.String [d])) = _
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
             ]
          rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
              hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
          constructor
          · rw [hUnp, hS1W]
            exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ (by simp)
          · intro pre suf hApp
            rw [hUnp, hS1W] at hApp
            rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel suf]
            exact StrInReConsumeInternal.native_str_in_re_snoc_word_mismatch_suffixes_false_local
              (native_unpack_string ssU2) c d rvU2 hCharNe pre suf hApp
        · -- fallback rebuild cannot be `false`
          exfalso
          rw [hLenF] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          simp at hIteFalse
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.UOp UserOp.str_to_re) s3) r2 hRTy).2
      rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel]
        at hSide
      have hSideNe : side ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hMemEps
        simp [__str_membership_re] at hMemEps
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hEqT | hEqF
      · -- s1 = s3: compose the tail residual with the exact-word snoc
        have hS1Eq : s1 = s3 := (eq_of_eo_eq_true s1 s3 hEqT).symm
        subst hS1Eq
        have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
          rw [hSide, hEqT, eo_ite_true]
        rcases ih.2 side hS2Ty hR2Ty hSide2 hMemEps
            (StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local _ s2 hUnrevNe)
            (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 with
          ⟨hMemTyRaw, hMemTy, hRest⟩
        refine ⟨hMemTyRaw, hMemTy, ?_⟩
        intro ssU ssR hSsU hSsR
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
        rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M s1 s2 ssU
            hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
        have hCompEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_comp
                    (Term.Apply (Term.UOp UserOp.str_to_re) s1))) =
              SmtValue.RegLan
                (native_str_to_re (native_unpack_string s1V)) := by
          rw [hHeadCompEq]
          change __smtx_model_eval M
              (SmtTerm.str_to_re (__eo_to_smt s1)) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1V,
            StrInReConsumeInternal.typed_seq_unpack_values_of_eval_local
              M hM s1 s1V hS1Ty hS1V]
        rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
            hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
        have hS1ValTy :
            __smtx_typeof_value (SmtValue.Seq s1V) =
              SmtType.Seq SmtType.Char := by
          have h := smt_model_eval_preserves_type_of_non_none M hM
            (__eo_to_smt s1) (by
              unfold term_has_non_none_type
              rw [hS1Ty]
              simp)
          rw [hS1V, hS1Ty] at h
          exact h
        have hW1Valid :
            native_string_valid (native_unpack_string s1V) = true :=
          native_unpack_string_valid_of_typeof_seq_char hS1ValTy
        rcases hRest ssU2 ssR (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact hSsU2) hSsR with ⟨hChainR, _hChunkR⟩
        rcases hChainR rvU2 hRvU2 with ⟨⟨u, hUdec, hUmem⟩, hQ⟩
        constructor
        · refine ⟨u ++ native_unpack_string s1V, ?_, ?_⟩
          · rw [hUnp, hUdec, List.append_assoc]
          · rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel]
            exact native_str_in_re_re_concat_intro u
              (native_unpack_string s1V) rvU2
              (native_str_to_re (native_unpack_string s1V)) hUmem
              (native_str_in_re_str_to_re_self_local _ hW1Valid)
        · intro q qv hQv
          rw [hUnp]
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_refl _) hRvURel) _]
          rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_assoc_consume_local qv rvU2
              (native_str_to_re (native_unpack_string s1V))) _]
          rw [StrInReConsumeInternal.native_str_in_re_snoc_word_eq_consume_local
            (native_unpack_string ssU2) (native_unpack_string s1V)
            (native_re_concat qv rvU2) hW1Valid]
          exact hQ q qv hQv
      · rw [hEqF] at hSide
        simp only [eo_ite_false] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hLenT | hLenF
        · exfalso
          rw [hLenT] at hSide
          simp only [eo_ite_true] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
        · exfalso
          rw [hLenF] at hSide
          simp only [eo_ite_false] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
  · -- range head: snoc view + keystone + length-1-class cores.
    intro s1 s2 s3 s5 r2 fuel hFuel ih
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hRangeTy :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
          r2 hRTy).1
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
          r2 hRTy).2
      have hRangeArgs :
          __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
        have hNN : term_has_non_none_type
            (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
          unfold term_has_non_none_type
          change __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) ≠
            SmtType.None
          rw [hRangeTy]
          simp
        exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
          (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
      rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel] at hSide
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hLenT | hLenF
      · rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, hRangeLens⟩
        rcases eo_and_eq_true_local _ _ hRangeLens with ⟨hS3Len, hS5Len⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hS1Len with ⟨c, rfl⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s3
            hRangeArgs.1 hS3Len with ⟨lo, rfl⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s5
            hRangeArgs.2 hS5Len with ⟨hi, rfl⟩
        rw [hLenT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        have hCValidString : native_string_valid [c] = true :=
          native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
        have hLen1 :
            ∀ x : native_String,
              nativeListInRe x (native_re_range [lo] [hi]) = true ->
                x.length = 1 := by
          intro x hx
          exact StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local x lo hi
            (by simpa [native_re_range] using hx)
        have hCompEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_range)
                        (Term.String [lo]))
                      (Term.String [hi])))) =
              SmtValue.RegLan (native_re_range [lo] [hi]) := by
          change __smtx_model_eval M
              (SmtTerm.re_range (SmtTerm.String [lo])
                (SmtTerm.String [hi])) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_range,
           ]
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hMatchT | hMatchF
        · -- head matched: recursion produced false
          rw [hMatchT] at hIteFalse
          simp only [eo_ite_true] at hIteFalse
          refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
          intro rvU hRvU
          simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
          rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
              hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
          rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
            ⟨ss1', hss1', hUnp1⟩
          injection hS1V.symm.trans hss1' with hEq1
          have hS1W : native_unpack_string s1V = [c] := by
            rw [hEq1]
            exact hUnp1
          rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
              hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
          rcases (ih.1 (Term.Boolean false) hS2Ty hR2Ty hIteFalse.symm
              rfl (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 ssU2 (by
                simp only [StrInReConsumeInternal.consume_unrev_str_local]
                exact hSsU2)).1 rvU2 hRvU2 with ⟨hNe2, hSuf2⟩
          constructor
          · rw [hUnp, hS1W]
            exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ (by simp)
          · intro pre suf hApp
            rw [hUnp, hS1W] at hApp
            rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel suf]
            exact StrInReConsumeInternal.native_str_in_re_snoc_len_one_suffixes_false_local
              (native_unpack_string ssU2) [c] rvU2
              (native_re_range [lo] [hi]) hLen1 rfl hSuf2 pre suf hApp
        · -- head mismatched: definite last-character clash
          have hNotIn :
              native_str_in_re [c] (native_re_range [lo] [hi]) =
                false :=
            str_re_consume_range_head_native_eq_of_match_local M hM
              c lo hi false hCValidString hRangeTy hMatchF
          refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
          intro rvU hRvU
          simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
          rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
              hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
          rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
            ⟨ss1', hss1', hUnp1⟩
          injection hS1V.symm.trans hss1' with hEq1
          have hS1W : native_unpack_string s1V = [c] := by
            rw [hEq1]
            exact hUnp1
          rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
              hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
          constructor
          · rw [hUnp, hS1W]
            exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ (by simp)
          · intro pre suf hApp
            rw [hUnp, hS1W] at hApp
            rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel suf]
            exact StrInReConsumeInternal.native_str_in_re_snoc_mismatch_suffixes_false_local
              (native_unpack_string ssU2) c rvU2
              (native_re_range [lo] [hi]) hLen1 hNotIn pre suf hApp
      · -- fallback rebuild cannot be `false`
        exfalso
        rw [hLenF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        simp at hIteFalse
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hRangeTy :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
          r2 hRTy).1
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
          r2 hRTy).2
      have hRangeArgs :
          __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
        have hNN : term_has_non_none_type
            (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
          unfold term_has_non_none_type
          change __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) ≠
            SmtType.None
          rw [hRangeTy]
          simp
        exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
          (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
      rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel] at hSide
      have hSideNe : side ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hMemEps
        simp [__str_membership_re] at hMemEps
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLenT | hLenF
      · rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, hRangeLens⟩
        rcases eo_and_eq_true_local _ _ hRangeLens with ⟨hS3Len, hS5Len⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hS1Len with ⟨c, rfl⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s3
            hRangeArgs.1 hS3Len with ⟨lo, rfl⟩
        rcases str_re_consume_string_singleton_of_seq_type_len_one s5
            hRangeArgs.2 hS5Len with ⟨hi, rfl⟩
        rw [hLenT] at hSide
        simp only [eo_ite_true] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hMatchT | hMatchF
        · -- head matched: compose the tail residual with the snoc core
          have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
            rw [hSide, hMatchT, eo_ite_true]
          have hCValidString : native_string_valid [c] = true :=
            native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
          have hLen1 :
              ∀ x : native_String,
                nativeListInRe x (native_re_range [lo] [hi]) = true ->
                  x.length = 1 := by
            intro x hx
            exact StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local x lo hi
              (by simpa [native_re_range] using hx)
          have hCin :
              native_str_in_re [c] (native_re_range [lo] [hi]) =
                true :=
            str_re_consume_range_head_native_eq_of_match_local M hM
              c lo hi true hCValidString hRangeTy hMatchT
          have hCompEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (__re_rev_comp
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.re_range)
                          (Term.String [lo]))
                        (Term.String [hi])))) =
                SmtValue.RegLan (native_re_range [lo] [hi]) := by
            change __smtx_model_eval M
                (SmtTerm.re_range (SmtTerm.String [lo])
                  (SmtTerm.String [hi])) = _
            simp [__smtx_model_eval, __smtx_model_eval_re_range,
             ]
          rcases ih.2 side hS2Ty hR2Ty hSide2 hMemEps
              (StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local _ s2 hUnrevNe)
              (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 with
            ⟨hMemTyRaw, hMemTy, hRest⟩
          refine ⟨hMemTyRaw, hMemTy, ?_⟩
          intro ssU ssR hSsU hSsR
          refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
          intro rvU hRvU
          simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
          rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
              hSsU with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
          rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
            ⟨ss1', hss1', hUnp1⟩
          injection hS1V.symm.trans hss1' with hEq1
          have hS1W : native_unpack_string s1V = [c] := by
            rw [hEq1]
            exact hUnp1
          rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
              hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
          rcases hRest ssU2 ssR (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact hSsU2) hSsR with ⟨hChainR, _hChunkR⟩
          rcases hChainR rvU2 hRvU2 with ⟨⟨u, hUdec, hUmem⟩, hQ⟩
          constructor
          · refine ⟨u ++ [c], ?_, ?_⟩
            · rw [hUnp, hS1W, hUdec, List.append_assoc]
            · rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                hRvURel]
              exact native_str_in_re_re_concat_intro u [c] rvU2
                (native_re_range [lo] [hi]) hUmem hCin
          · intro q qv hQv
            rw [hUnp, hS1W]
            rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              (smt_value_rel_re_concat_consume_local
                (RuleProofs.smt_value_rel_refl _) hRvURel) _]
            rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              (smt_value_rel_re_concat_assoc_consume_local qv rvU2
                (native_re_range [lo] [hi])) _]
            rw [StrInReConsumeInternal.native_str_in_re_snoc_len_one_eq_consume_local
              (native_unpack_string ssU2) [c]
              (native_re_concat qv rvU2) (native_re_range [lo] [hi])
              hLen1 rfl hCin]
            exact hQ q qv hQv
        · -- head mismatched: the result is `false`, no residual
          exfalso
          rw [hMatchF] at hSide
          simp only [eo_ite_false] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
      · -- fallback rebuild: residual regex is not eps
        exfalso
        rw [hLenF] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide] at hMemEps
        simp [__str_membership_re] at hMemEps
  · intro s1 s2 r2 fuel hFuel ih
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.UOp UserOp.re_allchar) r2 hRTy).2
      rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] at hSide
      have hIteFalse := hSide.symm.trans hFalse
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hCondT | hCondF
      · rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hCondT with ⟨c, rfl⟩
        rw [hCondT] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        simp only [StrInReConsumeInternal.consume_unrev_re_local] at hRvU
        rw [__re_rev_map_rev.eq_3
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          (Term.UOp UserOp.re_allchar) r2 (by
            intro h
            cases h)] at hRvU
        have hAccEval2 :
            __smtx_model_eval M
                (__eo_to_smt
                  (__eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_concat)
                      (__re_rev_comp (Term.UOp UserOp.re_allchar)))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtValue.RegLan
                (native_re_concat native_re_allchar
                  (native_str_to_re [])) := by
          change __smtx_model_eval M
              (SmtTerm.re_concat SmtTerm.re_allchar
                (SmtTerm.str_to_re (SmtTerm.String []))) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_concat,
            __smtx_model_eval_str_to_re,
           ]
        have hEpsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) =
              SmtValue.RegLan (native_str_to_re []) := by
          change __smtx_model_eval M
              (SmtTerm.str_to_re (SmtTerm.String [])) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
           ]
        rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M r2 _ rvU
            hRvU with ⟨⟨newAccV, hNewAccEval⟩, C, hTrans⟩
        rcases hTrans _ _ hAccEval2 with ⟨v1, hv1, hRel1⟩
        injection hRvU.symm.trans hv1 with hV1
        subst hV1
        rw [show native_re_concat native_re_allchar (native_str_to_re []) =
            native_re_allchar from rfl] at hRel1
        rcases hTrans _ _ hEpsEval with ⟨rvU2, hRvU2, hRel2⟩
        rw [show native_re_concat C (native_str_to_re []) = C from by
          cases C <;> rfl] at hRel2
        have hRvURel :
            RuleProofs.smt_value_rel (SmtValue.RegLan rvU)
              (SmtValue.RegLan
                (native_re_concat rvU2 native_re_allchar)) :=
          RuleProofs.smt_value_rel_trans _ _ _ hRel1
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_symm _ _ hRel2)
              (RuleProofs.smt_value_rel_refl _))
        simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
        rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 _ hSsU with
          ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
        rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
          ⟨ss1', hss1', hUnp1⟩
        injection hS1V.symm.trans hss1' with hEq1
        have hS1W : native_unpack_string s1V = [c] := by
          rw [hEq1]
          exact hUnp1
        have hS1Valid : native_string_valid [c] = true :=
          native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
        have hCValid : native_char_valid c = true := by
          simpa [native_string_valid] using hS1Valid
        have hLen1 :
            ∀ x : native_String,
              nativeListInRe x native_re_allchar = true ->
                x.length = 1 :=
          fun x hx => ((nativeListInRe_allchar_true_iff x).1 hx).1
        have hCin :
            native_str_in_re [c] native_re_allchar = true := by
          have hL := (nativeListInRe_allchar_true_iff [c]).2
            ⟨rfl, by simp [hCValid]⟩
          simpa [native_str_in_re, native_string_valid, hCValid,
            nativeListInRe] using hL
        have hIH :=
          (ih.1 (Term.Boolean false) hS2Ty hR2Ty hIteFalse.symm rfl
            (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2
            ssU2 (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact hSsU2)).1 rvU2 (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            exact hRvU2)
        rcases hIH with ⟨_hNe2, hSuf2⟩
        constructor
        · rw [hUnp, hS1W]
          exact StrInReConsumeInternal.list_append_ne_nil_right_consume_local _ _ (by simp)
        · intro pre suf hApp
          rw [hUnp, hS1W] at hApp
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel suf]
          exact StrInReConsumeInternal.native_str_in_re_snoc_len_one_suffixes_false_local
            (native_unpack_string ssU2) [c] rvU2 native_re_allchar
            hLen1 rfl hSuf2 pre suf hApp
      · exfalso
        rw [hCondF] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        simp at hIteFalse
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      have hS1Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
      have hS2Ty :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
      have hR2Ty :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.UOp UserOp.re_allchar) r2 hRTy).2
      rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] at hSide
      have hSideNe : side ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hMemEps
        simp [__str_membership_re] at hMemEps
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hCondT | hCondF
      · rcases str_re_consume_string_singleton_of_seq_type_len_one s1
            hS1Ty hCondT with ⟨c, rfl⟩
        have hSide2 : side = __str_re_consume_rec s2 r2 fuel := by
          rw [hSide, hCondT, eo_ite_true]
        rcases ih.2 side hS2Ty hR2Ty hSide2 hMemEps
            (StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local _ s2 hUnrevNe)
            (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2 with
          ⟨hMemTyRaw, hMemTy, hRest⟩
        refine ⟨hMemTyRaw, hMemTy, ?_⟩
        intro ssU ssR hSsU hSsR
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        simp only [StrInReConsumeInternal.consume_unrev_re_local] at hRvU
        rw [__re_rev_map_rev.eq_3
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          (Term.UOp UserOp.re_allchar) r2 (by
            intro h
            cases h)] at hRvU
        have hAccEval2 :
            __smtx_model_eval M
                (__eo_to_smt
                  (__eo_mk_apply
                    (__eo_mk_apply (Term.UOp UserOp.re_concat)
                      (__re_rev_comp (Term.UOp UserOp.re_allchar)))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtValue.RegLan
                (native_re_concat native_re_allchar
                  (native_str_to_re [])) := by
          change __smtx_model_eval M
              (SmtTerm.re_concat SmtTerm.re_allchar
                (SmtTerm.str_to_re (SmtTerm.String []))) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_concat,
            __smtx_model_eval_str_to_re,
           ]
        have hEpsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) =
              SmtValue.RegLan (native_str_to_re []) := by
          change __smtx_model_eval M
              (SmtTerm.str_to_re (SmtTerm.String [])) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
           ]
        rcases StrInReConsumeInternal.eval_rev_map_rev_acc_factor_consume_local M r2 _ rvU
            hRvU with ⟨⟨newAccV, hNewAccEval⟩, C, hTrans⟩
        rcases hTrans _ _ hAccEval2 with ⟨v1, hv1, hRel1⟩
        injection hRvU.symm.trans hv1 with hV1
        subst hV1
        rw [show native_re_concat native_re_allchar (native_str_to_re []) =
            native_re_allchar from rfl] at hRel1
        rcases hTrans _ _ hEpsEval with ⟨rvU2, hRvU2, hRel2⟩
        rw [show native_re_concat C (native_str_to_re []) = C from by
          cases C <;> rfl] at hRel2
        have hRvURel :
            RuleProofs.smt_value_rel (SmtValue.RegLan rvU)
              (SmtValue.RegLan
                (native_re_concat rvU2 native_re_allchar)) :=
          RuleProofs.smt_value_rel_trans _ _ _ hRel1
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_symm _ _ hRel2)
              (RuleProofs.smt_value_rel_refl _))
        simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU
        rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 _ hSsU with
          ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
        rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
          ⟨ss1', hss1', hUnp1⟩
        injection hS1V.symm.trans hss1' with hEq1
        have hS1W : native_unpack_string s1V = [c] := by
          rw [hEq1]
          exact hUnp1
        have hS1Valid : native_string_valid [c] = true :=
          native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
        have hCValid : native_char_valid c = true := by
          simpa [native_string_valid] using hS1Valid
        have hLen1 :
            ∀ x : native_String,
              nativeListInRe x native_re_allchar = true ->
                x.length = 1 :=
          fun x hx => ((nativeListInRe_allchar_true_iff x).1 hx).1
        have hCin :
            native_str_in_re [c] native_re_allchar = true := by
          have hL := (nativeListInRe_allchar_true_iff [c]).2
            ⟨rfl, by simp [hCValid]⟩
          simpa [native_str_in_re, native_string_valid, hCValid,
            nativeListInRe] using hL
        rcases hRest ssU2 ssR (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact hSsU2) hSsR with ⟨hChainR, _hChunkR⟩
        rcases hChainR rvU2 (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            exact hRvU2) with ⟨⟨u, hUdec, hUmem⟩, hQ⟩
        constructor
        · refine ⟨u ++ [c], ?_, ?_⟩
          · rw [hUnp, hS1W, hUdec, List.append_assoc]
          · rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
              hRvURel]
            exact native_str_in_re_re_concat_intro u [c] rvU2
              native_re_allchar hUmem hCin
        · intro q qv hQv
          rw [hUnp, hS1W]
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_refl _) hRvURel) _]
          rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_assoc_consume_local qv rvU2
              native_re_allchar) _]
          rw [StrInReConsumeInternal.native_str_in_re_snoc_len_one_eq_consume_local
            (native_unpack_string ssU2) [c] (native_re_concat qv rvU2)
            native_re_allchar hLen1 rfl hCin]
          exact hQ q qv hQv
      · exfalso
        have hSide2 : side =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.UOp UserOp.re_allchar))
                r2) := by
          rw [hSide, hCondF, eo_ite_false]
        rw [hSide2] at hMemEps
        simp [__str_membership_re] at hMemEps
  · -- re_mult head with concat fuel: star cores + retry composition.
    intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
      ihLeft ihRight _ihLeftAgain ihResidual
    have hMultTy : ∀ (hRTy : __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.re_mult) r3)) r2)) =
        SmtType.RegLan),
        __smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r3)) =
          SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan := by
      intro hRTy
      have h1 := (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 hRTy)
      exact ⟨h1.1, h1.2,
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
          r3 h1.1⟩
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      rcases hMultTy hRTy with ⟨hStarTy, hR2Ty, hR3Ty⟩
      have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
      have hWfR3 : StrInReConsumeInternal.consume_wf_chain_local r3 :=
        StrInReConsumeInternal.consume_wf_chain_mult_body_local hWfParts.1
      have hWfR2 := hWfParts.2
      rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr] at hSide
      have hIteFalse := hSide.symm.trans hFalse
      refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
      intro rvU hRvU
      rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM
          (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 rvU hStarTy
          hRvU with ⟨rvU2, headV, hCompEval, hRvU2, hRvURel0⟩
      rcases StrInReConsumeInternal.re_rev_comp_mult_decomp_local M hM r3 headV hStarTy
          hCompEval with ⟨v3B, hV3Eval, hHeadVEq⟩
      subst hHeadVEq
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [hIteFalse]
            intro h
            cases h) with hC1T | hC1F
      · -- star-body consume failed: side = right = false
        rw [hC1T] at hIteFalse
        simp only [eo_ite_true] at hIteFalse
        have hLeftF :
            __str_re_consume_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                  s1) s2) r3
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                  fc) fr) = Term.Boolean false :=
          (eq_of_eo_eq_true _ _ hC1T).symm
        rcases (ihLeft.1 (Term.Boolean false) hSTy hR3Ty hLeftF.symm
            rfl hWfR3 ssU hSsU).1 v3B hV3Eval with ⟨_hNeB, hSufB⟩
        rcases (ihRight.1 (Term.Boolean false) hSTy hR2Ty
            hIteFalse.symm rfl hWfR2 ssU hSsU).1 rvU2 hRvU2 with
          ⟨hNeA, hSufA⟩
        refine ⟨hNeA, ?_⟩
        intro pre suf hApp
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          hRvURel0 suf]
        exact StrInReConsumeInternal.native_str_in_re_concat_star_suffixes_false_local
          (native_unpack_string ssU) rvU2 v3B hSufA hSufB pre suf
          hApp
      · rw [hC1F] at hIteFalse
        simp only [eo_ite_false] at hIteFalse
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [hIteFalse]
              intro h
              cases h) with hC2T | hC2F
        · rw [hC2T] at hIteFalse
          simp only [eo_ite_true] at hIteFalse
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [hIteFalse]
                intro h
                cases h) with hC3T | hC3F
          · rw [hC3T] at hIteFalse
            simp only [eo_ite_true] at hIteFalse
            rcases eo_ite_cases_of_ne_stuck _ _ _
                (by
                  rw [hIteFalse]
                  intro h
                  cases h) with hC4T | hC4F
            · exfalso
              rw [hC4T] at hIteFalse
              simp only [eo_ite_true] at hIteFalse
              cases hIteFalse
            · -- retry consume returned false
              rw [hC4F] at hIteFalse
              simp only [eo_ite_false] at hIteFalse
              have hMemEpsL :
                  __str_membership_re
                      (__str_re_consume_rec
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            s1) s2) r3
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            fc) fr)) =
                    StrInReConsumeInternal.re_empty_string_re_consume_local :=
                (eq_of_eo_eq_true _ _ hC2T).symm
              have hRightF :=
                eq_of_eo_is_eq_true_consume_local _ _ hC3T
              have hUnrevNeS :=
                StrInReConsumeInternal.consume_unrev_str_ne_stuck_of_eval_local M _ ssU hSsU
              rcases ihLeft.2 _ hSTy hR3Ty rfl hMemEpsL hUnrevNeS
                  hWfR3 with ⟨hMemTyRawL, hMemTyL, hRestL⟩
              rcases
                smt_eval_seq_char_of_smt_type_seq_char_consume_local
                  M hM _ hMemTyL with ⟨ssR', hSsR'⟩
              rcases hRestL ssU ssR' hSsU hSsR' with ⟨hChainL, _⟩
              rcases hChainL v3B hV3Eval with
                ⟨⟨u, hUdec, hUmem⟩, hQ1⟩
              rcases (ihResidual.1 (Term.Boolean false) hMemTyRawL
                  hRTy hIteFalse.symm rfl hWf ssR' hSsR').1 rvU
                  hRvU with ⟨_hNeR, hSufRetry0⟩
              rcases (ihRight.1 (Term.Boolean false) hSTy hR2Ty
                  hRightF.symm rfl hWfR2 ssU hSsU).1 rvU2 hRvU2 with
                ⟨hNeA, hSufA⟩
              have hSufRetry :
                  ∀ p s : native_String,
                    p ++ s = native_unpack_string ssR' ->
                      native_str_in_re s
                          (native_re_concat rvU2
                            (native_re_mult v3B)) = false := by
                intro p s hps
                rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                  hRvURel0 s]
                exact hSufRetry0 p s hps
              have hUnrevTy :
                  __smtx_typeof
                      (__eo_to_smt
                        (StrInReConsumeInternal.consume_unrev_str_local
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat)
                              s1) s2))) =
                    SmtType.Seq SmtType.Char := by
                simp only [StrInReConsumeInternal.consume_unrev_str_local]
                exact smt_typeof_list_rev_str_concat_of_seq _
                  SmtType.Char
                  (eo_list_rev_is_list_true_of_ne_stuck _ _
                    (by simpa [StrInReConsumeInternal.consume_unrev_str_local] using
                      hUnrevNeS))
                  hSTy
                  (by simpa [StrInReConsumeInternal.consume_unrev_str_local] using hUnrevNeS)
              have hWValid :
                  native_string_valid (native_unpack_string ssU) =
                    true := by
                have h := smt_model_eval_preserves_type_of_non_none M
                  hM
                  (__eo_to_smt
                    (StrInReConsumeInternal.consume_unrev_str_local
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat) s1)
                        s2)))
                  (by
                    unfold term_has_non_none_type
                    rw [hUnrevTy]
                    simp)
                rw [hSsU, hUnrevTy] at h
                exact native_unpack_string_valid_of_typeof_seq_char h
              refine ⟨hNeA, ?_⟩
              intro pre suf hApp
              rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                hRvURel0 suf]
              have hApp' :
                  pre ++ suf = native_unpack_string ssR' ++ u := by
                rw [← hUdec]
                exact hApp
              have hNoSufA' :
                  ∀ p s : native_String,
                    p ++ s = native_unpack_string ssR' ++ u ->
                      native_str_in_re s rvU2 = false := by
                intro p s hps
                exact hSufA p s (by
                  rw [hUdec]
                  exact hps)
              have hQ1' :
                  ∀ q qv,
                    __smtx_model_eval M (__eo_to_smt q) =
                      SmtValue.RegLan qv ->
                      native_str_in_re
                          (native_unpack_string ssR' ++ u)
                          (native_re_concat qv v3B) =
                        native_str_in_re (native_unpack_string ssR')
                          qv := by
                intro q qv hq
                have h := hQ1 q qv hq
                rw [hUdec] at h
                exact h
              have hWValid' :
                  native_string_valid
                      (native_unpack_string ssR' ++ u) = true := by
                rw [← hUdec]
                exact hWValid
              exact StrInReConsumeInternal.consume_mult_retry_no_suffix_local M
                (native_unpack_string ssR') u rvU2 v3B r2
                (__re_rev_comp (Term.Apply (Term.UOp UserOp.re_mult)
                  r3))
                hRvU2 hCompEval hWValid' hNoSufA' hSufRetry hQ1'
                pre suf hApp'
          · exfalso
            rw [hC3F] at hIteFalse
            simp only [eo_ite_false] at hIteFalse
            cases hIteFalse
        · exfalso
          rw [hC2F] at hIteFalse
          simp only [eo_ite_false] at hIteFalse
          cases hIteFalse
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      rcases hMultTy hRTy with ⟨hStarTy, hR2Ty, hR3Ty⟩
      have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
      have hWfR3 : StrInReConsumeInternal.consume_wf_chain_local r3 :=
        StrInReConsumeInternal.consume_wf_chain_mult_body_local hWfParts.1
      have hWfR2 := hWfParts.2
      rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr] at hSide
      have hSideNe : side ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hMemEps
        simp [__str_membership_re] at hMemEps
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hC1T | hC1F
      · -- side is the right (tail) consume result
        rw [hC1T] at hSide
        simp only [eo_ite_true] at hSide
        have hLeftF :
            __str_re_consume_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                  s1) s2) r3
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                  fc) fr) = Term.Boolean false :=
          (eq_of_eo_eq_true _ _ hC1T).symm
        rcases ihRight.2 side hSTy hR2Ty hSide hMemEps hUnrevNe
            hWfR2 with ⟨hMemTyRaw, hMemTy, hRest⟩
        refine ⟨hMemTyRaw, hMemTy, ?_⟩
        intro ssU ssR hSsU hSsR
        refine ⟨?_, fun hNotConcat => ((hNotConcat _ _ rfl).elim)⟩
        intro rvU hRvU
        rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM
            (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 rvU hStarTy
            hRvU with ⟨rvU2, headV, hCompEval, hRvU2, hRvURel0⟩
        rcases StrInReConsumeInternal.re_rev_comp_mult_decomp_local M hM r3 headV hStarTy
            hCompEval with ⟨v3B, hV3Eval, hHeadVEq⟩
        subst hHeadVEq
        rcases (ihLeft.1 (Term.Boolean false) hSTy hR3Ty hLeftF.symm
            rfl hWfR3 ssU hSsU).1 v3B hV3Eval with ⟨_hNeB, hSufB⟩
        rcases (hRest ssU ssR hSsU hSsR).1 rvU2 hRvU2 with
          ⟨⟨u2, hU2dec, hU2mem⟩, hQ⟩
        constructor
        · refine ⟨u2, hU2dec, ?_⟩
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel0]
          have h := native_str_in_re_re_concat_intro u2 [] rvU2
            (native_re_mult v3B) hU2mem
            (native_str_in_re_re_mult_empty_local v3B)
          simpa using h
        · intro q qv hQv
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            (smt_value_rel_re_concat_consume_local
              (RuleProofs.smt_value_rel_refl _) hRvURel0) _]
          exact StrInReConsumeInternal.consume_mult_left_false_residual_eq_local
            (native_unpack_string ssU) (native_unpack_string ssR) qv
            rvU2 v3B hSufB (hQ q qv hQv)
      · rw [hC1F] at hSide
        simp only [eo_ite_false] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hC2T | hC2F
        · rw [hC2T] at hSide
          simp only [eo_ite_true] at hSide
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [← hSide]
                exact hSideNe) with hC3T | hC3F
          · rw [hC3T] at hSide
            simp only [eo_ite_true] at hSide
            rcases eo_ite_cases_of_ne_stuck _ _ _
                (by
                  rw [← hSide]
                  exact hSideNe) with hC4T | hC4F
            · -- rebuilt fallback: residual regex is not eps
              exfalso
              rw [hC4T] at hSide
              simp only [eo_ite_true] at hSide
              rw [hSide] at hMemEps
              simp [__str_membership_re] at hMemEps
            · -- side is the RETRY result
              rw [hC4F] at hSide
              simp only [eo_ite_false] at hSide
              have hMemEpsL :
                  __str_membership_re
                      (__str_re_consume_rec
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            s1) s2) r3
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            fc) fr)) =
                    StrInReConsumeInternal.re_empty_string_re_consume_local :=
                (eq_of_eo_eq_true _ _ hC2T).symm
              have hRightF :=
                eq_of_eo_is_eq_true_consume_local _ _ hC3T
              rcases ihLeft.2 _ hSTy hR3Ty rfl hMemEpsL hUnrevNe
                  hWfR3 with ⟨hMemTyRawL, hMemTyL, hRestL⟩
              have hMemTransNeL :
                  StrInReConsumeInternal.consume_unrev_str_local
                      (__str_membership_str
                        (__str_re_consume_rec
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat)
                              s1) s2) r3
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_concat)
                              fc) fr))) ≠ Term.Stuck := by
                intro hBad
                rw [hBad] at hMemTyL
                rw [show __eo_to_smt Term.Stuck = SmtTerm.None from
                  rfl] at hMemTyL
                rw [TranslationProofs.smtx_typeof_none] at hMemTyL
                cases hMemTyL
              rcases ihResidual.2 side hMemTyRawL hRTy hSide hMemEps
                  hMemTransNeL hWf with
                ⟨hMemTyRawR, hMemTyR, hRestR⟩
              refine ⟨hMemTyRawR, hMemTyR, ?_⟩
              intro ssU ssR hSsU hSsR
              refine ⟨?_, fun hNotConcat =>
                ((hNotConcat _ _ rfl).elim)⟩
              intro rvU hRvU
              rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M
                  hM (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 rvU
                  hStarTy hRvU with
                ⟨rvU2, headV, hCompEval, hRvU2, hRvURel0⟩
              rcases StrInReConsumeInternal.re_rev_comp_mult_decomp_local M hM r3 headV
                  hStarTy hCompEval with ⟨v3B, hV3Eval, hHeadVEq⟩
              subst hHeadVEq
              rcases
                smt_eval_seq_char_of_smt_type_seq_char_consume_local
                  M hM _ hMemTyL with ⟨ssR', hSsR'⟩
              rcases hRestL ssU ssR' hSsU hSsR' with ⟨hChainL, _⟩
              rcases hChainL v3B hV3Eval with
                ⟨⟨u, hUdec, hUmem⟩, hQ1⟩
              rcases hRestR ssR' ssR hSsR' hSsR with ⟨hChainR, _⟩
              rcases hChainR rvU hRvU with
                ⟨⟨u2, hU2dec, hU2mem0⟩, hQ2⟩
              have hU2mem :
                  native_str_in_re u2
                      (native_re_concat rvU2 (native_re_mult v3B)) =
                    true := by
                rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                  hRvURel0]
                exact hU2mem0
              rcases (ihRight.1 (Term.Boolean false) hSTy hR2Ty
                  hRightF.symm rfl hWfR2 ssU hSsU).1 rvU2 hRvU2 with
                ⟨_hNeA, hSufA⟩
              constructor
              · refine ⟨u2 ++ u, ?_, ?_⟩
                · rw [hUdec, hU2dec, List.append_assoc]
                · rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                    hRvURel0]
                  exact StrInReConsumeInternal.native_str_in_re_concat_star_absorb_local u2
                    u rvU2 v3B hU2mem hUmem
              · intro q qv hQv
                rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                  (smt_value_rel_re_concat_consume_local
                    (RuleProofs.smt_value_rel_refl _) hRvURel0) _]
                have hNoSufA' :
                    ∀ p s : native_String,
                      p ++ s =
                        native_unpack_string ssR' ++ u ->
                        native_str_in_re s rvU2 = false := by
                  intro p s hps
                  exact hSufA p s (by
                    rw [hUdec]
                    exact hps)
                have hQ1' :
                    ∀ q0 qv0,
                      __smtx_model_eval M (__eo_to_smt q0) =
                        SmtValue.RegLan qv0 ->
                        native_str_in_re
                            (native_unpack_string ssR' ++ u)
                            (native_re_concat qv0 v3B) =
                          native_str_in_re
                            (native_unpack_string ssR') qv0 := by
                  intro q0 qv0 hq0
                  have h := hQ1 q0 qv0 hq0
                  rw [hUdec] at h
                  exact h
                have hQ2' :
                    ∀ q0 qv0,
                      __smtx_model_eval M (__eo_to_smt q0) =
                        SmtValue.RegLan qv0 ->
                        native_str_in_re
                            (native_unpack_string ssR')
                            (native_re_concat qv0
                              (native_re_concat rvU2
                                (native_re_mult v3B))) =
                          native_str_in_re
                            (native_unpack_string ssR) qv0 := by
                  intro q0 qv0 hq0
                  have h := hQ2 q0 qv0 hq0
                  rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                    (smt_value_rel_re_concat_consume_local
                      (RuleProofs.smt_value_rel_refl _) hRvURel0) _]
                    at h
                  exact h
                have hGoal := StrInReConsumeInternal.consume_mult_retry_residual_eq_local M
                  (native_unpack_string ssR') u u2
                  (native_unpack_string ssR) rvU2 v3B r2
                  (__re_rev_comp
                    (Term.Apply (Term.UOp UserOp.re_mult) r3))
                  hRvU2 hCompEval hNoSufA' hUmem hU2dec hU2mem hQ1'
                  hQ2' q qv hQv
                rw [hUdec]
                exact hGoal
          · exfalso
            rw [hC3F] at hSide
            simp only [eo_ite_false] at hSide
            rw [hSide] at hMemEps
            simp [__str_membership_re] at hMemEps
        · exfalso
          rw [hC2F] at hSide
          simp only [eo_ite_false] at hSide
          rw [hSide] at hMemEps
          simp [__str_membership_re] at hMemEps
  · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    have hEq :=
      str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
        s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      have hBad := (hSide.trans hEq).symm.trans hFalse
      simp at hBad
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      rw [hSide.trans hEq] at hMemEps
      simp [__str_membership_re] at hMemEps
  rotate_left
  · -- eps-head with non-concat string: ε-unit keystone massage.
    intro s r fuel hS hFuel _hNotConcat ih
    exact StrInReConsumeInternal.str_re_consume_rec_unrev_re_concat_empty_left_from_ih_local M
      s r fuel hS hFuel ih
  · intro s r1 r2 fuel hS hFuel ih
    have hEq := str_re_consume_rec_re_inter_eq s r1 r2 fuel hS hFuel
    constructor
    · intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      constructor
      · intro rvU hRvU
        exfalso
        exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
          (StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
            (by
              intro h
              simp at h)
            (fun a b h => by simp at h))
      · intro _hNotConcat rvU hRvU
        exact ih.1 side hSTy hRTy (hSide.trans hEq) hFalse
          (StrInReConsumeInternal.consume_wf_chain_inter_tree_local hWf) ssU hSsU
          rvU hRvU
    · intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      rcases ih.2 side hSTy hRTy (hSide.trans hEq) hMemEps hUnrevNe
        (StrInReConsumeInternal.consume_wf_chain_inter_tree_local hWf) with
        ⟨hMemTyRaw, hMemTy, hRest⟩
      refine ⟨hMemTyRaw, hMemTy, ?_⟩
      intro ssU ssR hSsU hSsR
      constructor
      · intro rvU hRvU
        exfalso
        exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
          (StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
            (by
              intro h
              simp at h)
            (fun a b h => by simp at h))
      · intro _hNotConcat rvU hRvU
        exact hRest ssU ssR hSsU hSsR rvU hRvU
  · intro s r1 r2 fuel hS hFuel ih
    have hEq := str_re_consume_rec_re_union_eq s r1 r2 fuel hS hFuel
    constructor
    · intro side hSTy hRTy hSide hFalse hWf ssU hSsU
      constructor
      · intro rvU hRvU
        exfalso
        exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
          (StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
            (by
              intro h
              simp at h)
            (fun a b h => by simp at h))
      · intro _hNotConcat rvU hRvU
        exact ih.1 side hSTy hRTy (hSide.trans hEq) hFalse
          (StrInReConsumeInternal.consume_wf_chain_union_tree_local hWf) ssU hSsU
          rvU hRvU
    · intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      rcases ih.2 side hSTy hRTy (hSide.trans hEq) hMemEps hUnrevNe
        (StrInReConsumeInternal.consume_wf_chain_union_tree_local hWf) with
        ⟨hMemTyRaw, hMemTy, hRest⟩
      refine ⟨hMemTyRaw, hMemTy, ?_⟩
      intro ssU ssR hSsU hSsR
      constructor
      · intro rvU hRvU
        exfalso
        exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
          (StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
            (by
              intro h
              simp at h)
            (fun a b h => by simp at h))
      · intro _hNotConcat rvU hRvU
        exact hRest ssU ssR hSsU hSsR rvU hRvU
  · -- default (rebuilt `str_in_re s r`): the no-suffix component is a
    -- constructor clash; the residual component is the consume-finished
    -- base case (`r = eps`).
    intro s r fuel hS hR hFuel hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
      hNotRConcatEmpty hNotRInter hNotRUnion
    have hEq := str_re_consume_rec_default_eq s r fuel hS hR hFuel
      hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      have hBad := (hSide.trans hEq).symm.trans hFalse
      cases hBad
    · intro side hSTy hRTy hSide hMemEps hUnrevNe _hWf
      have hSideEq : side =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r :=
        hSide.trans hEq
      have hREq : r = StrInReConsumeInternal.re_empty_string_re_consume_local := by
        rw [hSideEq] at hMemEps
        simpa [__str_membership_re] using hMemEps
      subst hREq
      have hMembStr : __str_membership_str side = s := by
        rw [hSideEq]
        rfl
      have hUnrevNe' :
          __eo_list_rev (Term.UOp UserOp.str_concat) s ≠ Term.Stuck := by
        simpa [StrInReConsumeInternal.consume_unrev_str_local] using hUnrevNe
      have hList : __eo_is_list (Term.UOp UserOp.str_concat) s =
          Term.Boolean true :=
        eo_list_rev_is_list_true_of_ne_stuck _ _ hUnrevNe'
      have hEpsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String []))) =
            SmtValue.RegLan (native_str_to_re []) := by
        change __smtx_model_eval M
            (SmtTerm.str_to_re (SmtTerm.String [])) = _
        simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
         ]
      refine ⟨?_, ?_, ?_⟩
      · rw [hMembStr]
        exact hSTy
      · rw [hMembStr]
        simp only [StrInReConsumeInternal.consume_unrev_str_local]
        exact smt_typeof_list_rev_str_concat_of_seq s SmtType.Char hList
          hSTy hUnrevNe'
      · intro ssU ssR hSsU hSsR
        rw [hMembStr] at hSsR
        injection hSsU.symm.trans hSsR with hEqSs
        subst hEqSs
        constructor
        · intro rvU hRvU
          have hUnrevEps :
              StrInReConsumeInternal.consume_unrev_re_local StrInReConsumeInternal.re_empty_string_re_consume_local =
                StrInReConsumeInternal.re_empty_string_re_consume_local := rfl
          rw [hUnrevEps] at hRvU
          injection hRvU.symm.trans hEpsEval with hRvEq
          subst hRvEq
          refine ⟨⟨[], by simp, ?_⟩, ?_⟩
          · exact StrInReConsumeInternal.native_str_in_re_nil_str_to_re_nil_consume_local
          · intro q qv _hQv
            have h := StrInReConsumeInternal.native_str_in_re_snoc_word_eq_consume_local
              (native_unpack_string ssU) [] qv (by
                simp [native_string_valid])
            simpa using h
        · intro _hNotConcat rvU hRvU
          have hRevCompEps :
              __re_rev_comp StrInReConsumeInternal.re_empty_string_re_consume_local =
                StrInReConsumeInternal.re_empty_string_re_consume_local := rfl
          rw [hRevCompEps] at hRvU
          injection hRvU.symm.trans hEpsEval with hRvEq
          subst hRvEq
          refine ⟨⟨[], by simp, ?_⟩, ?_⟩
          · exact StrInReConsumeInternal.native_str_in_re_nil_str_to_re_nil_consume_local
          · intro q qv _hQv
            have h := StrInReConsumeInternal.native_str_in_re_snoc_word_eq_consume_local
              (native_unpack_string ssU) [] qv (by
                simp [native_string_valid])
            simpa using h
  · intro r fuel
    constructor
    all_goals
      intro side hSTy
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
  · intro s r hS
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r side hS hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r side hS hSide
        (by
          intro hBad
          rw [hBad] at hMemEps
          simp [__str_membership_re] at hMemEps)
  rotate_left
  rotate_left
  · intro s r fuel hS hFuel hNotNone hNotUnion
    have hEq := str_re_consume_union_default_eq s r fuel hS hFuel
      hNotNone hNotUnion
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      have hBad := (hSide.trans hEq).symm.trans hFalse
      cases hBad
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      rw [hSide.trans hEq] at hMemEps
      simp [__str_membership_re] at hMemEps
  · intro r fuel
    constructor
    all_goals
      intro side hSTy
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
  · intro s r hS
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r side hS hSide
        (by
          rw [hFalse]
          intro h
          cases h)
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r side hS hSide
        (by
          intro hBad
          rw [hBad] at hMemEps
          simp [__str_membership_re] at hMemEps)
  rotate_left
  rotate_left
  · intro s r fuel hS hFuel hNotAll hNotInter
    have hEq := str_re_consume_inter_default_eq s r fuel hS hFuel
      hNotAll hNotInter
    constructor
    · intro side _hSTy _hRTy hSide hFalse
      exfalso
      have hBad := (hSide.trans hEq).symm.trans hFalse
      cases hBad
    · intro side _hSTy _hRTy hSide hMemEps
      exfalso
      rw [hSide.trans hEq] at hMemEps
      simp [__str_membership_re] at hMemEps
  rotate_left
  · -- union with re_none tail: rec-IH chain form + union-∅ unit.
    intro s r fuel hS hFuel ih
    have hEq := str_re_consume_union_re_none_eq s r fuel hS hFuel
    have hRevCompStuck :
        __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local =
            Term.Stuck ->
          __re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none)) =
            Term.Stuck := by
      intro hBad
      show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev r
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp (Term.UOp UserOp.re_none)) = Term.Stuck
      rw [show __re_rev_map_rev r
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
          Term.Stuck from hBad]
      rfl
    have hRevCompShape :
        __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck ->
          __re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none)) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
              (Term.UOp UserOp.re_none) := by
      intro hXNe
      show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_union)
            (__re_rev_map_rev r
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp (Term.UOp UserOp.re_none)) = _
      cases hX : __re_rev_map_rev r
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      case Stuck => exact absurd hX hXNe
      all_goals rfl
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU rvU hRvU
      have hXNe :
          __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck := by
        intro hBad
        apply StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
        exact hRevCompStuck hBad
      rw [hRevCompShape hXNe] at hRvU
      have hR1Ty : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local r
          (Term.UOp UserOp.re_none) hRTy).1
      have hXTy :
          __smtx_typeof
              (__eo_to_smt
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local)) =
            SmtType.RegLan :=
        (StrInReConsumeInternal.re_rev_map_rev_type_facts_local r _ hR1Ty
          StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
          StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hXNe).2.1
      have hUnionTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union)
                    (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
                  (Term.UOp UserOp.re_none))) =
            SmtType.RegLan := by
        exact smt_typeof_re_union_of_reglan_consume_local _ _ hXTy
          (by simp [__smtx_typeof])
      rcases eval_re_union_parts_consume_local M hM _ _ rvU hUnionTy
          hRvU with
        ⟨rvX, rvNone, _hXTy2, _hNoneTy, hXEval, hNoneEval, hRvUEq⟩
      have hRvNone : rvNone = native_re_none := by
        change __smtx_model_eval M SmtTerm.re_none =
          SmtValue.RegLan rvNone at hNoneEval
        simpa [__smtx_model_eval] using hNoneEval.symm
      subst hRvNone
      subst hRvUEq
      rcases (ih.1 side hSTy hR1Ty (hSide.trans hEq) hFalse
          (StrInReConsumeInternal.consume_wf_union_tail_parts_local hWf).1 ssU hSsU).1
          rvX (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            exact hXEval) with ⟨hNe, hSuf⟩
      refine ⟨hNe, ?_⟩
      intro pre suf hApp
      rw [native_str_in_re_re_union_right_none_consume_local]
      exact hSuf pre suf hApp
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      have hR1Ty : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local r
          (Term.UOp UserOp.re_none) hRTy).1
      rcases ih.2 side hSTy hR1Ty (hSide.trans hEq) hMemEps hUnrevNe
          (StrInReConsumeInternal.consume_wf_union_tail_parts_local hWf).1 with
        ⟨hMemTyRaw, hMemTy, hRest⟩
      refine ⟨hMemTyRaw, hMemTy, ?_⟩
      intro ssU ssR hSsU hSsR rvU hRvU
      have hXNe :
          __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck := by
        intro hBad
        apply StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
        exact hRevCompStuck hBad
      rw [hRevCompShape hXNe] at hRvU
      have hXTy :
          __smtx_typeof
              (__eo_to_smt
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local)) =
            SmtType.RegLan :=
        (StrInReConsumeInternal.re_rev_map_rev_type_facts_local r _ hR1Ty
          StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
          StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hXNe).2.1
      have hUnionTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_union)
                    (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
                  (Term.UOp UserOp.re_none))) =
            SmtType.RegLan := by
        exact smt_typeof_re_union_of_reglan_consume_local _ _ hXTy
          (by simp [__smtx_typeof])
      rcases eval_re_union_parts_consume_local M hM _ _ rvU hUnionTy
          hRvU with
        ⟨rvX, rvNone, _hXTy2, _hNoneTy, hXEval, hNoneEval, hRvUEq⟩
      have hRvNone : rvNone = native_re_none := by
        change __smtx_model_eval M SmtTerm.re_none =
          SmtValue.RegLan rvNone at hNoneEval
        simpa [__smtx_model_eval] using hNoneEval.symm
      subst hRvNone
      subst hRvUEq
      rcases (hRest ssU ssR hSsU hSsR).1 rvX (by
          simp only [StrInReConsumeInternal.consume_unrev_re_local]
          exact hXEval) with ⟨⟨u, hUdec, hUmem⟩, hQ⟩
      constructor
      · refine ⟨u, hUdec, ?_⟩
        rw [native_str_in_re_re_union_right_none_consume_local]
        exact hUmem
      · intro q qv hQv
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          (smt_value_rel_re_concat_consume_local
            (RuleProofs.smt_value_rel_refl (SmtValue.RegLan qv))
            (StrInReConsumeInternal.smt_value_rel_union_right_none_consume_local rvX))]
        exact hQ q qv hQv
  rotate_left
  · -- inter with re_all tail: rec-IH chain form + inter-⊤ unit.
    intro s r fuel hS hFuel ih
    have hEq := str_re_consume_inter_re_all_eq s r fuel hS hFuel
    have hRevCompStuck :
        __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local =
            Term.Stuck ->
          __re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all)) =
            Term.Stuck := by
      intro hBad
      show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev r
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp (Term.UOp UserOp.re_all)) = Term.Stuck
      rw [show __re_rev_map_rev r
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
          Term.Stuck from hBad]
      rfl
    have hRevCompShape :
        __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck ->
          __re_rev_comp
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all)) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
              (Term.UOp UserOp.re_all) := by
      intro hXNe
      show __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.re_inter)
            (__re_rev_map_rev r
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
          (__re_rev_comp (Term.UOp UserOp.re_all)) = _
      cases hX : __re_rev_map_rev r
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      case Stuck => exact absurd hX hXNe
      all_goals rfl
    constructor
    · -- no-suffix component
      intro side hSTy hRTy hSide hFalse hWf ssU hSsU rvU hRvU
      have hXNe :
          __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck := by
        intro hBad
        apply StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
        exact hRevCompStuck hBad
      rw [hRevCompShape hXNe] at hRvU
      have hR1Ty : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local r
          (Term.UOp UserOp.re_all) hRTy).1
      have hXTy :
          __smtx_typeof
              (__eo_to_smt
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local)) =
            SmtType.RegLan :=
        (StrInReConsumeInternal.re_rev_map_rev_type_facts_local r _ hR1Ty
          StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
          StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hXNe).2.1
      have hInterTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_inter)
                    (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
                  (Term.UOp UserOp.re_all))) =
            SmtType.RegLan := by
        exact smt_typeof_re_inter_of_reglan_consume_local _ _ hXTy
          (by simp [__smtx_typeof])
      rcases eval_re_inter_parts_consume_local M hM _ _ rvU hInterTy
          hRvU with
        ⟨rvX, rvAll, _hXTy2, _hAllTy, hXEval, hAllEval, hRvUEq⟩
      have hRvAll : rvAll = native_re_all := by
        change __smtx_model_eval M SmtTerm.re_all =
          SmtValue.RegLan rvAll at hAllEval
        simpa [__smtx_model_eval] using hAllEval.symm
      subst hRvAll
      subst hRvUEq
      rcases (ih.1 side hSTy hR1Ty (hSide.trans hEq) hFalse
          (StrInReConsumeInternal.consume_wf_inter_tail_parts_local hWf).1 ssU hSsU).1
          rvX (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            exact hXEval) with ⟨hNe, hSuf⟩
      refine ⟨hNe, ?_⟩
      intro pre suf hApp
      rw [native_str_in_re_re_inter_right_all_consume_local]
      exact hSuf pre suf hApp
    · -- residual component
      intro side hSTy hRTy hSide hMemEps hUnrevNe hWf
      have hR1Ty : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local r
          (Term.UOp UserOp.re_all) hRTy).1
      rcases ih.2 side hSTy hR1Ty (hSide.trans hEq) hMemEps hUnrevNe
          (StrInReConsumeInternal.consume_wf_inter_tail_parts_local hWf).1 with
        ⟨hMemTyRaw, hMemTy, hRest⟩
      refine ⟨hMemTyRaw, hMemTy, ?_⟩
      intro ssU ssR hSsU hSsR rvU hRvU
      have hXNe :
          __re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local ≠
            Term.Stuck := by
        intro hBad
        apply StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
        exact hRevCompStuck hBad
      rw [hRevCompShape hXNe] at hRvU
      have hXTy :
          __smtx_typeof
              (__eo_to_smt
                (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local)) =
            SmtType.RegLan :=
        (StrInReConsumeInternal.re_rev_map_rev_type_facts_local r _ hR1Ty
          StrInReConsumeInternal.re_empty_string_is_re_concat_list_true_consume_local
          StrInReConsumeInternal.smt_typeof_re_empty_string_consume_local hXNe).2.1
      have hInterTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_inter)
                    (__re_rev_map_rev r StrInReConsumeInternal.re_empty_string_re_consume_local))
                  (Term.UOp UserOp.re_all))) =
            SmtType.RegLan := by
        exact smt_typeof_re_inter_of_reglan_consume_local _ _ hXTy
          (by simp [__smtx_typeof])
      rcases eval_re_inter_parts_consume_local M hM _ _ rvU hInterTy
          hRvU with
        ⟨rvX, rvAll, _hXTy2, _hAllTy, hXEval, hAllEval, hRvUEq⟩
      have hRvAll : rvAll = native_re_all := by
        change __smtx_model_eval M SmtTerm.re_all =
          SmtValue.RegLan rvAll at hAllEval
        simpa [__smtx_model_eval] using hAllEval.symm
      subst hRvAll
      subst hRvUEq
      rcases (hRest ssU ssR hSsU hSsR).1 rvX (by
          simp only [StrInReConsumeInternal.consume_unrev_re_local]
          exact hXEval) with ⟨⟨u, hUdec, hUmem⟩, hQ⟩
      constructor
      · refine ⟨u, hUdec, ?_⟩
        rw [native_str_in_re_re_inter_right_all_consume_local]
        exact hUmem
      · intro q qv hQv
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          (smt_value_rel_re_concat_consume_local
            (RuleProofs.smt_value_rel_refl (SmtValue.RegLan qv))
            (StrInReConsumeInternal.smt_value_rel_inter_right_all_consume_local rvX))]
        exact hQ q qv hQv
  rotate_left
  · -- generic concat head: wf forces a non-concat chunk; compose the
    -- head's rev_comp conclusions with the tail residual.
    intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
      hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
      ihResidual
    exact StrInReConsumeInternal.str_re_consume_rec_unrev_str_concat_re_concat_from_ih_local
      M hM s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
      hR1Allchar hFuelMult hR1Mult ihLeft ihResidual
  · -- union combinator: branch dispatch via rev_comp distribution.
    intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight
    exact StrInReConsumeInternal.str_re_consume_union_unrev_from_ih_local M hM s c1 c2 fuel
      hS hFuel hC2Ne ihLeft ihRight
  · -- inter combinator: branch dispatch via rev_comp distribution.
    intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight
    exact StrInReConsumeInternal.str_re_consume_inter_unrev_from_ih_local M hM s c1 c2 fuel
      hS hFuel hC2Ne ihRight ihLeft

theorem StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive M s0 r0 fuel0 :=
  fun s0 r0 fuel0 =>
    (StrInReConsumeInternal.str_re_consume_rec_unrev_semantic_local M hM s0 r0 fuel0).1

theorem StrInReConsumeInternal.str_re_consume_rec_unrev_residual_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_unrev_residual_motive M s0 r0 fuel0 :=
  fun s0 r0 fuel0 =>
    (StrInReConsumeInternal.str_re_consume_rec_unrev_semantic_local M hM s0 r0 fuel0).2

theorem StrInReConsumeInternal.consume_unrev_pair_eval_local
    (M : SmtModel) (a b : Term) (ssA : SmtSeq) (rvB : SmtRegLan)
    (hA :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local a)) =
        SmtValue.Seq ssA)
    (hB :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local b)) =
        SmtValue.RegLan rvB)
    (hSsATy : __smtx_typeof_value (SmtValue.Seq ssA) =
      SmtType.Seq SmtType.Char) :
    __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local a b)) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ssA) rvB) := by
  simp only [StrInReConsumeInternal.consume_unrev_pair_local]
  change __smtx_model_eval M
      (SmtTerm.str_in_re
        (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local a))
        (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local b))) = _
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hA, hB,
    model_str_in_re_unpack_eq_string_of_value_type ssA rvB hSsATy]

theorem StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local
    (M : SmtModel) (hM : model_wf M) (s : Term)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNe : StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck) :
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ss ∧
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
  have hNe' : __eo_list_rev (Term.UOp UserOp.str_concat) s ≠
      Term.Stuck := by
    simpa [StrInReConsumeInternal.consume_unrev_str_local] using hNe
  have hUnrevTy :
      __smtx_typeof (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtType.Seq SmtType.Char := by
    simp only [StrInReConsumeInternal.consume_unrev_str_local]
    exact smt_typeof_list_rev_str_concat_of_seq s SmtType.Char
      (eo_list_rev_is_list_true_of_ne_stuck _ _ hNe') hTy hNe'
  rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM _
      hUnrevTy with ⟨ss, hEval⟩
  refine ⟨ss, hEval, ?_⟩
  exact StrInReConsumeInternal.typed_seq_value_of_eval_local M hM _ ss
    hUnrevTy hEval

theorem StrInReConsumeInternal.consume_unrev_str_value_type_of_eval_local
    (M : SmtModel) (hM : model_wf M) (s : Term) (ss : SmtSeq)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNe : StrInReConsumeInternal.consume_unrev_str_local s ≠ Term.Stuck)
    (hEval : __smtx_model_eval M
      (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtValue.Seq ss) :
    __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char := by
  have hNe' : __eo_list_rev (Term.UOp UserOp.str_concat) s ≠
      Term.Stuck := by
    simpa [StrInReConsumeInternal.consume_unrev_str_local] using hNe
  have hUnrevTy :
      __smtx_typeof
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_str_local s)) =
        SmtType.Seq SmtType.Char := by
    simp only [StrInReConsumeInternal.consume_unrev_str_local]
    exact smt_typeof_list_rev_str_concat_of_seq s SmtType.Char
      (eo_list_rev_is_list_true_of_ne_stuck _ _ hNe') hTy hNe'
  exact StrInReConsumeInternal.typed_seq_value_of_eval_local M hM _ ss
    hUnrevTy hEval

/--
The `re_mult`-tail equality for the model relation's left-false branch:
if the star body admits no suffix of `w`, the star factor contributes
only `ε`.
-/
theorem StrInReConsumeInternal.consume_mult_left_false_tail_eq_local
    (w : native_String) (A B : SmtRegLan)
    (hNoSufB :
      ∀ pre suf : native_String,
        pre ++ suf = w -> native_str_in_re suf B = false) :
    native_str_in_re w (native_re_concat A (native_re_mult B)) =
      native_str_in_re w A := by
  cases hWV : native_string_valid w with
  | false =>
      have h1 : native_str_in_re w
          (native_re_concat A (native_re_mult B)) = false := by
        simp [native_str_in_re, hWV]
      have h2 : native_str_in_re w A = false := by
        simp [native_str_in_re, hWV]
      rw [h1, h2]
  | true =>
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hMem
        have hListMem :
            nativeListInRe w
                (native_re_mk_concat A (native_re_mult B)) = true := by
          simpa [native_str_in_re, nativeListInRe, hWV] using hMem
        rcases (nativeListInRe_mk_concat_true_iff_exists_append w A
            _).1 hListMem with ⟨x, y, hSplit, hXm, hYm⟩
        have hXValid : native_string_valid x = true :=
          StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hYValid : native_string_valid y = true :=
          StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
            rw [hSplit]
            exact hWV)
        have hXStr : native_str_in_re x A = true := by
          simpa [native_str_in_re, hXValid] using hXm
        have hYStr : native_str_in_re y (native_re_mult B) = true := by
          simpa [native_str_in_re, hYValid] using hYm
        by_cases hYNil : y = []
        · subst hYNil
          rw [show w = x from by
            rw [← hSplit]
            simp]
          exact hXStr
        · exfalso
          rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local y B
              hYStr hYNil with ⟨y1, yk, hYSplit, _hYkNe, _hY1Mem,
                hYkMem⟩
          have hBad := hNoSufB (x ++ y1) yk (by
            rw [List.append_assoc, hYSplit, hSplit])
          rw [hBad] at hYkMem
          cases hYkMem
      · intro hMem
        have h := native_str_in_re_re_concat_intro w [] A
          (native_re_mult B) hMem
          (native_str_in_re_re_mult_empty_local B)
        simpa using h

/--
The retry-step equality for the model relation's `re_mult` retry
branch: trimming one consumed star chunk off the end preserves
membership in `A · B*` (given the tail chain admits no suffix of the
whole word and the body residual ∀q equality).
-/
theorem StrInReConsumeInternal.consume_mult_retry_step_eq_local
    (M : SmtModel) (w5 u : native_String)
    (A B : SmtRegLan) (r2t multt : Term)
    (hAEval :
      __smtx_model_eval M (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t)) =
        SmtValue.RegLan A)
    (hMultEval :
      __smtx_model_eval M (__eo_to_smt multt) =
        SmtValue.RegLan (native_re_mult B))
    (hNoSufA :
      ∀ pre suf : native_String,
        pre ++ suf = w5 ++ u -> native_str_in_re suf A = false)
    (hU : native_str_in_re u B = true)
    (hQ1 :
      ∀ q qv,
        __smtx_model_eval M (__eo_to_smt q) = SmtValue.RegLan qv ->
          native_str_in_re (w5 ++ u) (native_re_concat qv B) =
            native_str_in_re w5 qv) :
    native_str_in_re (w5 ++ u)
        (native_re_concat A (native_re_mult B)) =
      native_str_in_re w5
        (native_re_concat A (native_re_mult B)) := by
  have hQEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (StrInReConsumeInternal.consume_unrev_re_local r2t))
              multt)) =
        SmtValue.RegLan
          (native_re_concat A (native_re_mult B)) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (__eo_to_smt (StrInReConsumeInternal.consume_unrev_re_local r2t))
          (__eo_to_smt multt)) = _
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hAEval,
      hMultEval]
  have hEq := hQ1 _ _ hQEval
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    have hWuValid : native_string_valid (w5 ++ u) = true := by
      cases h : native_string_valid (w5 ++ u) with
      | true => rfl
      | false => simp [native_str_in_re, h] at hMem
    have hListMem :
        nativeListInRe (w5 ++ u)
            (native_re_mk_concat A (native_re_mult B)) = true := by
      simpa [native_str_in_re, nativeListInRe, hWuValid] using hMem
    rcases (nativeListInRe_mk_concat_true_iff_exists_append _ A
        _).1 hListMem with ⟨x, y, hSplit, hXm, hYm⟩
    have hXValid : native_string_valid x = true :=
      StrInReConsumeInternal.native_string_valid_prefix_consume_local x y (by
        rw [hSplit]
        exact hWuValid)
    have hYValid : native_string_valid y = true :=
      StrInReConsumeInternal.native_string_valid_suffix_consume_local x y (by
        rw [hSplit]
        exact hWuValid)
    have hXStr : native_str_in_re x A = true := by
      simpa [native_str_in_re, hXValid] using hXm
    have hYStr : native_str_in_re y (native_re_mult B) = true := by
      simpa [native_str_in_re, hYValid] using hYm
    by_cases hYNil : y = []
    · exfalso
      subst hYNil
      have hBad := hNoSufA [] (w5 ++ u) (by simp)
      rw [show w5 ++ u = x from by
        rw [← hSplit]
        simp] at hBad
      rw [hBad] at hXStr
      cases hXStr
    · rcases StrInReConsumeInternal.native_str_in_re_star_nonempty_suffix_full_local y B
          hYStr hYNil with ⟨y1, yk, hYSplit, _hYkNe, hY1Mem, hYkMem⟩
      have hLhs :
          native_str_in_re (w5 ++ u)
              (native_re_concat
                (native_re_concat A (native_re_mult B)) B) = true := by
        rw [show w5 ++ u = (x ++ y1) ++ yk from by
          rw [List.append_assoc, hYSplit, hSplit]]
        refine native_str_in_re_re_concat_intro (x ++ y1) yk _ _ ?_
          hYkMem
        exact native_str_in_re_re_concat_intro x y1 _ _ hXStr hY1Mem
      rw [hEq] at hLhs
      exact hLhs
  · intro hMem
    have hAbsorb := StrInReConsumeInternal.native_str_in_re_concat_star_absorb_local w5 u A B
      hMem hU
    exact hAbsorb

theorem StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_local
    (M : SmtModel) (hM : model_wf M) :
    ∀ s0 r0 fuel0,
      StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_motive M s0 r0 fuel0 := by
  intro s0 r0 fuel0
  refine __str_re_consume_rec.induct
    (fun _ _ _ => True)
    (StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_motive M)
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
    intro side hSTy
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hSTy
    cases hSTy
  -- rec: r stuck
  · intro s fuel hS
    intro side _hSTy hRTy
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
      TranslationProofs.smtx_typeof_none] at hRTy
    cases hRTy
  -- rec: fuel stuck
  · intro s r hS hR
    intro side _hSTy _hRTy hSide hSideNe
    exfalso
    exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
      hSideNe
  -- eq_4: eps head, concat string
  · intro s1 s2 r2 fuel hFuel ih
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        StrInReConsumeInternal.re_empty_string_re_consume_local r2 hRTy).2
    have hSide' :
        side =
          __str_re_consume_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
              s2) r2 fuel :=
      hSide.trans
        (str_re_consume_rec_re_concat_empty_left_eq _ r2 fuel (by
          intro h
          cases h) hFuel)
    rcases StrInReConsumeInternal.eval_unrev_re_concat_empty_left_bridge_local M r2 rvU
        hRvU with ⟨rvU2, hRvU2, hRel⟩
    rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
    have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
      hSsUTy
    have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU2 hSsU hRvU2
      hSsUTy
    have hStep :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (StrInReConsumeInternal.consume_unrev_pair_local
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    StrInReConsumeInternal.re_empty_string_re_consume_local) r2))))
          (__smtx_model_eval M
            (__eo_to_smt
              (StrInReConsumeInternal.consume_unrev_pair_local
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                r2))) := by
      rw [hL, hR]
      rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hRel]
      exact RuleProofs.smt_value_rel_refl _
    exact RuleProofs.smt_value_rel_trans _ _ _ hStep
      (ih side hSTy hR2Ty hSide' hSideNe hSideNotFalse hMemNe
        hUnrevNe ⟨rvU2, hRvU2⟩
        (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2)
  -- eq_5: str_to_re head
  · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.str_to_re) s3) r2 hRTy).2
    rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel]
      at hSide
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hEqT | hEqF
    · -- s1 = s3: the head consumes the exact word of s1
      have hS1Eq : s1 = s3 := (eq_of_eo_eq_true s1 s3 hEqT).symm
      subst hS1Eq
      have hSide' : side = __str_re_consume_rec s2 r2 fuel := by
        rw [hSide, hEqT, eo_ite_true]
      rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
      have hSsU' := hSsU
      simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU'
      rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M s1 s2 ssU
          hSsU' with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
      have hCompEval :
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp
                  (Term.Apply (Term.UOp UserOp.str_to_re) s1))) =
            SmtValue.RegLan
              (native_str_to_re (native_unpack_string s1V)) := by
        rw [show __re_rev_comp
            (Term.Apply (Term.UOp UserOp.str_to_re) s1) =
            Term.Apply (Term.UOp UserOp.str_to_re) s1 from rfl]
        change __smtx_model_eval M
            (SmtTerm.str_to_re (__eo_to_smt s1)) = _
        simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1V,
          StrInReConsumeInternal.typed_seq_unpack_values_of_eval_local
            M hM s1 s1V hS1Ty hS1V]
      rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
          hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
      have hS1ValTy :
          __smtx_typeof_value (SmtValue.Seq s1V) =
            SmtType.Seq SmtType.Char := by
        have h := smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt s1) (by
            unfold term_has_non_none_type
            rw [hS1Ty]
            simp)
        rw [hS1V, hS1Ty] at h
        exact h
      have hW1Valid :
          native_string_valid (native_unpack_string s1V) = true :=
        native_unpack_string_valid_of_typeof_seq_char hS1ValTy
      have hUnrevNe2 := StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local s1 s2
        hUnrevNe
      have hSsU2Ty :=
        StrInReConsumeInternal.consume_unrev_str_value_type_of_eval_local
          M hM s2 ssU2 hS2Ty hUnrevNe2 (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact hSsU2)
      have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
        hSsUTy
      have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M s2 r2 ssU2 rvU2 (by
        simp only [StrInReConsumeInternal.consume_unrev_str_local]
        exact hSsU2) hRvU2 hSsU2Ty
      have hStep :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.Apply (Term.UOp UserOp.str_to_re) s1))
                    r2))))
            (__smtx_model_eval M
              (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local s2 r2))) := by
        rw [hL, hR]
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          hRvURel]
        rw [hUnp]
        rw [StrInReConsumeInternal.native_str_in_re_snoc_word_eq_consume_local
          (native_unpack_string ssU2) (native_unpack_string s1V)
          rvU2 hW1Valid]
        exact RuleProofs.smt_value_rel_refl _
      exact RuleProofs.smt_value_rel_trans _ _ _ hStep
        (ih side hS2Ty hR2Ty hSide' hSideNe hSideNotFalse hMemNe
          hUnrevNe2 ⟨rvU2, hRvU2⟩
          (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2)
    · rw [hEqF] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hLenT | hLenF
      · exfalso
        rw [hLenT] at hSide
        simp only [eo_ite_true] at hSide
        exact hSideNotFalse hSide
      · rw [hLenF] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide]
        exact RuleProofs.smt_value_rel_refl _
  -- eq_6: range head
  · intro s1 s2 s3 s5 r2 fuel hFuel ih
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hRangeTy :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
        r2 hRTy).1
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5)
        r2 hRTy).2
    have hRangeArgs :
        __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char ∧
          __smtx_typeof (__eo_to_smt s5) = SmtType.Seq SmtType.Char := by
      have hNN : term_has_non_none_type
          (SmtTerm.re_range (__eo_to_smt s3) (__eo_to_smt s5)) := by
        unfold term_has_non_none_type
        change __smtx_typeof
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_range) s3) s5)) ≠
          SmtType.None
        rw [hRangeTy]
        simp
      exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
        (typeof_re_range_eq (__eo_to_smt s3) (__eo_to_smt s5)) hNN
    rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel] at hSide
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hLenT | hLenF
    · rcases eo_and_eq_true_local _ _ hLenT with ⟨hS1Len, hRangeLens⟩
      rcases eo_and_eq_true_local _ _ hRangeLens with ⟨hS3Len, hS5Len⟩
      rcases str_re_consume_string_singleton_of_seq_type_len_one s1
          hS1Ty hS1Len with ⟨c, rfl⟩
      rcases str_re_consume_string_singleton_of_seq_type_len_one s3
          hRangeArgs.1 hS3Len with ⟨lo, rfl⟩
      rcases str_re_consume_string_singleton_of_seq_type_len_one s5
          hRangeArgs.2 hS5Len with ⟨hi, rfl⟩
      rw [hLenT] at hSide
      simp only [eo_ite_true] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hMatchT | hMatchF
      · -- head matched
        have hSide' : side = __str_re_consume_rec s2 r2 fuel := by
          rw [hSide, hMatchT, eo_ite_true]
        have hCValidString : native_string_valid [c] = true :=
          native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
        have hLen1 :
            ∀ x : native_String,
              nativeListInRe x (native_re_range [lo] [hi]) = true ->
                x.length = 1 := by
          intro x hx
          exact StrInReConsumeInternal.nativeListInRe_range_length_one_consume_local x lo hi
            (by simpa [native_re_range] using hx)
        have hCin :
            native_str_in_re [c] (native_re_range [lo] [hi]) = true :=
          str_re_consume_range_head_native_eq_of_match_local M hM
            c lo hi true hCValidString hRangeTy hMatchT
        rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
            hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
        have hSsU' := hSsU
        simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU'
        rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
            hSsU' with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
        rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
          ⟨ss1', hss1', hUnp1⟩
        injection hS1V.symm.trans hss1' with hEq1
        have hS1W : native_unpack_string s1V = [c] := by
          rw [hEq1]
          exact hUnp1
        have hCompEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_comp
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_range)
                        (Term.String [lo]))
                      (Term.String [hi])))) =
              SmtValue.RegLan (native_re_range [lo] [hi]) := by
          change __smtx_model_eval M
              (SmtTerm.re_range (SmtTerm.String [lo])
                (SmtTerm.String [hi])) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_range,
           ]
        rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
            hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
        have hUnrevNe2 := StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local _ s2
          hUnrevNe
        have hSsU2Ty :=
          StrInReConsumeInternal.consume_unrev_str_value_type_of_eval_local
            M hM s2 ssU2 hS2Ty hUnrevNe2 (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact hSsU2)
        have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU
          hRvU hSsUTy
        have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M s2 r2 ssU2 rvU2 (by
          simp only [StrInReConsumeInternal.consume_unrev_str_local]
          exact hSsU2) hRvU2 hSsU2Ty
        have hStep :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_pair_local
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat)
                        (Term.String [c])) s2)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_range)
                            (Term.String [lo]))
                          (Term.String [hi])))
                      r2))))
              (__smtx_model_eval M
                (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local s2 r2))) := by
          rw [hL, hR]
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel]
          rw [hUnp, hS1W]
          rw [StrInReConsumeInternal.native_str_in_re_snoc_len_one_eq_consume_local
            (native_unpack_string ssU2) [c] rvU2
            (native_re_range [lo] [hi]) hLen1 rfl hCin]
          exact RuleProofs.smt_value_rel_refl _
        exact RuleProofs.smt_value_rel_trans _ _ _ hStep
          (ih side hS2Ty hR2Ty hSide' hSideNe hSideNotFalse hMemNe
            hUnrevNe2 ⟨rvU2, hRvU2⟩
            (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2)
      · exfalso
        rw [hMatchF] at hSide
        simp only [eo_ite_false] at hSide
        exact hSideNotFalse hSide
    · rw [hLenF] at hSide
      simp only [eo_ite_false] at hSide
      rw [hSide]
      exact RuleProofs.smt_value_rel_refl _
  -- eq_7: allchar head
  · intro s1 s2 r2 fuel hFuel ih
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hS1Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).1
    have hS2Ty :=
      (str_concat_args_of_seq_type s1 s2 SmtType.Char hSTy).2
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.UOp UserOp.re_allchar) r2 hRTy).2
    rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] at hSide
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hCondT | hCondF
    · rcases str_re_consume_string_singleton_of_seq_type_len_one s1
          hS1Ty hCondT with ⟨c, rfl⟩
      have hSide' : side = __str_re_consume_rec s2 r2 fuel := by
        rw [hSide, hCondT, eo_ite_true]
      have hS1Valid : native_string_valid [c] = true :=
        native_string_valid_of_smtx_typeof_eo_string [c] hS1Ty
      have hCValid : native_char_valid c = true := by
        simpa [native_string_valid] using hS1Valid
      have hLen1 :
          ∀ x : native_String,
            nativeListInRe x native_re_allchar = true ->
              x.length = 1 :=
        fun x hx => ((nativeListInRe_allchar_true_iff x).1 hx).1
      have hCin :
          native_str_in_re [c] native_re_allchar = true := by
        have hL := (nativeListInRe_allchar_true_iff [c]).2
          ⟨rfl, by simp [hCValid]⟩
        simpa [native_str_in_re, native_string_valid, hCValid,
          nativeListInRe] using hL
      rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
      have hSsU' := hSsU
      simp only [StrInReConsumeInternal.consume_unrev_str_local] at hSsU'
      rcases StrInReConsumeInternal.eval_list_rev_snoc_view_consume_local M _ s2 ssU
          hSsU' with ⟨ssU2, s1V, hSsU2, hS1V, hUnp⟩
      rcases StrInReConsumeInternal.eval_string_unpack_consume_local M [c] with
        ⟨ss1', hss1', hUnp1⟩
      injection hS1V.symm.trans hss1' with hEq1
      have hS1W : native_unpack_string s1V = [c] := by
        rw [hEq1]
        exact hUnp1
      have hCompEval :
          __smtx_model_eval M
              (__eo_to_smt
                (__re_rev_comp (Term.UOp UserOp.re_allchar))) =
            SmtValue.RegLan native_re_allchar := by
        change __smtx_model_eval M SmtTerm.re_allchar = _
        simp [__smtx_model_eval]
      rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_local M _ r2 rvU _
          hCompEval hRvU with ⟨rvU2, hRvU2, hRvURel⟩
      have hUnrevNe2 := StrInReConsumeInternal.consume_unrev_str_tail_ne_stuck_local _ s2
        hUnrevNe
      have hSsU2Ty :=
        StrInReConsumeInternal.consume_unrev_str_value_type_of_eval_local
          M hM s2 ssU2 hS2Ty hUnrevNe2 (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact hSsU2)
      have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
        hSsUTy
      have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M s2 r2 ssU2 rvU2 (by
        simp only [StrInReConsumeInternal.consume_unrev_str_local]
        exact hSsU2) hRvU2 hSsU2Ty
      have hStep :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat)
                      (Term.String [c])) s2)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.UOp UserOp.re_allchar))
                    r2))))
            (__smtx_model_eval M
              (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local s2 r2))) := by
        rw [hL, hR]
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          hRvURel]
        rw [hUnp, hS1W]
        rw [StrInReConsumeInternal.native_str_in_re_snoc_len_one_eq_consume_local
          (native_unpack_string ssU2) [c] rvU2 native_re_allchar
          hLen1 rfl hCin]
        exact RuleProofs.smt_value_rel_refl _
      exact RuleProofs.smt_value_rel_trans _ _ _ hStep
        (ih side hS2Ty hR2Ty hSide' hSideNe hSideNotFalse hMemNe
          hUnrevNe2 ⟨rvU2, hRvU2⟩
          (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2)
    · rw [hCondF] at hSide
      simp only [eo_ite_false] at hSide
      rw [hSide]
      exact RuleProofs.smt_value_rel_refl _
  -- eq_8: re_mult head with concat fuel
  · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
      ihLeft ihRight _ihLeftAgain ihResidual
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hStarTy :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 hRTy).1
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 hRTy).2
    have hR3Ty :=
      RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
        r3 hStarTy
    have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
    have hWfR3 : StrInReConsumeInternal.consume_wf_chain_local r3 :=
      StrInReConsumeInternal.consume_wf_chain_mult_body_local hWfParts.1
    have hWfR2 := hWfParts.2
    rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM
        (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 rvU hStarTy
        hRvU with ⟨rvU2, headV, hCompEval, hRvU2, hRvURel0⟩
    rcases StrInReConsumeInternal.re_rev_comp_mult_decomp_local M hM r3 headV hStarTy
        hCompEval with ⟨v3B, hV3Eval, hHeadVEq⟩
    subst hHeadVEq
    rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
    have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
      hSsUTy
    rw [__str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr] at hSide
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hC1T | hC1F
    · -- star-body consume failed: side is the tail consume result
      rw [hC1T] at hSide
      simp only [eo_ite_true] at hSide
      have hLeftF :
          __str_re_consume_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                s1) s2) r3
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
                fc) fr) = Term.Boolean false :=
        (eq_of_eo_eq_true _ _ hC1T).symm
      rcases (StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_local M hM _ _ _
          (Term.Boolean false) hSTy hR3Ty hLeftF.symm rfl hWfR3 ssU
          hSsU).1 v3B hV3Eval with ⟨_hNeB, hSufB⟩
      have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ r2 ssU rvU2 hSsU
        hRvU2 hSsUTy
      have hStep :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.Apply (Term.UOp UserOp.re_mult) r3))
                    r2))))
            (__smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r2))) := by
        rw [hL, hR]
        rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
          hRvURel0]
        rw [StrInReConsumeInternal.consume_mult_left_false_tail_eq_local
          (native_unpack_string ssU) rvU2 v3B hSufB]
        exact RuleProofs.smt_value_rel_refl _
      exact RuleProofs.smt_value_rel_trans _ _ _ hStep
        (ihRight side hSTy hR2Ty hSide hSideNe hSideNotFalse hMemNe
          hUnrevNe ⟨rvU2, hRvU2⟩ hWfR2)
    · rw [hC1F] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hC2T | hC2F
      · rw [hC2T] at hSide
        simp only [eo_ite_true] at hSide
        rcases eo_ite_cases_of_ne_stuck _ _ _
            (by
              rw [← hSide]
              exact hSideNe) with hC3T | hC3F
        · rw [hC3T] at hSide
          simp only [eo_ite_true] at hSide
          rcases eo_ite_cases_of_ne_stuck _ _ _
              (by
                rw [← hSide]
                exact hSideNe) with hC4T | hC4F
          · -- rebuilt fallback
            rw [hC4T] at hSide
            simp only [eo_ite_true] at hSide
            rw [hSide]
            exact RuleProofs.smt_value_rel_refl _
          · -- retry on the residual string
            rw [hC4F] at hSide
            simp only [eo_ite_false] at hSide
            have hMemEpsL :
                __str_membership_re
                    (__str_re_consume_rec
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat)
                          s1) s2) r3
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat)
                          fc) fr)) =
                  StrInReConsumeInternal.re_empty_string_re_consume_local :=
              (eq_of_eo_eq_true _ _ hC2T).symm
            have hRightF :=
              eq_of_eo_is_eq_true_consume_local _ _ hC3T
            rcases StrInReConsumeInternal.str_re_consume_rec_unrev_residual_local M hM _ _ _
                _ hSTy hR3Ty rfl hMemEpsL hUnrevNe hWfR3 with
              ⟨hMemTyRawL, hMemTyL, hRestL⟩
            have hMemTransNeL :
                StrInReConsumeInternal.consume_unrev_str_local
                    (__str_membership_str
                      (__str_re_consume_rec
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            s1) s2) r3
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            fc) fr))) ≠ Term.Stuck := by
              intro hBad
              rw [hBad] at hMemTyL
              rw [show __eo_to_smt Term.Stuck = SmtTerm.None from
                rfl] at hMemTyL
              rw [TranslationProofs.smtx_typeof_none] at hMemTyL
              cases hMemTyL
            rcases
              smt_eval_seq_char_of_smt_type_seq_char_consume_local
                M hM _ hMemTyL with ⟨ssR', hSsR'⟩
            have hSsR'Ty :=
              StrInReConsumeInternal.typed_seq_value_of_eval_local
                M hM _ ssR' hMemTyL hSsR'
            rcases hRestL ssU ssR' hSsU hSsR' with ⟨hChainL, _⟩
            rcases hChainL v3B hV3Eval with
              ⟨⟨u, hUdec, hUmem⟩, hQ1⟩
            rcases (StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_local M hM _
                _ _ (Term.Boolean false) hSTy hR2Ty hRightF.symm rfl
                hWfR2 ssU hSsU).1 rvU2 hRvU2 with ⟨_hNeA, hSufA⟩
            have hNoSufA' :
                ∀ p s : native_String,
                  p ++ s = native_unpack_string ssR' ++ u ->
                    native_str_in_re s rvU2 = false := by
              intro p s hps
              exact hSufA p s (by
                rw [hUdec]
                exact hps)
            have hQ1' :
                ∀ q0 qv0,
                  __smtx_model_eval M (__eo_to_smt q0) =
                    SmtValue.RegLan qv0 ->
                    native_str_in_re
                        (native_unpack_string ssR' ++ u)
                        (native_re_concat qv0 v3B) =
                      native_str_in_re (native_unpack_string ssR')
                        qv0 := by
              intro q0 qv0 hq0
              have h := hQ1 q0 qv0 hq0
              rw [hUdec] at h
              exact h
            have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssR' rvU
              hSsR' hRvU hSsR'Ty
            have hStep :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (StrInReConsumeInternal.consume_unrev_pair_local
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            s1) s2)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_concat)
                            (Term.Apply (Term.UOp UserOp.re_mult)
                              r3))
                          r2))))
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (StrInReConsumeInternal.consume_unrev_pair_local
                        (__str_membership_str
                          (__str_re_consume_rec
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp.str_concat) s1) s2)
                            r3
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp.str_concat) fc)
                              fr)))
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.re_concat)
                            (Term.Apply (Term.UOp UserOp.re_mult)
                              r3))
                          r2)))) := by
              rw [hL, hR]
              rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                hRvURel0 (native_unpack_string ssU)]
              rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
                hRvURel0 (native_unpack_string ssR')]
              rw [hUdec]
              rw [StrInReConsumeInternal.consume_mult_retry_step_eq_local M
                (native_unpack_string ssR') u rvU2 v3B r2
                (__re_rev_comp
                  (Term.Apply (Term.UOp UserOp.re_mult) r3))
                hRvU2 hCompEval hNoSufA' hUmem hQ1']
              exact RuleProofs.smt_value_rel_refl _
            exact RuleProofs.smt_value_rel_trans _ _ _ hStep
              (ihResidual side hMemTyRawL hRTy hSide hSideNe
                hSideNotFalse hMemNe hMemTransNeL ⟨rvU, hRvU⟩ hWf)
        · rw [hC3F] at hSide
          simp only [eo_ite_false] at hSide
          rw [hSide]
          exact RuleProofs.smt_value_rel_refl _
      · rw [hC2F] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide]
        exact RuleProofs.smt_value_rel_refl _
  -- eq_9: re_mult head, non-concat fuel
  · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    intro side _hSTy _hRTy hSide _hSideNe _hSideNotFalse _hMemNe
      _hUnrevNe _hEx _hWf
    have hEq :=
      str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
        s1 s2 r3 r2 fuel hFuel hNotFuelConcat
    rw [hSide.trans hEq]
    exact RuleProofs.smt_value_rel_refl _
  -- eq_10: generic concat head
  · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
      hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
      ihResidual
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hR1Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).1
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2 hRTy).2
    have hWfParts := StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf
    have hR1NotConcat : ∀ a b,
        r1 = Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b ->
          False := by
      intro a b hEq
      rw [hEq] at hWfParts
      have hBad := hWfParts.1
      simpa [StrInReConsumeInternal.consume_wf_chunk_local, StrInReConsumeInternal.consume_wf_local] using hBad
    have hWfR1 : StrInReConsumeInternal.consume_wf_chain_local r1 :=
      StrInReConsumeInternal.consume_wf_chain_of_chunk_local hR1NotConcat hWfParts.1
    rcases StrInReConsumeInternal.eval_unrev_re_concat_head_bridge_exists_local M hM r1 r2
        rvU hR1Ty hRvU with ⟨rvU2, headV, hCompEval, hRvU2, hRvURel⟩
    rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
    have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
      hSsUTy
    rw [__str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
      hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult]
      at hSide
    rcases eo_ite_cases_of_ne_stuck _ _ _
        (by
          rw [← hSide]
          exact hSideNe) with hLF | hLNF
    · exfalso
      rw [hLF] at hSide
      simp only [eo_ite_true] at hSide
      exact hSideNotFalse hSide
    · rw [hLNF] at hSide
      simp only [eo_ite_false] at hSide
      rcases eo_ite_cases_of_ne_stuck _ _ _
          (by
            rw [← hSide]
            exact hSideNe) with hME | hMNE
      · -- head fully consumed: recurse on the residual string
        rw [hME] at hSide
        simp only [eo_ite_true] at hSide
        have hMemEpsEq :
            __str_membership_re
                (__str_re_consume_rec
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
                  r1 fuel) =
              StrInReConsumeInternal.re_empty_string_re_consume_local :=
          eq_of_eo_is_eq_true_consume_local _ _ hME
        rcases StrInReConsumeInternal.str_re_consume_rec_unrev_residual_local M hM _ _ _ _
            hSTy hR1Ty rfl hMemEpsEq hUnrevNe hWfR1 with
          ⟨hMemTyRaw, hMemTy, hRestL⟩
        have hMemTransNe :
            StrInReConsumeInternal.consume_unrev_str_local
                (__str_membership_str
                  (__str_re_consume_rec
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) s1)
                      s2) r1 fuel)) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hMemTy
          rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl]
            at hMemTy
          rw [TranslationProofs.smtx_typeof_none] at hMemTy
          cases hMemTy
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local
            M hM _ hMemTy with ⟨ssR', hSsR'⟩
        have hSsR'Ty :=
          StrInReConsumeInternal.typed_seq_value_of_eval_local
            M hM _ ssR' hMemTy hSsR'
        rcases hRestL ssU ssR' hSsU hSsR' with ⟨_hChainL, hCompVer⟩
        rcases hCompVer hR1NotConcat headV hCompEval with
          ⟨⟨u, hUdec, hUmem⟩, hQ⟩
        have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ r2 ssR' rvU2
          hSsR' hRvU2 hSsR'Ty
        have hStep :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_pair_local
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_concat) s1)
                      s2)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.re_concat) r1)
                      r2))))
              (__smtx_model_eval M
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_pair_local
                    (__str_membership_str
                      (__str_re_consume_rec
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_concat)
                            s1) s2) r1 fuel))
                    r2))) := by
          rw [hL, hR]
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local
            hRvURel]
          rw [hQ _ rvU2 hRvU2]
          exact RuleProofs.smt_value_rel_refl _
        exact RuleProofs.smt_value_rel_trans _ _ _ hStep
          (ihResidual side hMemTyRaw hR2Ty hSide hSideNe
            hSideNotFalse hMemNe hMemTransNe ⟨rvU2, hRvU2⟩
            hWfParts.2)
      · rw [hMNE] at hSide
        simp only [eo_ite_false] at hSide
        rw [hSide]
        exact RuleProofs.smt_value_rel_refl _
  -- eq_11: eps head, non-concat string
  · intro s r fuel hS hFuel _hNotConcat ih
    intro side hSTy hRTy hSide hSideNe hSideNotFalse hMemNe hUnrevNe
      hEx hWf
    rcases hEx with ⟨rvU, hRvU⟩
    have hR2Ty :=
      (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
        StrInReConsumeInternal.re_empty_string_re_consume_local r hRTy).2
    have hSide' : side = __str_re_consume_rec s r fuel :=
      hSide.trans
        (str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel)
    rcases StrInReConsumeInternal.eval_unrev_re_concat_empty_left_bridge_local M r rvU
        hRvU with ⟨rvU2, hRvU2, hRel⟩
    rcases StrInReConsumeInternal.consume_unrev_str_eval_of_ne_stuck_local M hM _ hSTy
        hUnrevNe with ⟨ssU, hSsU, hSsUTy⟩
    have hL := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU hSsU hRvU
      hSsUTy
    have hR := StrInReConsumeInternal.consume_unrev_pair_eval_local M _ _ ssU rvU2 hSsU hRvU2
      hSsUTy
    have hStep :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (StrInReConsumeInternal.consume_unrev_pair_local s
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.re_concat)
                    StrInReConsumeInternal.re_empty_string_re_consume_local) r))))
          (__smtx_model_eval M
            (__eo_to_smt (StrInReConsumeInternal.consume_unrev_pair_local s r))) := by
      rw [hL, hR]
      rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hRel]
      exact RuleProofs.smt_value_rel_refl _
    exact RuleProofs.smt_value_rel_trans _ _ _ hStep
      (ih side hSTy hR2Ty hSide' hSideNe hSideNotFalse hMemNe
        hUnrevNe ⟨rvU2, hRvU2⟩
        (StrInReConsumeInternal.consume_wf_chain_concat_parts_local hWf).2)
  -- eq_12: inter dispatch — vacuous (the inter tree's unrev is stuck)
  · intro s r1 r2 fuel hS hFuel _ih
    intro side _hSTy _hRTy _hSide _hSideNe _hSideNotFalse _hMemNe
      _hUnrevNe hEx _hWf
    exfalso
    rcases hEx with ⟨rvU, hRvU⟩
    exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
      (by
        simp only [StrInReConsumeInternal.consume_unrev_re_local]
        exact StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
          (by
            intro h
            simp at h)
          (fun a b h => by simp at h))
  -- eq_13: union dispatch — vacuous
  · intro s r1 r2 fuel hS hFuel _ih
    intro side _hSTy _hRTy _hSide _hSideNe _hSideNotFalse _hMemNe
      _hUnrevNe hEx _hWf
    exfalso
    rcases hEx with ⟨rvU, hRvU⟩
    exact StrInReConsumeInternal.term_ne_stuck_of_eval_reglan_consume_local M _ _ hRvU
      (by
        simp only [StrInReConsumeInternal.consume_unrev_re_local]
        exact StrInReConsumeInternal.rev_map_rev_not_chain_stuck_consume_local _ _
          (by
            intro h
            simp at h)
          (fun a b h => by simp at h))
  -- default: rebuilt `str_in_re s r`
  · intro s r fuel hS hR hFuel hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
      hNotRConcatEmpty hNotRInter hNotRUnion
    intro side _hSTy _hRTy hSide _hSideNe _hSideNotFalse _hMemNe
      _hUnrevNe _hEx _hWf
    have hEq := str_re_consume_rec_default_eq s r fuel hS hR hFuel
      hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
      hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
      hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel
    rw [hSide.trans hEq]
    exact RuleProofs.smt_value_rel_refl _
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

end RuleProofs
