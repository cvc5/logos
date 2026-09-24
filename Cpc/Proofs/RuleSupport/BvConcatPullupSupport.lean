module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport
public import Cpc.Proofs.RuleSupport.BvNaryAndSupport
import all Cpc.Proofs.RuleSupport.BvNaryAndSupport
public import Cpc.Proofs.RuleSupport.BvNaryOrSupport
import all Cpc.Proofs.RuleSupport.BvNaryOrSupport
public import Cpc.Proofs.RuleSupport.BvNaryXorSupport
import all Cpc.Proofs.RuleSupport.BvNaryXorSupport
public import Cpc.Proofs.Rules.Bv_bitwise_slicing
public import Cpc.Proofs.RuleSupport.BvBitwiseElimSupport
import all Cpc.Proofs.RuleSupport.BvBitwiseElimSupport
import all Cpc.Logos

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

inductive BvConcatPullupOp where
  | band
  | bor
  | bxor
  deriving DecidableEq

def BvConcatPullupOp.term : BvConcatPullupOp → Term
  | .band => Term.UOp UserOp.bvand
  | .bor => Term.UOp UserOp.bvor
  | .bxor => Term.UOp UserOp.bvxor

def BvConcatPullupOp.apply
    (op : BvConcatPullupOp) (x y : Term) : Term :=
  Term.Apply (Term.Apply op.term x) y

def BvConcatPullupOp.eval : BvConcatPullupOp → SmtValue → SmtValue → SmtValue
  | .band => __smtx_model_eval_bvand
  | .bor => __smtx_model_eval_bvor
  | .bxor => __smtx_model_eval_bvxor

def bvConcatPullupExtract (x hi lo : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract hi lo) x

def bvConcatPullupConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y

def bvConcatPullupAggregate
    (op : BvConcatPullupOp) (xs ws : Term) : Term :=
  __eo_list_singleton_elim op.term (__eo_list_concat op.term xs ws)

def bvConcatPullup1Prem1Raw (nyRef yRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nyRef)
    (Term.Apply (Term.UOp UserOp._at_bvsize) yRef)

def bvConcatPullup1Prem2Raw
    (nxmRef zRef yRef ysRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nxmRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize)
        (bvConcatPullupConcat zRef (bvConcatPullupConcat yRef ysRef))))
      (Term.Numeral 1))

def bvConcatPullup1Prem3Raw (nymRef yRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nymRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) yRef))
      (Term.Numeral 1))

def bvConcatPullup1Prem1 (ny y : Term) : Term :=
  bvConcatPullup1Prem1Raw ny y

def bvConcatPullup1Prem2 (nxm z y ys : Term) : Term :=
  bvConcatPullup1Prem2Raw nxm z y ys

def bvConcatPullup1Prem3 (nym y : Term) : Term :=
  bvConcatPullup1Prem3Raw nym y

def bvConcatPullup1Program
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) : Term :=
  match op with
  | .band => __eo_prog_bv_and_concat_pullup xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
  | .bor => __eo_prog_bv_or_concat_pullup xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
  | .bxor => __eo_prog_bv_xor_concat_pullup xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def bvConcatPullup1ConcatZYs (z y ys : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) ys
    (bvConcatPullupConcat z (bvConcatPullupConcat y (Term.Binary 0 0)))

def bvConcatPullup1ConcatZs (z ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (__eo_list_concat (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0)))

def bvConcatPullup1Low
    (op : BvConcatPullupOp) (xs ws nym : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nym
    (Term.Numeral 0)

def bvConcatPullup1High
    (op : BvConcatPullupOp) (xs ws nxm ny : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nxm ny

def bvConcatPullup1Lhs
    (op : BvConcatPullupOp) (xs ws y z ys : Term) : Term :=
  __eo_list_concat op.term xs
    (op.apply (bvConcatPullup1ConcatZYs z y ys) ws)

def bvConcatPullup1Rhs
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) : Term :=
  bvConcatPullupConcat
    (op.apply (bvConcatPullup1High op xs ws nxm ny)
      (op.apply (bvConcatPullup1ConcatZs z ys)
        (__eo_nil op.term
          (__eo_typeof (bvConcatPullup1High op xs ws nxm ny)))))
    (bvConcatPullupConcat
      (op.apply (bvConcatPullup1Low op xs ws nym)
        (Term.Apply (Term.Apply op.term y)
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup1Low op xs ws nym)))))
      (Term.Binary 0 0))

def bvConcatPullup1Term
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvConcatPullup1Lhs op xs ws y z ys))
    (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)

def bvConcatPullup1LowRaw
    (op : BvConcatPullupOp) (xs ws nym : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nym (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullup1HighRaw
    (op : BvConcatPullupOp) (xs ws nxm ny : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nxm ny)
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullup1LhsRaw
    (op : BvConcatPullupOp) (xs ws y z ys : Term) : Term :=
  __eo_list_concat op.term xs
    (__eo_mk_apply
      (__eo_mk_apply op.term (bvConcatPullup1ConcatZYs z y ys)) ws)

def bvConcatPullup1RhsRaw
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) : Term :=
  let high := __eo_mk_apply
    (__eo_mk_apply op.term (bvConcatPullup1HighRaw op xs ws nxm ny))
    (__eo_mk_apply
      (__eo_mk_apply op.term (bvConcatPullup1ConcatZs z ys))
      (__eo_nil op.term
        (__eo_typeof (bvConcatPullup1HighRaw op xs ws nxm ny))))
  let low := __eo_mk_apply
    (__eo_mk_apply op.term (bvConcatPullup1LowRaw op xs ws nym))
    (__eo_mk_apply (Term.Apply op.term y)
      (__eo_nil op.term
        (__eo_typeof (bvConcatPullup1LowRaw op xs ws nym))))
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.concat) high)
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.concat) low)
      (Term.Binary 0 0))

def bvConcatPullup1BodyRaw
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (bvConcatPullup1LhsRaw op xs ws y z ys))
    (bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym)

private theorem pullup_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h |-
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h |-

private theorem pullup1_guard_refs
    {ny y nxm z ys nym nyRef yRef1 nxmRef zRef yRef2 ysRef
      nymRef yRef3 body : Term} :
    __eo_requires
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and (__eo_eq ny nyRef) (__eo_eq y yRef1))
                  (__eo_eq nxm nxmRef))
                (__eo_eq z zRef))
              (__eo_eq y yRef2))
            (__eo_eq ys ysRef))
          (__eo_eq nym nymRef))
        (__eo_eq y yRef3))
      (Term.Boolean true) body ≠ Term.Stuck ->
    nyRef = ny ∧ yRef1 = y ∧ nxmRef = nxm ∧ zRef = z ∧
      yRef2 = y ∧ ysRef = ys ∧ nymRef = nym ∧ yRef3 = y := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  rcases pullup_and_true hGuard with ⟨h7, hY3⟩
  rcases pullup_and_true h7 with ⟨h6, hNym⟩
  rcases pullup_and_true h6 with ⟨h5, hYs⟩
  rcases pullup_and_true h5 with ⟨h4, hY2⟩
  rcases pullup_and_true h4 with ⟨h3, hZ⟩
  rcases pullup_and_true h3 with ⟨h2, hNxm⟩
  rcases pullup_and_true h2 with ⟨hNy, hY1⟩
  exact ⟨support_eq_of_eo_eq_true ny nyRef hNy,
    support_eq_of_eo_eq_true y yRef1 hY1,
    support_eq_of_eo_eq_true nxm nxmRef hNxm,
    support_eq_of_eo_eq_true z zRef hZ,
    support_eq_of_eo_eq_true y yRef2 hY2,
    support_eq_of_eo_eq_true ys ysRef hYs,
    support_eq_of_eo_eq_true nym nymRef hNym,
    support_eq_of_eo_eq_true y yRef3 hY3⟩

private theorem bvConcatPullup1_premise_shape
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> ys ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    ny ≠ Term.Stuck -> nym ≠ Term.Stuck ->
    bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3 ≠
      Term.Stuck ->
    ∃ nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3,
      P1 = bvConcatPullup1Prem1Raw nyRef yRef1 ∧
      P2 = bvConcatPullup1Prem2Raw nxmRef zRef yRef2 ysRef ∧
      P3 = bvConcatPullup1Prem3Raw nymRef yRef3 := by
  intro hXs hWs hY hZ hYs hNxm hNy hNym hProg
  by_cases hShape :
      ∃ nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3,
        P1 = bvConcatPullup1Prem1Raw nyRef yRef1 ∧
        P2 = bvConcatPullup1Prem2Raw nxmRef zRef yRef2 ysRef ∧
        P3 = bvConcatPullup1Prem3Raw nymRef yRef3
  · exact hShape
  · exfalso
    apply hProg
    cases op with
    | band =>
        exact __eo_prog_bv_and_concat_pullup.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
              hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            exact hShape ⟨nyRef, yRef1, nxmRef, zRef, yRef2, ysRef,
              nymRef, yRef3, by simpa [bvConcatPullup1Prem1Raw] using hP1',
              by simpa [bvConcatPullup1Prem2Raw, bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup1Prem3Raw] using hP3'⟩)
    | bor =>
        exact __eo_prog_bv_or_concat_pullup.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
              hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            exact hShape ⟨nyRef, yRef1, nxmRef, zRef, yRef2, ysRef,
              nymRef, yRef3, by simpa [bvConcatPullup1Prem1Raw] using hP1',
              by simpa [bvConcatPullup1Prem2Raw, bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup1Prem3Raw] using hP3'⟩)
    | bxor =>
        exact __eo_prog_bv_xor_concat_pullup.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
              hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            exact hShape ⟨nyRef, yRef1, nxmRef, zRef, yRef2, ysRef,
              nymRef, yRef3, by simpa [bvConcatPullup1Prem1Raw] using hP1',
              by simpa [bvConcatPullup1Prem2Raw, bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup1Prem3Raw] using hP3'⟩)

theorem bvConcatPullup1Program_normalize
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation ny ->
    RuleProofs.eo_has_smt_translation nym ->
    bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvConcatPullup1Prem1 ny y ∧
      P2 = bvConcatPullup1Prem2 nxm z y ys ∧
      P3 = bvConcatPullup1Prem3 nym y := by
  intro hXsTrans hWsTrans hYTrans hZTrans hYsTrans hNxmTrans hNyTrans
    hNymTrans hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmTrans
  have hNy := RuleProofs.term_ne_stuck_of_has_smt_translation ny hNyTrans
  have hNym := RuleProofs.term_ne_stuck_of_has_smt_translation nym hNymTrans
  rcases bvConcatPullup1_premise_shape op xs ws y z ys nxm ny nym P1 P2 P3
      hXs hWs hY hZ hYs hNxm hNy hNym hProg with
    ⟨nyRef, yRef1, nxmRef, zRef, yRef2, ysRef, nymRef, yRef3,
      hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  cases op with
  | band =>
      change __eo_prog_bv_and_concat_pullup xs ws y z ys nxm ny nym
        (Proof.pf (bvConcatPullup1Prem1Raw nyRef yRef1))
        (Proof.pf (bvConcatPullup1Prem2Raw nxmRef zRef yRef2 ysRef))
        (Proof.pf (bvConcatPullup1Prem3Raw nymRef yRef3)) ≠ Term.Stuck at hReq
      simp only [bvConcatPullup1Prem1Raw, bvConcatPullup1Prem2Raw,
        bvConcatPullup1Prem3Raw, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_and_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup1_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup1Prem1],
        by simpa [bvConcatPullup1Prem2], by simpa [bvConcatPullup1Prem3]⟩
  | bor =>
      change __eo_prog_bv_or_concat_pullup xs ws y z ys nxm ny nym
        (Proof.pf (bvConcatPullup1Prem1Raw nyRef yRef1))
        (Proof.pf (bvConcatPullup1Prem2Raw nxmRef zRef yRef2 ysRef))
        (Proof.pf (bvConcatPullup1Prem3Raw nymRef yRef3)) ≠ Term.Stuck at hReq
      simp only [bvConcatPullup1Prem1Raw, bvConcatPullup1Prem2Raw,
        bvConcatPullup1Prem3Raw, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_or_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup1_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup1Prem1],
        by simpa [bvConcatPullup1Prem2], by simpa [bvConcatPullup1Prem3]⟩
  | bxor =>
      change __eo_prog_bv_xor_concat_pullup xs ws y z ys nxm ny nym
        (Proof.pf (bvConcatPullup1Prem1Raw nyRef yRef1))
        (Proof.pf (bvConcatPullup1Prem2Raw nxmRef zRef yRef2 ysRef))
        (Proof.pf (bvConcatPullup1Prem3Raw nymRef yRef3)) ≠ Term.Stuck at hReq
      simp only [bvConcatPullup1Prem1Raw, bvConcatPullup1Prem2Raw,
        bvConcatPullup1Prem3Raw, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_xor_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        nyRef yRef1 nxmRef zRef yRef2 ysRef nymRef yRef3
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup1_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup1Prem1],
        by simpa [bvConcatPullup1Prem2], by simpa [bvConcatPullup1Prem3]⟩

theorem bvConcatPullup1Program_eq_raw
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> ys ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    ny ≠ Term.Stuck -> nym ≠ Term.Stuck ->
    bvConcatPullup1Program op xs ws y z ys nxm ny nym
        (bvConcatPullup1Prem1 ny y)
        (bvConcatPullup1Prem2 nxm z y ys)
        (bvConcatPullup1Prem3 nym y) =
      bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym := by
  intro hXs hWs hY hZ hYs hNxm hNy hNym
  cases op with
  | band =>
      unfold bvConcatPullup1Program bvConcatPullup1Prem1
        bvConcatPullup1Prem2 bvConcatPullup1Prem3
        bvConcatPullup1Prem1Raw bvConcatPullup1Prem2Raw
        bvConcatPullup1Prem3Raw bvConcatPullupConcat
      rw [__eo_prog_bv_and_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        ny y nxm z y ys nym y hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullup1BodyRaw, bvConcatPullup1LhsRaw,
        bvConcatPullup1RhsRaw, bvConcatPullup1LowRaw,
        bvConcatPullup1HighRaw, bvConcatPullupAggregate,
        bvConcatPullup1ConcatZYs, bvConcatPullup1ConcatZs,
        bvConcatPullupConcat, BvConcatPullupOp.term,
        __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]
  | bor =>
      unfold bvConcatPullup1Program bvConcatPullup1Prem1
        bvConcatPullup1Prem2 bvConcatPullup1Prem3
        bvConcatPullup1Prem1Raw bvConcatPullup1Prem2Raw
        bvConcatPullup1Prem3Raw bvConcatPullupConcat
      rw [__eo_prog_bv_or_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        ny y nxm z y ys nym y hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullup1BodyRaw, bvConcatPullup1LhsRaw,
        bvConcatPullup1RhsRaw, bvConcatPullup1LowRaw,
        bvConcatPullup1HighRaw, bvConcatPullupAggregate,
        bvConcatPullup1ConcatZYs, bvConcatPullup1ConcatZs,
        bvConcatPullupConcat, BvConcatPullupOp.term,
        __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]
  | bxor =>
      unfold bvConcatPullup1Program bvConcatPullup1Prem1
        bvConcatPullup1Prem2 bvConcatPullup1Prem3
        bvConcatPullup1Prem1Raw bvConcatPullup1Prem2Raw
        bvConcatPullup1Prem3Raw bvConcatPullupConcat
      rw [__eo_prog_bv_xor_concat_pullup.eq_9 xs ws y z ys nxm ny nym
        ny y nxm z y ys nym y hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullup1BodyRaw, bvConcatPullup1LhsRaw,
        bvConcatPullup1RhsRaw, bvConcatPullup1LowRaw,
        bvConcatPullup1HighRaw, bvConcatPullupAggregate,
        bvConcatPullup1ConcatZYs, bvConcatPullup1ConcatZs,
        bvConcatPullupConcat, BvConcatPullupOp.term,
        __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]

private theorem pullup_list_concat_parts_of_ne_stuck
    (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have hA := support_eo_requires_cond_eq_of_non_stuck hReq
  have hTail := eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hReq
  exact ⟨hA, support_eo_requires_cond_eq_of_non_stuck hTail⟩

private theorem pullup_term_ne_stuck_of_is_list_true (f t : Term) :
    __eo_is_list f t = Term.Boolean true -> t ≠ Term.Stuck := by
  intro hList h
  subst t
  cases f <;> simp [__eo_is_list] at hList

private theorem bvConcatPullup1LhsRaw_eq
    (op : BvConcatPullupOp) (xs ws y z ys : Term) :
    bvConcatPullup1LhsRaw op xs ws y z ys ≠ Term.Stuck ->
    bvConcatPullup1LhsRaw op xs ws y z ys =
      bvConcatPullup1Lhs op xs ws y z ys := by
  intro hLhs
  let full := bvConcatPullup1ConcatZYs z y ys
  let head := __eo_mk_apply op.term full
  let tail := __eo_mk_apply head ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullup1LhsRaw, full, head, tail] using hLhs)
  have hTail : tail ≠ Term.Stuck :=
    pullup_term_ne_stuck_of_is_list_true op.term tail hLists.2
  have hHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck head ws hTail
  have hFull := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term full hHead
  have hHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term full hHead
  have hTailEq := eo_mk_apply_eq_apply_of_ne_stuck head ws hTail
  calc
    bvConcatPullup1LhsRaw op xs ws y z ys =
        __eo_list_concat op.term xs tail := by
      rfl
    _ = __eo_list_concat op.term xs
        (op.apply full ws) := by
      dsimp [tail, head, BvConcatPullupOp.apply] at hTailEq hHeadEq ⊢
      rw [hTailEq, hHeadEq]
    _ = bvConcatPullup1Lhs op xs ws y z ys := by
      rfl

private theorem bvConcatPullup1RhsRaw_eq
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym ≠ Term.Stuck ->
    bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym =
      bvConcatPullup1Rhs op xs ws y z ys nxm ny nym := by
  intro hRhs
  let hiR := bvConcatPullup1HighRaw op xs ws nxm ny
  let loR := bvConcatPullup1LowRaw op xs ws nym
  let hiTailHead := __eo_mk_apply op.term (bvConcatPullup1ConcatZs z ys)
  let hiTail := __eo_mk_apply hiTailHead
    (__eo_nil op.term (__eo_typeof hiR))
  let hiHead := __eo_mk_apply op.term hiR
  let hi := __eo_mk_apply hiHead hiTail
  let loTail := __eo_mk_apply (Term.Apply op.term y)
    (__eo_nil op.term (__eo_typeof loR))
  let loHead := __eo_mk_apply op.term loR
  let lo := __eo_mk_apply loHead loTail
  let loConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) lo
  let loConcat := __eo_mk_apply loConcatHead (Term.Binary 0 0)
  let hiConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) hi
  have hRhs' : __eo_mk_apply hiConcatHead loConcat ≠ Term.Stuck := by
    simpa [bvConcatPullup1RhsRaw, hiR, loR, hiTailHead, hiTail,
      hiHead, hi, loTail, loHead, lo, loConcatHead, loConcat,
      hiConcatHead] using hRhs
  have hHiConcatHead :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hiConcatHead loConcat hRhs'
  have hLoConcat :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck hiConcatHead loConcat hRhs'
  have hHi := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hLoConcatHead :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck loConcatHead (Term.Binary 0 0)
      hLoConcat
  have hLo := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hHiHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term hiR hHiHead
  have hHiTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hLoHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term loR hLoHead
  have hHiREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nxm ny)
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hHiR; (try simp [hiR] at hsimpa ⊢); exact hsimpa)
  have hLoREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nym (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hLoR; (try simp [loR] at hsimpa ⊢); exact hsimpa)
  have hHiTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term
    (bvConcatPullup1ConcatZs z ys) hHiTailHead
  have hHiTailEq := eo_mk_apply_eq_apply_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hHiHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term hiR hHiHead
  have hHiEq := eo_mk_apply_eq_apply_of_ne_stuck hiHead hiTail hHi
  have hLoTailEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.Apply op.term y) (__eo_nil op.term (__eo_typeof loR)) hLoTail
  have hLoHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term loR hLoHead
  have hLoEq := eo_mk_apply_eq_apply_of_ne_stuck loHead loTail hLo
  have hLoConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hLoConcatEq := eo_mk_apply_eq_apply_of_ne_stuck loConcatHead
    (Term.Binary 0 0) hLoConcat
  have hHiConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hRhsEq := eo_mk_apply_eq_apply_of_ne_stuck hiConcatHead loConcat hRhs'
  dsimp [bvConcatPullup1RhsRaw, bvConcatPullup1HighRaw,
    bvConcatPullup1LowRaw, hiR, loR, hiTailHead, hiTail,
    hiHead, hi, loTail, loHead, lo, loConcatHead, loConcat,
    hiConcatHead] at *
  simp only [hHiREq, hLoREq] at *
  rw [hRhsEq, hHiConcatHeadEq, hHiEq, hHiHeadEq,
    hHiTailEq, hHiTailHeadEq, hLoConcatEq, hLoConcatHeadEq,
    hLoEq, hLoHeadEq, hLoTailEq]
  rfl

theorem bvConcatPullup1BodyRaw_eq_term
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym ≠ Term.Stuck ->
    bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym =
      bvConcatPullup1Term op xs ws y z ys nxm ny nym := by
  intro hBody
  let lhsR := bvConcatPullup1LhsRaw op xs ws y z ys
  let rhsR := bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhsR
  have hBody' : __eo_mk_apply eqHead rhsR ≠ Term.Stuck := by
    simpa [bvConcatPullup1BodyRaw, lhsR, rhsR, eqHead] using hBody
  have hEqHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hRhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hLhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hLhsEq := bvConcatPullup1LhsRaw_eq op xs ws y z ys hLhs
  have hRhsEq := bvConcatPullup1RhsRaw_eq op xs ws y z ys nxm ny nym hRhs
  have hHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck eqHead rhsR hBody'
  dsimp [lhsR, rhsR, eqHead] at hLhsEq hRhsEq hHeadEq hOuterEq ⊢
  calc
    bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq)
            (bvConcatPullup1LhsRaw op xs ws y z ys))
          (bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym) := by rfl
    _ = Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (bvConcatPullup1LhsRaw op xs ws y z ys))
          (bvConcatPullup1RhsRaw op xs ws y z ys nxm ny nym) := by
      rw [hOuterEq, hHeadEq]
    _ = bvConcatPullup1Term op xs ws y z ys nxm ny nym := by
      rw [hLhsEq, hRhsEq]
      rfl

theorem BvConcatPullupOp.binaryArgsSmtType
    (op : BvConcatPullupOp) (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (op.apply x y)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w := by
  cases op with
  | band => exact BvNaryAndSupport.binaryArgsSmtType x y w
  | bor => exact BvNaryOrSupport.binaryArgsSmtType x y w
  | bxor => exact BvNaryXorSupport.binaryArgsSmtType x y w

theorem BvConcatPullupOp.binarySmtType
    (op : BvConcatPullupOp) (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (op.apply x y)) = SmtType.BitVec w := by
  cases op with
  | band => exact BvNaryAndSupport.binarySmtType x y w
  | bor => exact BvNaryOrSupport.binarySmtType x y w
  | bxor => exact BvNaryXorSupport.binarySmtType x y w

theorem BvConcatPullupOp.listConcatRecSmtType
    (op : BvConcatPullupOp) (a z : Term) (w : Nat) :
    __eo_is_list op.term a = Term.Boolean true ->
    __eo_is_list op.term z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w := by
  cases op with
  | band => exact BvNaryAndSupport.listConcatRecSmtType a z w
  | bor => exact BvNaryOrSupport.listConcatRecSmtType a z w
  | bxor => exact BvNaryXorSupport.listConcatRecSmtType a z w

theorem BvConcatPullupOp.listSingletonElimSmtType
    (op : BvConcatPullupOp) (c : Term) (w : Nat) :
    __eo_is_list op.term c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt (__eo_list_singleton_elim op.term c)) =
      SmtType.BitVec w := by
  cases op with
  | band => exact BvNaryAndSupport.listSingletonElimSmtType c w
  | bor => exact BvNaryOrSupport.listSingletonElimSmtType c w
  | bxor => exact BvNaryXorSupport.listSingletonElimSmtType c w

theorem BvConcatPullupOp.listConcatRecEvalEq
    (op : BvConcatPullupOp)
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (w : Nat) :
    __eo_is_list op.term a = Term.Boolean true ->
    __eo_is_list op.term z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
      __smtx_model_eval M (__eo_to_smt (op.apply a z)) := by
  cases op with
  | band => exact BvNaryAndSupport.listConcatRecEvalEq M hM a z w
  | bor => exact BvNaryOrSupport.listConcatRecEvalEq M hM a z w
  | bxor => exact BvNaryXorSupport.listConcatRecEvalEq M hM a z w

theorem BvConcatPullupOp.listSingletonElimEvalEq
    (op : BvConcatPullupOp)
    (M : SmtModel) (hM : model_wf M)
    (c : Term) (w : Nat) :
    __eo_is_list op.term c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim op.term c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  cases op with
  | band => exact BvNaryAndSupport.listSingletonElimEvalEq M hM c w
  | bor => exact BvNaryOrSupport.listSingletonElimEvalEq M hM c w
  | bxor => exact BvNaryXorSupport.listSingletonElimEvalEq M hM c w

theorem BvConcatPullupOp.evalAssoc
    (op : BvConcatPullupOp)
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (op.apply (op.apply x y) z)) =
      __smtx_model_eval M (__eo_to_smt (op.apply x (op.apply y z))) := by
  cases op with
  | band => exact BvNaryAndSupport.evalAssoc M hM x y z w
  | bor => exact BvNaryOrSupport.evalAssoc M hM x y z w
  | bxor => exact BvNaryXorSupport.evalAssoc M hM x y z w

theorem BvConcatPullupOp.evalComm
    (op : BvConcatPullupOp)
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (op.apply x y)) =
      __smtx_model_eval M (__eo_to_smt (op.apply y x)) := by
  cases op with
  | band => exact BvNaryAndSupport.evalComm M hM x y w
  | bor => exact BvNaryOrSupport.evalComm M hM x y w
  | bxor => exact BvNaryXorSupport.evalComm M hM x y w

theorem BvConcatPullupOp.evalRightNil
    (op : BvConcatPullupOp)
    (M : SmtModel) (hM : model_wf M)
    (x nil : Term) (w : Nat) :
    __eo_is_list_nil op.term nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (op.apply x nil)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  cases op with
  | band => exact BvNaryAndSupport.evalRightNil M hM x nil w
  | bor => exact BvNaryOrSupport.evalRightNil M hM x nil w
  | bxor => exact BvNaryXorSupport.evalRightNil M hM x nil w

theorem BvConcatPullupOp.evalApply
    (op : BvConcatPullupOp) (M : SmtModel) (x y : Term) :
    __smtx_model_eval M (__eo_to_smt (op.apply x y)) =
      op.eval (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  cases op <;> rfl

theorem BvConcatPullupOp.splitValue
    (op : BvConcatPullupOp)
    (W k : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W)
    (ha0 : 0 ≤ an) (ha1 : an < 2^W)
    (hk1 : 1 ≤ k) (hkW : k ≤ W) :
    op.eval (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an) =
      __smtx_model_eval_concat
        (op.eval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(W - 1))
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (op.eval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) := by
  cases op with
  | band =>
      simpa [BvConcatPullupOp.eval] using
        bvand_concat_full_split_value W k cn an hc0 hc1 ha0 ha1 hk1 hkW
  | bor =>
      simpa [BvConcatPullupOp.eval] using
        bvor_concat_full_split_value W k cn an hc0 hc1 ha0 ha1 hk1 hkW
  | bxor =>
      simpa [BvConcatPullupOp.eval] using
        bvxor_concat_full_split_value W k cn an hc0 hc1 ha0 ha1 hk1 hkW

theorem BvConcatPullupOp.splitSliceValue
    (op : BvConcatPullupOp)
    (W : Nat) (cn an : Int) (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    op.eval
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
          (SmtValue.Numeral 0) (SmtValue.Binary ↑W an)) =
      __smtx_model_eval_concat
        (op.eval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑s)
            (SmtValue.Numeral ↑k) (SmtValue.Binary ↑W an)))
        (op.eval
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W cn))
          (__smtx_model_eval_extract (SmtValue.Numeral ↑(k - 1))
            (SmtValue.Numeral 0) (SmtValue.Binary ↑W an))) := by
  cases op with
  | band => simpa [BvConcatPullupOp.eval] using
      bvand_concat_slice_split_value W cn an hc0 ha0 s k hk1 hks
  | bor => simpa [BvConcatPullupOp.eval] using
      bvor_concat_slice_split_value W cn an hc0 ha0 s k hk1 hks
  | bxor => simpa [BvConcatPullupOp.eval] using
      bvxor_concat_slice_split_value W cn an hc0 ha0 s k hk1 hks

def PullupListTypeOrNil (t : Term) (w : Nat) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

private theorem pullup_term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy h
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem pullup_generated_nil_marker
    (op : BvConcatPullupOp) (width : Nat) :
    __eo_nil op.term
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int width))) ≠
      Term.Stuck ->
    __eo_is_list_nil op.term
        (__eo_nil op.term
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int width)))) =
      Term.Boolean true := by
  intro hNil
  cases op with
  | band => exact bvand_generated_nil_marker width (by
      simpa [BvConcatPullupOp.term] using hNil)
  | bor => exact bvor_generated_nil_marker width (by
      simpa [BvConcatPullupOp.term] using hNil)
  | bxor => exact bvxor_generated_nil_marker width (by
      simpa [BvConcatPullupOp.term] using hNil)

private theorem pullup_generated_nil_smt_type
    (op : BvConcatPullupOp) (width : Nat) :
    __eo_nil op.term
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int width))) ≠
      Term.Stuck ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_nil op.term
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int width))))) =
      SmtType.BitVec width := by
  intro hNil
  cases op with
  | band => exact bvand_generated_nil_smt_type width (by
      simpa [BvConcatPullupOp.term] using hNil)
  | bor => exact bvor_generated_nil_smt_type width (by
      simpa [BvConcatPullupOp.term] using hNil)
  | bxor => exact bvxor_generated_nil_smt_type width (by
      simpa [BvConcatPullupOp.term] using hNil)

theorem bvConcatPullupEvalApplyGeneratedNil
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp) (x T : Term) (w width : Nat) :
    T =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int width)) ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (op.apply x (__eo_nil op.term T))) =
      SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (op.apply x (__eo_nil op.term T))) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hTEoTy hXTy hApplyTy
  let nil := __eo_nil op.term T
  have hArgs := op.binaryArgsSmtType x nil w (by
    simpa [nil] using hApplyTy)
  have hNilNe := pullup_term_ne_stuck_of_smt_bitvec_type hArgs.2
  have hMarker := pullup_generated_nil_marker op width (by
    simpa [nil, hTEoTy] using hNilNe)
  exact op.evalRightNil M hM x nil w (by
    simpa [nil, hTEoTy] using hMarker)
    hArgs.1 hArgs.2

private theorem pullup_eo_typeof_eq_bitvec_of_smt_bitvec
    (t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hTrans : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTy]
    intro h
    cases h
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_bitvec
    (hMatch.symm.trans hTy)

private theorem pullup_list_concat_eq_rec
    (f a z : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f z = Term.Boolean true ->
    __eo_list_concat f a z = __eo_list_concat_rec a z := by
  intro hA hZ
  simp [__eo_list_concat, hA, hZ, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem pullup_list_concat_rec_cons_of_right_ne_stuck
    (f x xs z : Term) :
    z ≠ Term.Stuck ->
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs z) := by
  intro hZ
  cases z <;> first | exact absurd rfl hZ | rfl

private theorem pullup_list_type_or_nil_of_concat_type
    (op : BvConcatPullupOp) (a z : Term) (w : Nat) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list op.term a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w ->
    PullupListTypeOrNil a w := by
  intro hATrans hAList hZTy hResultTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hAList rfl)
  | case2 a hA =>
      change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hZTy
      rw [TranslationProofs.smtx_typeof_none] at hZTy
      cases hZTy
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hAList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op.term x xs hAList
      have hResultNe := pullup_term_ne_stuck_of_smt_bitvec_type hResultTy
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hResultNe
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hZNe,
          h]
        rfl
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResultTy
      have hXTy := (op.binaryArgsSmtType x
        (__eo_list_concat_rec xs z) w hResultTy).1
      unfold RuleProofs.eo_has_smt_translation at hATrans
      have hOrigNN : __smtx_typeof (__eo_to_smt (op.apply x xs)) ≠
          SmtType.None := by
        simpa [BvConcatPullupOp.apply] using hATrans
      cases op with
      | band =>
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
              (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
                  (__eo_to_smt xs)) =
                __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                  (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_def] <;> simp only) hOrigNN with
            ⟨actual, hXActual, hXsActual⟩
          have hw : actual = w := by rw [hXTy] at hXActual; cases hXActual; rfl
          subst actual
          exact Or.inl (BvNaryAndSupport.binarySmtType x xs w hXTy hXsActual)
      | bor =>
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
              (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                  (__eo_to_smt xs)) =
                __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                  (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_def] <;> simp only) hOrigNN with
            ⟨actual, hXActual, hXsActual⟩
          have hw : actual = w := by rw [hXTy] at hXActual; cases hXActual; rfl
          subst actual
          exact Or.inl (BvNaryOrSupport.binarySmtType x xs w hXTy hXsActual)
      | bxor =>
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
              (show __smtx_typeof (SmtTerm.bvxor (__eo_to_smt x)
                  (__eo_to_smt xs)) =
                __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                  (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_44]) hOrigNN with
            ⟨actual, hXActual, hXsActual⟩
          have hw : actual = w := by rw [hXTy] at hXActual; cases hXActual; rfl
          subst actual
          exact Or.inl (BvNaryXorSupport.binarySmtType x xs w hXTy hXsActual)
  | case4 nil z hNil hZ hNot =>
      exact Or.inr (fun tail => by
        unfold __eo_list_concat_rec
        split <;> simp_all)

theorem bvConcatPullupListEval
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp) (xs ws full : Term) (w : Nat) :
    __eo_is_list op.term xs = Term.Boolean true ->
    __eo_is_list op.term ws = Term.Boolean true ->
    PullupListTypeOrNil xs w ->
    __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat op.term xs (op.apply full ws))) =
      op.eval
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim op.term
              (__eo_list_concat op.term xs ws))))
        (__smtx_model_eval M (__eo_to_smt full)) := by
  intro hXsList hWsList hXsType hWsTy hFullTy
  let tail := op.apply full ws
  let c := __eo_list_concat op.term xs ws
  have hTailList : __eo_is_list op.term tail = Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list op.term full ws (by
      cases op <;> decide) hWsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec w :=
    op.binarySmtType full ws w hFullTy hWsTy
  have hCList : __eo_is_list op.term c = Term.Boolean true := by
    have hRecList := eo_list_concat_rec_is_list_true_of_lists op.term xs ws
      hXsList hWsList
    dsimp [c]
    rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
    exact hRecList
  rcases hXsType with hXsTy | hXsNil
  · have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
      dsimp only [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact op.listConcatRecSmtType xs ws w hXsList hWsList hXsTy hWsTy
    have hElim := op.listSingletonElimEvalEq M hM c w hCList hCTy
    have hLhsRec := op.listConcatRecEvalEq M hM xs tail w
      hXsList hTailList hXsTy hTailTy
    have hCRec := op.listConcatRecEvalEq M hM xs ws w
      hXsList hWsList hXsTy hWsTy
    have hComm := op.evalComm M hM full ws w hFullTy hWsTy
    have hAssoc := op.evalAssoc M hM xs ws full w hXsTy hWsTy hFullTy
    simp only [op.evalApply] at hComm hAssoc
    have hCEval : __smtx_model_eval M (__eo_to_smt c) =
        __smtx_model_eval M (__eo_to_smt (op.apply xs ws)) := by
      dsimp only [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact hCRec
    have hAggEval :
        __smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim op.term
                (__eo_list_concat op.term xs ws))) =
          __smtx_model_eval M (__eo_to_smt (op.apply xs ws)) := by
      dsimp only [c] at hElim
      exact hElim.trans hCEval
    dsimp only [tail] at hLhsRec
    rw [pullup_list_concat_eq_rec op.term xs tail hXsList hTailList,
      hLhsRec]
    rw [op.evalApply, op.evalApply]
    rw [hComm]
    rw [← hAssoc]
    rw [← op.evalApply M xs ws, ← hAggEval]
  · have hCeq : c = ws := by
      dsimp only [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList,
        hXsNil ws]
    have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
      rw [hCeq]
      exact hWsTy
    have hElim := op.listSingletonElimEvalEq M hM c w hCList hCTy
    have hAggEval :
        __smtx_model_eval M
            (__eo_to_smt
              (__eo_list_singleton_elim op.term
                (__eo_list_concat op.term xs ws))) =
          __smtx_model_eval M (__eo_to_smt ws) := by
      dsimp only [c] at hElim hCeq
      rw [hElim, hCeq]
    have hLhsEq : __eo_list_concat op.term xs tail = tail := by
      rw [pullup_list_concat_eq_rec op.term xs tail hXsList hTailList,
        hXsNil tail]
    dsimp only [tail] at hLhsEq
    rw [hLhsEq]
    rw [op.evalApply]
    have hComm := op.evalComm M hM full ws w hFullTy hWsTy
    simp only [op.evalApply] at hComm
    rw [hComm, ← hAggEval]

theorem bvConcatPullupListSmtType
    (op : BvConcatPullupOp) (xs ws full : Term) (w : Nat) :
    __eo_is_list op.term xs = Term.Boolean true ->
    __eo_is_list op.term ws = Term.Boolean true ->
    PullupListTypeOrNil xs w ->
    __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt (__eo_list_concat op.term xs (op.apply full ws))) =
      SmtType.BitVec w := by
  intro hXsList hWsList hXsType hWsTy hFullTy
  let tail := op.apply full ws
  have hTailList : __eo_is_list op.term tail = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list op.term full ws
      (by cases op <;> decide) hWsList
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec w :=
    op.binarySmtType full ws w hFullTy hWsTy
  rw [pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
  rcases hXsType with hXsTy | hXsNil
  · exact op.listConcatRecSmtType xs tail w hXsList hTailList hXsTy hTailTy
  · rw [hXsNil tail]
    exact hTailTy

private theorem pullup_list_concat_rec_right_smt_non_none
    (op : BvConcatPullupOp) (a z : Term) :
    __eo_is_list op.term a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt z) ≠ SmtType.None := by
  intro hList hResult
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hList rfl)
  | case2 a hA =>
      have hBad : __eo_list_concat_rec a Term.Stuck = Term.Stuck := by
        cases a <;> rfl
      rw [hBad] at hResult
      exact False.elim (hResult TranslationProofs.smtx_typeof_none)
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op.term x xs hList
      have hWholeNe : __eo_list_concat_rec
          (Term.Apply (Term.Apply op.term x) xs) z ≠ Term.Stuck := by
        intro h
        rw [h] at hResult
        exact hResult TranslationProofs.smtx_typeof_none
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hWholeNe
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hZNe, h]
        rfl
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResult
      have hTailSmtNN :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z)) ≠
            SmtType.None := by
        cases op with
        | band =>
            rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
              (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_def] <;> simp only) hResult with
              ⟨actual, _hX, hTail⟩
            rw [hTail]
            simp
        | bor =>
            rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
              (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_def] <;> simp only) hResult with
              ⟨actual, _hX, hTail⟩
            rw [hTail]
            simp
        | bxor =>
            rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
              (show __smtx_typeof (SmtTerm.bvxor (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_44]) hResult with
              ⟨actual, _hX, hTail⟩
            rw [hTail]
            simp
      exact ih hTailList hTailSmtNN
  | case4 nil z hNil hZ hNot =>
      simpa [__eo_list_concat_rec] using hResult

private theorem pullup_list_concat_rec_result_smt_type
    (op : BvConcatPullupOp) (a z : Term) (w : Nat) :
    __eo_is_list op.term a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w := by
  intro hList hZTy hResult
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hList rfl)
  | case2 a hA =>
      change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hZTy
      rw [TranslationProofs.smtx_typeof_none] at hZTy
      cases hZTy
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op.term x xs hList
      have hWholeNe : __eo_list_concat_rec
          (Term.Apply (Term.Apply op.term x) xs) z ≠ Term.Stuck := by
        intro h
        rw [h] at hResult
        exact hResult TranslationProofs.smtx_typeof_none
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hWholeNe
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hZNe, h]
        rfl
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResult ⊢
      have hArgs : ∃ actual,
          __smtx_typeof (__eo_to_smt x) = SmtType.BitVec actual ∧
            __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z)) =
              SmtType.BitVec actual := by
        cases op with
        | band =>
            exact bv_binop_args_of_non_none (op := SmtTerm.bvand)
              (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_def] <;> simp only) hResult
        | bor =>
            exact bv_binop_args_of_non_none (op := SmtTerm.bvor)
              (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_def] <;> simp only) hResult
        | bxor =>
            exact bv_binop_args_of_non_none (op := SmtTerm.bvxor)
              (show __smtx_typeof (SmtTerm.bvxor (__eo_to_smt x)
                    (__eo_to_smt (__eo_list_concat_rec xs z))) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z))) by
                rw [__smtx_typeof.eq_44]) hResult
      rcases hArgs with ⟨actual, hXTy, hTailActual⟩
      have hTailNN :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs z)) ≠
            SmtType.None := by rw [hTailActual]; simp
      have hTailTy := ih hTailList hZTy hTailNN
      have hw : actual = w := by rw [hTailTy] at hTailActual; cases hTailActual; rfl
      subst actual
      exact op.binarySmtType x (__eo_list_concat_rec xs z) w hXTy hTailTy
  | case4 nil z hNil hZ hNot =>
      simpa [__eo_list_concat_rec] using hZTy

private theorem pullup_typeof_bvand_arg_types_of_ne_stuck
    {A B : Term} (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠ Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem pullup_typeof_apply_args_of_result_bitvec
    (op : BvConcatPullupOp) (x y width : Term) :
    __eo_typeof (op.apply x y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  have h' : __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
    cases op <;>
      (have hsimpa := h
       try simp [BvConcatPullupOp.apply, BvConcatPullupOp.term] at hsimpa ⊢
       exact hsimpa)
  have hNe :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) ≠ Term.Stuck := by
    rw [h']
    intro hBad
    cases hBad
  rcases pullup_typeof_bvand_arg_types_of_ne_stuck hNe with
    ⟨actualWidth, hx, hy⟩
  have hWidthNe : actualWidth ≠ Term.Stuck := by
    intro hStuck
    apply hNe
    rw [hx, hy, hStuck]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth)
          (Term.Apply (Term.UOp UserOp.BitVec) actualWidth) =
        Term.Apply (Term.UOp UserOp.BitVec) actualWidth := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hWidthNe]
  have hWidth : actualWidth = width := by
    rw [hx, hy, hReduce] at h'
    cases h'
    rfl
  subst width
  exact ⟨hx, hy⟩

private theorem pullup_typeof_apply
    (op : BvConcatPullupOp) (x y : Term) :
    __eo_typeof (op.apply x y) =
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) := by
  cases op <;> rfl

private theorem pullup_list_concat_rec_right_type_non_stuck
    (op : BvConcatPullupOp) (a z : Term) :
    __eo_is_list op.term a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof z ≠ Term.Stuck := by
  intro hList hResult
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hList rfl)
  | case2 a hA =>
      apply False.elim
      apply hResult
      cases a <;> rfl
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op.term x xs hList
      have hWholeNe : __eo_list_concat_rec
          (Term.Apply (Term.Apply op.term x) xs) z ≠ Term.Stuck := by
        intro h
        rw [h] at hResult
        exact hResult rfl
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hWholeNe
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hZNe, h]
        rfl
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResult
      have hTailTypeNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        have hResult' :
            __eo_typeof_bvand (__eo_typeof x)
                (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck := by
          rw [← pullup_typeof_apply op]
          exact hResult
        intro h
        apply hResult'
        rw [h]
        simp [__eo_typeof_bvand]
      exact ih hTailList hTailTypeNe
  | case4 nil z hNil hZ hNot =>
      simpa [__eo_list_concat_rec] using hResult

private theorem pullup_list_concat_rec_result_eo_type
    (op : BvConcatPullupOp) (a z width : Term) :
    __eo_is_list op.term a = Term.Boolean true ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hZTy hResult
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hList rfl)
  | case2 a hA => cases hZTy
  | case3 f x xs z hZNe ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op.term x xs hList
      have hWholeNe : __eo_list_concat_rec
          (Term.Apply (Term.Apply op.term x) xs) z ≠ Term.Stuck := by
        intro h
        rw [h] at hResult
        exact hResult rfl
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hWholeNe
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hZNe, h]
        rfl
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResult ⊢
      have hTailTypeNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        have hResult' :
            __eo_typeof_bvand (__eo_typeof x)
                (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck := by
          rw [← pullup_typeof_apply op]
          exact hResult
        intro h
        apply hResult'
        rw [h]
        simp [__eo_typeof_bvand]
      have hTailTy := ih hTailList hZTy hTailTypeNe
      have hOuterNe :
          __eo_typeof_bvand (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck := by
        rw [← pullup_typeof_apply op]
        exact hResult
      rcases pullup_typeof_bvand_arg_types_of_ne_stuck hOuterNe with
        ⟨actual, hXTy, hTailActual⟩
      have hw : actual = width := by
        rw [hTailTy] at hTailActual
        cases hTailActual
        rfl
      subst actual
      have hReduced :
          __eo_typeof_bvand (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec xs z)) =
            Term.Apply (Term.UOp UserOp.BitVec) width := by
        rw [hXTy, hTailTy]
        have hWidthNe : width ≠ Term.Stuck := by
          intro h
          subst width
          rw [hXTy, hTailTy] at hOuterNe
          simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
            native_teq, native_not] at hOuterNe
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not, hWidthNe]
      change __eo_typeof (op.apply x (__eo_list_concat_rec xs z)) = _
      rw [pullup_typeof_apply]
      exact hReduced
  | case4 nil z hNil hZ hNot =>
      simpa [__eo_list_concat_rec] using hZTy

private theorem pullup_list_type_or_nil_of_concat_eo_type
    (op : BvConcatPullupOp) (a z width : Term) (w : Nat) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list op.term a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) width) =
      SmtType.BitVec w ->
    PullupListTypeOrNil a w := by
  intro hATrans hAList hZNe hResultTy hWidthTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      exact False.elim
        (pullup_term_ne_stuck_of_is_list_true op.term Term.Stuck hAList rfl)
  | case2 a hA => exact False.elim (hZNe rfl)
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op.term f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        rw [pullup_list_concat_rec_cons_of_right_ne_stuck
          op.term x xs z hz, h] at hResultTy
        cases hResultTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op.term x xs z hTailNe]
        at hResultTy
      have hArgs := pullup_typeof_apply_args_of_result_bitvec op
        x (__eo_list_concat_rec xs z) width hResultTy
      unfold RuleProofs.eo_has_smt_translation at hATrans
      have hOrigNN : __smtx_typeof (__eo_to_smt (op.apply x xs)) ≠
          SmtType.None := by
        simpa [BvConcatPullupOp.apply] using hATrans
      cases op with
      | band =>
          have hNN : __smtx_typeof
              (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt xs)) ≠
                SmtType.None := by
            simpa [BvConcatPullupOp.apply, BvConcatPullupOp.term] using hOrigNN
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
              (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
                    (__eo_to_smt xs)) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_def] <;> simp only) hNN with
            ⟨actual, hXActual, hXsActual⟩
          have hXMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
            x (by rw [hXActual]; simp)
          have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
            rw [hArgs.1] at hXMatch
            exact hXMatch.trans hWidthTy
          have hw : actual = w := by
            rw [hXTy] at hXActual
            cases hXActual
            rfl
          subst actual
          exact Or.inl
            (BvNaryAndSupport.binarySmtType x xs w hXTy hXsActual)
      | bor =>
          have hNN : __smtx_typeof
              (SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt xs)) ≠
                SmtType.None := by
            simpa [BvConcatPullupOp.apply, BvConcatPullupOp.term] using hOrigNN
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
              (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                    (__eo_to_smt xs)) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_def] <;> simp only) hNN with
            ⟨actual, hXActual, hXsActual⟩
          have hXMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
            x (by rw [hXActual]; simp)
          have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
            rw [hArgs.1] at hXMatch
            exact hXMatch.trans hWidthTy
          have hw : actual = w := by
            rw [hXTy] at hXActual
            cases hXActual
            rfl
          subst actual
          exact Or.inl
            (BvNaryOrSupport.binarySmtType x xs w hXTy hXsActual)
      | bxor =>
          have hNN : __smtx_typeof
              (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt xs)) ≠
                SmtType.None := by
            simpa [BvConcatPullupOp.apply, BvConcatPullupOp.term] using hOrigNN
          rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
              (show __smtx_typeof (SmtTerm.bvxor (__eo_to_smt x)
                    (__eo_to_smt xs)) =
                  __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
                    (__smtx_typeof (__eo_to_smt xs)) by
                rw [__smtx_typeof.eq_44]) hNN with
            ⟨actual, hXActual, hXsActual⟩
          have hXMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
            x (by rw [hXActual]; simp)
          have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
            rw [hArgs.1] at hXMatch
            exact hXMatch.trans hWidthTy
          have hw : actual = w := by
            rw [hXTy] at hXActual
            cases hXActual
            rfl
          subst actual
          exact Or.inl
            (BvNaryXorSupport.binarySmtType x xs w hXTy hXsActual)
  | case4 nil z hNil hZ hNot =>
      exact Or.inr (fun tail => by
        unfold __eo_list_concat_rec
        split <;> simp_all)

theorem bvConcatPullup1ListsOfBodyType
    (op : BvConcatPullupOp) (xs ws y z ys nxm ny nym : Term) :
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup1Lhs op xs ws y z ys))
    (__eo_typeof (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup1Term] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullup1Lhs op xs ws y z ys ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let full := bvConcatPullup1ConcatZYs z y ys
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullup1Lhs, full, tail] using hLhsNe)
  have hXsList := hLists.1
  have hTailList := hLists.2
  have hWsList : __eo_is_list op.term ws = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op.term full ws hTailList
  have hRecTypeNe : __eo_typeof (__eo_list_concat_rec xs tail) ≠
      Term.Stuck := by
    rw [← pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
    simpa [bvConcatPullup1Lhs, full, tail] using hSides.1
  have hTailTypeNe := pullup_list_concat_rec_right_type_non_stuck op xs tail
    hXsList hRecTypeNe
  have hTailTypeNe' :
      __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) ≠
        Term.Stuck := by
    rw [← pullup_typeof_apply op]
    exact hTailTypeNe
  rcases pullup_typeof_bvand_arg_types_of_ne_stuck hTailTypeNe' with
    ⟨width, hFullEoTy, _hWsEoTy⟩
  have hFullNe : full ≠ Term.Stuck := by
    intro h
    rw [h] at hFullEoTy
    cases hFullEoTy
  have hConcatLists := bvConcat_list_concat_lists_of_ne_stuck ys
    (bvConcatPullupConcat z (bvConcatPullupConcat y (Term.Binary 0 0))) (by
      simpa [full, bvConcatPullup1ConcatZYs] using hFullNe)
  exact ⟨hXsList, hWsList, hConcatLists.1⟩

theorem bvConcatPullup1BaseContextFromFull
    (op : BvConcatPullupOp) (xs ws y z ys nxm ny nym : Term) (w : Nat) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1ConcatZYs z y ys)) =
      SmtType.BitVec w ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ∧
      PullupListTypeOrNil xs w ∧
      __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
        SmtType.BitVec w := by
  intro hXsTrans hWsTrans hFullTy hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup1Lhs op xs ws y z ys))
    (__eo_typeof (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup1Term] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullup1Lhs op xs ws y z ys ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let full := bvConcatPullup1ConcatZYs z y ys
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullup1Lhs, full, tail] using hLhsNe)
  have hXsList := hLists.1
  have hTailList := hLists.2
  have hWsList : __eo_is_list op.term ws = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op.term full ws hTailList
  have hRecTypeNe : __eo_typeof (__eo_list_concat_rec xs tail) ≠
      Term.Stuck := by
    rw [← pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
    simpa [bvConcatPullup1Lhs, full, tail] using hSides.1
  have hTailTypeNe := pullup_list_concat_rec_right_type_non_stuck op xs tail
    hXsList hRecTypeNe
  have hTailTypeNe' :
      __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) ≠
        Term.Stuck := by
    rw [← pullup_typeof_apply op]
    exact hTailTypeNe
  have hTailArgs := pullup_typeof_bvand_arg_types_of_ne_stuck hTailTypeNe'
  rcases hTailArgs with ⟨width, hFullEoTy, hWsEoTy⟩
  have hFullMatch := TranslationProofs.eo_to_smt_typeof_matches_translation full
    (by rw [show __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w by
      simpa [full] using hFullTy]; simp)
  have hWidthTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) width) =
        SmtType.BitVec w := by
    rw [hFullEoTy] at hFullMatch
    exact hFullMatch.symm.trans (by simpa [full] using hFullTy)
  have hWsMatch := TranslationProofs.eo_to_smt_typeof_matches_translation ws
    hWsTrans
  have hWsTy : __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w := by
    rw [hWsEoTy] at hWsMatch
    exact hWsMatch.trans hWidthTy
  have hTailEoTy :
      __eo_typeof tail = Term.Apply (Term.UOp UserOp.BitVec) width := by
    have hReduced :
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) =
          Term.Apply (Term.UOp UserOp.BitVec) width := by
      rw [hFullEoTy, hWsEoTy]
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        subst width
        simp [__eo_to_smt_type] at hWidthTy
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
    rw [show __eo_typeof tail =
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) by
      simpa [tail] using pullup_typeof_apply op full ws]
    exact hReduced
  have hRecEoTy := pullup_list_concat_rec_result_eo_type op xs tail width
    hXsList hTailEoTy hRecTypeNe
  have hTailNe : tail ≠ Term.Stuck := by
    simp [tail, BvConcatPullupOp.apply]
  have hXsType := pullup_list_type_or_nil_of_concat_eo_type op xs tail
    width w hXsTrans hXsList hTailNe hRecEoTy hWidthTy
  have hFullNe := pullup_term_ne_stuck_of_smt_bitvec_type
    (show __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w by
      simpa [full] using hFullTy)
  have hConcatLists := bvConcat_list_concat_lists_of_ne_stuck ys
    (bvConcatPullupConcat z (bvConcatPullupConcat y (Term.Binary 0 0))) (by
      simpa [full, bvConcatPullup1ConcatZYs] using hFullNe)
  have hYsList := hConcatLists.1
  let c := __eo_list_concat op.term xs ws
  have hCList : __eo_is_list op.term c = Term.Boolean true := by
    dsimp [c]
    rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
    exact eo_list_concat_rec_is_list_true_of_lists op.term xs ws
      hXsList hWsList
  have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
    rcases hXsType with hXsTy | hXsNil
    · dsimp [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact op.listConcatRecSmtType xs ws w hXsList hWsList hXsTy hWsTy
    · have hCeq : c = ws := by
        dsimp [c]
        rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList,
          hXsNil ws]
      rw [hCeq]
      exact hWsTy
  have hAggTy := op.listSingletonElimSmtType c w hCList hCTy
  exact ⟨hXsList, hWsList, hYsList, hXsType, hWsTy,
    by simpa [bvConcatPullupAggregate, c] using hAggTy⟩

theorem bvConcatPullup1Prem1Type (ny y : Term) :
    RuleProofs.eo_has_bool_type (bvConcatPullup1Prem1 ny y) ->
    ∃ wy : Nat, __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy := by
  intro hPrem
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type ny
      (Term.Apply (Term.UOp UserOp._at_bvsize) y)
      (by simpa [bvConcatPullup1Prem1, bvConcatPullup1Prem1Raw] using hPrem) with
    ⟨hSame, hNyNN⟩
  have hSizeNN : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hNyNN
  rcases bvConcat_bvsize_smt_type_of_non_none y hSizeNN with
    ⟨wy, hYTy, _⟩
  exact ⟨wy, hYTy⟩

theorem bvConcatPullup1Prem2Type (nxm z y ys : Term) :
    RuleProofs.eo_has_bool_type (bvConcatPullup1Prem2 nxm z y ys) ->
    ∃ wz wy wys : Nat,
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys := by
  intro hPrem
  let full := bvConcatPullupConcat z (bvConcatPullupConcat y ys)
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.UOp UserOp._at_bvsize) full)) (Term.Numeral 1)
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type nxm rhs
      (by simpa [bvConcatPullup1Prem2, bvConcatPullup1Prem2Raw,
        bvConcatPullupConcat, full, rhs]
        using hPrem) with
    ⟨hSame, hNxmNN⟩
  have hRhsNN : __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
    rw [← hSame]
    exact hNxmNN
  have hNegNN : term_has_non_none_type
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) full))
        (SmtTerm.Numeral 1)) := by
    unfold term_has_non_none_type
    have hsimpa := hRhsNN
    try simp [rhs] at hsimpa ⊢
    exact hsimpa
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) full))
        (SmtTerm.Numeral 1)) hNegNN with hArgs | hArgs
  · rcases bvConcat_bvsize_smt_type_inv full hArgs.1 with ⟨w, hFullTy⟩
    rcases bvConcat_term_smt_type_inv z (bvConcatPullupConcat y ys) w
        (by have hsimpa := hFullTy; (try simp [full, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa) with
      ⟨wz, wt, hZTy, hTailTy, _⟩
    rcases bvConcat_term_smt_type_inv y ys wt
        (by have hsimpa := hTailTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa) with
      ⟨wy, wys, hYTy, hYsTy, _⟩
    exact ⟨wz, wy, wys, hZTy, hYTy, hYsTy⟩
  · have hBad := hArgs.2
    simp [__smtx_typeof] at hBad

theorem bvConcatPullup1ConcatTypes
    (z y ys : Term) (wz wy wys : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1ConcatZYs z y ys)) =
      SmtType.BitVec (wys + wz + wy) ∧
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1ConcatZs z ys)) =
      SmtType.BitVec (wys + wz) := by
  intro hYsList hZTy hYTy hYsTy
  have hEmptyList :
      __eo_is_list (Term.UOp UserOp.concat) (Term.Binary 0 0) =
        Term.Boolean true := by native_decide
  have hEmptyTy := bvConcat_empty_smt_type
  have hYEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) y (Term.Binary 0 0) (by decide) hEmptyList
  have hYEmptyTy := bvConcat_term_smt_type y (Term.Binary 0 0) wy 0
    hYTy hEmptyTy
  have hZYEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) z
      (bvConcatPullupConcat y (Term.Binary 0 0)) (by decide) hYEmptyList
  have hZYEmptyTy := bvConcat_term_smt_type z
    (bvConcatPullupConcat y (Term.Binary 0 0)) wz (wy + 0) hZTy
    (by have hsimpa := hYEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hFullTy := bvConcat_list_concat_smt_type ys
    (bvConcatPullupConcat z
      (bvConcatPullupConcat y (Term.Binary 0 0))) wys (wz + (wy + 0))
    hYsList hZYEmptyList hYsTy
    (by have hsimpa := hZYEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hZEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) z (Term.Binary 0 0) (by decide) hEmptyList
  have hZEmptyTy := bvConcat_term_smt_type z (Term.Binary 0 0) wz 0
    hZTy hEmptyTy
  have hHighListTy := bvConcat_list_concat_smt_type ys
    (bvConcatPullupConcat z (Term.Binary 0 0)) wys (wz + 0)
    hYsList hZEmptyList hYsTy
    (by have hsimpa := hZEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hHighList : __eo_is_list (Term.UOp UserOp.concat)
      (__eo_list_concat (Term.UOp UserOp.concat) ys
        (bvConcatPullupConcat z (Term.Binary 0 0))) =
        Term.Boolean true := by
    rw [pullup_list_concat_eq_rec (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0)) hYsList hZEmptyList]
    exact eo_list_concat_rec_is_list_true_of_lists (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0)) hYsList hZEmptyList
  have hHighTy := bvConcat_singleton_elim_smt_type
    (__eo_list_concat (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0))) (wys + (wz + 0))
    hHighList hHighListTy
  constructor
  · simpa [bvConcatPullup1ConcatZYs, Nat.add_assoc] using hFullTy
  · simpa [bvConcatPullup1ConcatZs, Nat.add_assoc] using hHighTy

theorem bvConcatPullup1FullEval
    (M : SmtModel) (hM : model_wf M)
    (z y ys : Term) (wz wy wys : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatPullup1ConcatZYs z y ys)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatPullupConcat (bvConcatPullup1ConcatZs z ys) y)) := by
  intro hYsList hZTy hYTy hYsTy
  have hEmptyList :
      __eo_is_list (Term.UOp UserOp.concat) (Term.Binary 0 0) =
        Term.Boolean true := by native_decide
  have hYEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) y (Term.Binary 0 0) (by decide) hEmptyList
  have hZEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) z (Term.Binary 0 0) (by decide) hEmptyList
  have hZYEmptyList := eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) z
      (bvConcatPullupConcat y (Term.Binary 0 0)) (by decide) hYEmptyList
  have hEmptyTy := bvConcat_empty_smt_type
  have hYEmptyTy := bvConcat_term_smt_type y (Term.Binary 0 0) wy 0
    hYTy hEmptyTy
  have hZEmptyTy := bvConcat_term_smt_type z (Term.Binary 0 0) wz 0
    hZTy hEmptyTy
  have hZyTy := bvConcat_term_smt_type z y wz wy hZTy hYTy
  have hBaseLeft := bvConcat_assoc_eval M hM z y (Term.Binary 0 0)
    wz wy 0 hZTy hYTy hEmptyTy
  have hZyEmpty := bvConcat_eval_right_empty M hM
    (bvConcatPullupConcat z y) (wz + wy)
    (by have hsimpa := hZyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hZEmpty := bvConcat_eval_right_empty M hM z wz hZTy
  have hZEmpty' : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat z (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt z) := by
    simpa [bvConcatPullupConcat, bvConcatTerm] using hZEmpty
  have hBase : __smtx_model_eval M
      (__eo_to_smt
        (bvConcatPullupConcat z
          (bvConcatPullupConcat y (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatPullupConcat
            (bvConcatPullupConcat z (Term.Binary 0 0)) y)) := by
    calc
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatPullupConcat
              (bvConcatPullupConcat z y) (Term.Binary 0 0))) := by
            have hsimpa := hBaseLeft
            try simp [bvConcatPullupConcat] at hsimpa ⊢
            exact hsimpa
      _ = __smtx_model_eval M
          (__eo_to_smt (bvConcatPullupConcat z y)) := hZyEmpty
      _ = __smtx_model_eval M
          (__eo_to_smt
            (bvConcatPullupConcat
              (bvConcatPullupConcat z (Term.Binary 0 0)) y)) := by
            change __smtx_model_eval_concat
                (__smtx_model_eval M (__eo_to_smt z))
                (__smtx_model_eval M (__eo_to_smt y)) =
              __smtx_model_eval_concat
                (__smtx_model_eval M
                  (__eo_to_smt
                    (bvConcatPullupConcat z (Term.Binary 0 0))))
                (__smtx_model_eval M (__eo_to_smt y))
            rw [hZEmpty']
  have hRec := bvConcat_list_concat_rec_eval_append M hM ys
    (bvConcatPullupConcat z
      (bvConcatPullupConcat y (Term.Binary 0 0)))
    (bvConcatPullupConcat z (Term.Binary 0 0)) y
    wys wz wy hYsList hYsTy
    (by
      have h := bvConcat_term_smt_type z
        (bvConcatPullupConcat y (Term.Binary 0 0)) wz (wy + 0) hZTy
        (by have hsimpa := hYEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
      have hsimpa := h; (try simp [bvConcatPullupConcat, Nat.add_assoc] at hsimpa ⊢); exact hsimpa)
    (by have hsimpa := hZEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa) hYTy hBase
  have hHighRawList : __eo_is_list (Term.UOp UserOp.concat)
      (__eo_list_concat (Term.UOp UserOp.concat) ys
        (bvConcatPullupConcat z (Term.Binary 0 0))) =
        Term.Boolean true := by
    rw [pullup_list_concat_eq_rec (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0)) hYsList hZEmptyList]
    exact eo_list_concat_rec_is_list_true_of_lists (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0)) hYsList hZEmptyList
  have hHighRawTy := bvConcat_list_concat_smt_type ys
    (bvConcatPullupConcat z (Term.Binary 0 0)) wys (wz + 0)
    hYsList hZEmptyList hYsTy
    (by have hsimpa := hZEmptyTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hElim := bvConcat_singleton_elim_eval_eq M hM
    (__eo_list_concat (Term.UOp UserOp.concat) ys
      (bvConcatPullupConcat z (Term.Binary 0 0))) (wys + (wz + 0))
    hHighRawList hHighRawTy
  have hFullEq := pullup_list_concat_eq_rec (Term.UOp UserOp.concat) ys
    (bvConcatPullupConcat z
      (bvConcatPullupConcat y (Term.Binary 0 0))) hYsList hZYEmptyList
  have hHighEq := pullup_list_concat_eq_rec (Term.UOp UserOp.concat) ys
    (bvConcatPullupConcat z (Term.Binary 0 0)) hYsList hZEmptyList
  rw [hHighEq] at hElim
  unfold bvConcatPullup1ConcatZYs bvConcatPullup1ConcatZs
  rw [hFullEq, hHighEq]
  rw [hRec]
  change __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat_rec ys
          (bvConcatPullupConcat z (Term.Binary 0 0)))))
      (__smtx_model_eval M (__eo_to_smt y)) =
    __smtx_model_eval_concat
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat)
            (__eo_list_concat_rec ys
              (bvConcatPullupConcat z (Term.Binary 0 0))))))
      (__smtx_model_eval M (__eo_to_smt y))
  rw [hElim]

theorem bvConcatPullup1ExtractTypesNonStuck
    (op : BvConcatPullupOp) (xs ws y z ys nxm ny nym : Term) :
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __eo_typeof (bvConcatPullup1High op xs ws nxm ny) ≠ Term.Stuck ∧
    __eo_typeof (bvConcatPullup1Low op xs ws nym) ≠ Term.Stuck ∧
    __eo_nil op.term
        (__eo_typeof (bvConcatPullup1High op xs ws nxm ny)) ≠
      Term.Stuck ∧
    __eo_nil op.term
        (__eo_typeof (bvConcatPullup1Low op xs ws nym)) ≠
      Term.Stuck := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup1Lhs op xs ws y z ys))
    (__eo_typeof (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup1Term] at hsimpa ⊢); exact hsimpa)
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highTail := op.apply (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := Term.Apply (Term.Apply op.term y)
    (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  let lowConcat := bvConcatPullupConcat lowPart (Term.Binary 0 0)
  have hOuter : __eo_typeof_concat (__eo_typeof highPart)
      (__eo_typeof lowConcat) ≠ Term.Stuck := by
    have hsimpa := hSides.2
    try simp [bvConcatPullup1Rhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hOuter with
    ⟨wh, wl, hHighPartTy, hLowConcatTy⟩
  have hLowOuter : __eo_typeof_concat (__eo_typeof lowPart)
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hNe : __eo_typeof lowConcat ≠ Term.Stuck := by
      rw [hLowConcatTy]
      intro h
      cases h
    have hsimpa := hNe
    try simp [lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hLowOuter with
    ⟨wlo, we, hLowPartTy, _⟩
  have hHighArgs := pullup_typeof_apply_args_of_result_bitvec op
    highExt highTail wh (by simpa [highPart] using hHighPartTy)
  have hLowArgs := pullup_typeof_apply_args_of_result_bitvec op
    lowExt lowTail wlo (by simpa [lowPart] using hLowPartTy)
  have hHighTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt)) wh
    (by simpa [highTail] using hHighArgs.2)
  have hLowTailArgs := pullup_typeof_apply_args_of_result_bitvec op y
    (__eo_nil op.term (__eo_typeof lowExt)) wlo
    (by simpa [lowTail, BvConcatPullupOp.apply] using hLowArgs.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show __eo_typeof highExt =
        Term.Apply (Term.UOp UserOp.BitVec) wh from hHighArgs.1]
    intro h
    cases h
  · rw [show __eo_typeof lowExt =
        Term.Apply (Term.UOp UserOp.BitVec) wlo from hLowArgs.1]
    intro h
    cases h
  · have h := hHighTailArgs.2
    intro hBad
    rw [hBad] at h
    cases h
  · have h := hLowTailArgs.2
    intro hBad
    rw [hBad] at h
    cases h

theorem bvConcatPullup1RhsEoContext
    (op : BvConcatPullupOp) (xs ws y z ys nxm ny nym : Term) :
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    ∃ wh wl : Term,
      __eo_typeof (bvConcatPullup1High op xs ws nxm ny) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof (bvConcatPullup1ConcatZs z ys) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup1High op xs ws nxm ny))) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof (bvConcatPullup1Low op xs ws nym) =
          Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup1Low op xs ws nym))) =
          Term.Apply (Term.UOp UserOp.BitVec) wl := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup1Lhs op xs ws y z ys))
    (__eo_typeof (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup1Term] at hsimpa ⊢); exact hsimpa)
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highTail := op.apply (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply y (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  let lowConcat := bvConcatPullupConcat lowPart (Term.Binary 0 0)
  have hOuter : __eo_typeof_concat (__eo_typeof highPart)
      (__eo_typeof lowConcat) ≠ Term.Stuck := by
    have hsimpa := hSides.2
    try simp [bvConcatPullup1Rhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hOuter with
    ⟨wh, _wlOuter, hHighPartTy, hLowConcatTy⟩
  have hLowOuter : __eo_typeof_concat (__eo_typeof lowPart)
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hNe : __eo_typeof lowConcat ≠ Term.Stuck := by
      rw [hLowConcatTy]
      intro h
      cases h
    have hsimpa := hNe
    try simp [lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hLowOuter with
    ⟨wl, _we, hLowPartTy, _hEmptyTy⟩
  have hHighArgs := pullup_typeof_apply_args_of_result_bitvec op
    highExt highTail wh (by simpa [highPart] using hHighPartTy)
  have hLowArgs := pullup_typeof_apply_args_of_result_bitvec op
    lowExt lowTail wl (by simpa [lowPart] using hLowPartTy)
  have hHighTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt)) wh
    (by simpa [highTail] using hHighArgs.2)
  have hLowTailArgs := pullup_typeof_apply_args_of_result_bitvec op y
    (__eo_nil op.term (__eo_typeof lowExt)) wl
    (by simpa [lowTail] using hLowArgs.2)
  exact ⟨wh, wl,
    by simpa [highExt] using hHighArgs.1,
    hHighTailArgs.1,
    by simpa [highExt] using hHighTailArgs.2,
    by simpa [lowExt] using hLowArgs.1,
    hLowTailArgs.1,
    by simpa [lowExt] using hLowTailArgs.2⟩

theorem bvConcatPullup1RhsSmtTypes
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (A B : Nat) :
    nxm = Term.Numeral (native_nat_to_int (A + B - 1)) ->
    ny = Term.Numeral (native_nat_to_int B) ->
    nym = Term.Numeral (native_nat_to_int (B - 1)) ->
    __eo_typeof (bvConcatPullupAggregate op xs ws) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (A + B))) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (A + B) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1ConcatZs z ys)) =
      SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec B ->
    0 < A -> 0 < B ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1High op xs ws nxm ny)) =
        SmtType.BitVec A ∧
      __eo_typeof (bvConcatPullup1High op xs ws nxm ny) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int A)) ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply (bvConcatPullup1ConcatZs z ys)
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullup1High op xs ws nxm ny))))) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt (bvConcatPullup1Low op xs ws nym)) =
        SmtType.BitVec B ∧
      __eo_typeof (bvConcatPullup1Low op xs ws nym) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int B)) ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply y
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullup1Low op xs ws nym))))) =
        SmtType.BitVec B := by
  intro hNxm hNy hNym hAggEoTy hAggTy hHighCompTy hYTy hAPos hBPos
    hBodyTy
  have hAB1 : 1 ≤ A + B := by omega
  have hB1 : 1 ≤ B := by omega
  have hHighWidthEq :
      native_zplus (native_zplus (native_nat_to_int (A + B - 1)) 1)
          (native_zneg (native_nat_to_int B)) =
        native_nat_to_int A := by
    change (↑(A + B - 1) : Int) + 1 + -↑B = ↑A
    rw [Int.ofNat_sub hAB1]
    push_cast
    omega
  have hLowWidthEq :
      native_zplus (native_zplus (native_nat_to_int (B - 1)) 1)
          (native_zneg 0) =
        native_nat_to_int B := by
    change (↑(B - 1) : Int) + 1 + -0 = ↑B
    rw [Int.ofNat_sub hB1]
    push_cast
    omega
  have hHighHi : native_zlt (native_nat_to_int (A + B - 1))
      (native_nat_to_int (A + B)) = true := by
    have hsimpa :=
      (show (↑(A + B - 1) : Int) < ↑(A + B) by
        exact_mod_cast (show A + B - 1 < A + B by omega))
    try simp [SmtEval.native_zlt, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hHighWidth : native_zlt 0
      (native_zplus (native_zplus (native_nat_to_int (A + B - 1)) 1)
        (native_zneg (native_nat_to_int B))) = true := by
    rw [hHighWidthEq]
    simpa [SmtEval.native_zlt, native_nat_to_int,
      Smtm.native_nat_to_int] using hAPos
  have hLowHi : native_zlt (native_nat_to_int (B - 1))
      (native_nat_to_int (A + B)) = true := by
    have hsimpa :=
      (show (↑(B - 1) : Int) < ↑(A + B) by
        exact_mod_cast (show B - 1 < A + B by omega))
    try simp [SmtEval.native_zlt, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hLowWidth : native_zlt 0
      (native_zplus (native_zplus (native_nat_to_int (B - 1)) 1)
        (native_zneg 0)) = true := by
    rw [hLowWidthEq]
    simpa [SmtEval.native_zlt, native_nat_to_int,
      Smtm.native_nat_to_int] using hBPos
  have hNatWidth0 : ∀ w : Nat,
      native_zleq 0 (native_nat_to_int w) = true := by
    intro w
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hNonStuck := bvConcatPullup1ExtractTypesNonStuck op
    xs ws y z ys nxm ny nym hBodyTy
  have hHighEoTy :
      __eo_typeof (bvConcatPullup1High op xs ws nxm ny) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int A)) := by
    rw [hNxm, hNy]
    have hContext := eo_typeof_extract_of_context
        (bvConcatPullupAggregate op xs ws)
        (native_nat_to_int (A + B))
        (native_nat_to_int (A + B - 1)) (native_nat_to_int B)
        hAggEoTy
        (hNatWidth0 B)
        hHighHi hHighWidth
    rw [hHighWidthEq] at hContext
    simpa [bvConcatPullup1High, bvConcatPullupExtract, bvExtractTerm] using
      hContext
  have hLowEoTy :
      __eo_typeof (bvConcatPullup1Low op xs ws nym) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int B)) := by
    rw [hNym]
    have hContext := eo_typeof_extract_of_context
        (bvConcatPullupAggregate op xs ws)
        (native_nat_to_int (A + B)) (native_nat_to_int (B - 1)) 0
        hAggEoTy
        (by simp [SmtEval.native_zleq])
        hLowHi hLowWidth
    rw [hLowWidthEq] at hContext
    simpa [bvConcatPullup1Low, bvConcatPullupExtract, bvExtractTerm] using
      hContext
  have hHighTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1High op xs ws nxm ny)) =
      SmtType.BitVec A := by
    rw [hNxm, hNy]
    have hContext := smt_typeof_extract_of_context
        (bvConcatPullupAggregate op xs ws)
        (native_nat_to_int (A + B))
        (native_nat_to_int (A + B - 1)) (native_nat_to_int B)
        (by have hsimpa := hAggTy; (try simp [native_int_to_nat, SmtEval.native_int_to_nat, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢); exact hsimpa)
        (hNatWidth0 (A + B))
        (hNatWidth0 B)
        hHighHi hHighWidth
    rw [hHighWidthEq] at hContext
    simpa [bvConcatPullup1High, bvConcatPullupExtract, bvExtractTerm,
      native_int_to_nat, SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int] using hContext
  have hLowTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1Low op xs ws nym)) =
      SmtType.BitVec B := by
    rw [hNym]
    have hContext := smt_typeof_extract_of_context
        (bvConcatPullupAggregate op xs ws)
        (native_nat_to_int (A + B)) (native_nat_to_int (B - 1)) 0
        (by have hsimpa := hAggTy; (try simp [native_int_to_nat, SmtEval.native_int_to_nat, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢); exact hsimpa)
        (hNatWidth0 (A + B))
        (by simp [SmtEval.native_zleq])
        hLowHi hLowWidth
    rw [hLowWidthEq] at hContext
    simpa [bvConcatPullup1Low, bvConcatPullupExtract, bvExtractTerm,
      native_int_to_nat, SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int] using hContext
  have hHighNilTy := pullup_generated_nil_smt_type op A (by
    simpa [hHighEoTy] using hNonStuck.2.2.1)
  have hLowNilTy := pullup_generated_nil_smt_type op B (by
    simpa [hLowEoTy] using hNonStuck.2.2.2)
  exact ⟨hHighTy, hHighEoTy,
    op.binarySmtType _ _ A hHighCompTy (by simpa [hHighEoTy] using hHighNilTy),
    hLowTy, hLowEoTy,
    op.binarySmtType _ _ B hYTy (by simpa [hLowEoTy] using hLowNilTy)⟩

theorem bvConcatPullup1RhsSmtTypesOfBody
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (A B : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1ConcatZs z ys)) =
      SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec B ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullup1High op xs ws nxm ny)) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply (bvConcatPullup1ConcatZs z ys)
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullup1High op xs ws nxm ny))))) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt (bvConcatPullup1Low op xs ws nym)) =
        SmtType.BitVec B ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply y
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullup1Low op xs ws nym))))) =
        SmtType.BitVec B := by
  intro hAggTrans hHighCompTy hYTy hBodyTy
  let agg := bvConcatPullupAggregate op xs ws
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highNil := __eo_nil op.term (__eo_typeof highExt)
  let lowNil := __eo_nil op.term (__eo_typeof lowExt)
  let highComp := bvConcatPullup1ConcatZs z ys
  have hEo := bvConcatPullup1RhsEoContext op
    xs ws y z ys nxm ny nym hBodyTy
  rcases hEo with ⟨wh, wl, hHighExtEo, hHighCompEo, hHighNilEo,
    hLowExtEo, hYEo, hLowNilEo⟩
  have hHighCompTrans : RuleProofs.eo_has_smt_translation highComp := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt highComp) = SmtType.BitVec A by
      simpa [highComp] using hHighCompTy]
    intro h
    cases h
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width highComp wh
      hHighCompTrans (by simpa [highComp] using hHighCompEo) with
    ⟨wi, hWh, hWi0, hHighCompRawTy⟩
  have hWiNat : native_int_to_nat wi = A := by
    rw [show __smtx_typeof (__eo_to_smt highComp) = SmtType.BitVec A by
      simpa [highComp] using hHighCompTy] at hHighCompRawTy
    injection hHighCompRawTy with h
    exact h.symm
  have hWi : wi = native_nat_to_int A := by
    have hRound := native_int_to_nat_roundtrip wi hWi0
    rw [hWiNat] at hRound
    exact hRound.symm
  have hHighExtConcrete : __eo_typeof highExt =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int A)) := by
    rw [show __eo_typeof highExt =
        Term.Apply (Term.UOp UserOp.BitVec) wh by
      simpa [highExt] using hHighExtEo, hWh, hWi]
  have hHighExtNe : __eo_typeof highExt ≠ Term.Stuck := by
    rw [hHighExtConcrete]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck agg nxm ny
      (by simpa [agg] using hAggTrans)
      (by simpa [highExt, agg, bvConcatPullup1High,
        bvConcatPullupExtract, bvExtractTerm] using hHighExtNe) with
    ⟨wH, hH, lH, _hAggEoH, hNxm, hNy, hwH0, hlH0, hhHw,
      hHighWidth, hAggSmtH⟩
  have hHighRawTy : __smtx_typeof (__eo_to_smt highExt) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_zplus hH 1) (native_zneg lH))) := by
    unfold highExt bvConcatPullup1High bvConcatPullupExtract
    rw [hNxm, hNy]
    simpa [agg, bvExtractTerm] using
      (smt_typeof_extract_of_context agg wH hH lH hAggSmtH hwH0 hlH0
        hhHw hHighWidth)
  have hHighExtMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation highExt (by
      rw [hHighRawTy]
      intro h
      cases h)
  have hHighExtTy : __smtx_typeof (__eo_to_smt highExt) =
      SmtType.BitVec A := by
    rw [hHighExtConcrete] at hHighExtMatch
    simpa [__eo_to_smt_type, native_ite, SmtEval.native_zleq,
      native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
      SmtEval.native_int_to_nat] using hHighExtMatch
  have hHighNilNe : highNil ≠ Term.Stuck := by
    have hHighNilEo' : __eo_typeof highNil =
        Term.Apply (Term.UOp UserOp.BitVec) wh := by
      simpa [highNil, highExt] using hHighNilEo
    intro h
    rw [h] at hHighNilEo'
    cases hHighNilEo'
  have hHighNilTy : __smtx_typeof (__eo_to_smt highNil) =
      SmtType.BitVec A := by
    simpa [highNil, hHighExtConcrete] using
      (pullup_generated_nil_smt_type op A (by
        simpa [highNil, hHighExtConcrete] using hHighNilNe))
  have hHighTailTy : __smtx_typeof
      (__eo_to_smt (op.apply highComp highNil)) = SmtType.BitVec A :=
    op.binarySmtType highComp highNil A
      (by simpa [highComp] using hHighCompTy) hHighNilTy
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hYTy]
    intro h
    cases h
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width y wl
      hYTrans hYEo with ⟨wj, hWl, hWj0, hYRawTy⟩
  have hWjNat : native_int_to_nat wj = B := by
    rw [hYTy] at hYRawTy
    injection hYRawTy with h
    exact h.symm
  have hWj : wj = native_nat_to_int B := by
    have hRound := native_int_to_nat_roundtrip wj hWj0
    rw [hWjNat] at hRound
    exact hRound.symm
  have hLowExtConcrete : __eo_typeof lowExt =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int B)) := by
    rw [show __eo_typeof lowExt =
        Term.Apply (Term.UOp UserOp.BitVec) wl by
      simpa [lowExt] using hLowExtEo, hWl, hWj]
  have hLowExtNe : __eo_typeof lowExt ≠ Term.Stuck := by
    rw [hLowExtConcrete]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck agg nym (Term.Numeral 0)
      (by simpa [agg] using hAggTrans)
      (by simpa [lowExt, agg, bvConcatPullup1Low,
        bvConcatPullupExtract, bvExtractTerm] using hLowExtNe) with
    ⟨wL, hL, lL, _hAggEoL, hNym, hZero, hwL0, hlL0, hhLw,
      hLowWidth, hAggSmtL⟩
  have hLowRawTy : __smtx_typeof (__eo_to_smt lowExt) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_zplus hL 1) (native_zneg lL))) := by
    unfold lowExt bvConcatPullup1Low bvConcatPullupExtract
    rw [hNym, hZero]
    simpa [agg, bvExtractTerm] using
      (smt_typeof_extract_of_context agg wL hL lL hAggSmtL hwL0 hlL0
        hhLw hLowWidth)
  have hLowExtMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation lowExt (by
      rw [hLowRawTy]
      intro h
      cases h)
  have hLowExtTy : __smtx_typeof (__eo_to_smt lowExt) =
      SmtType.BitVec B := by
    rw [hLowExtConcrete] at hLowExtMatch
    simpa [__eo_to_smt_type, native_ite, SmtEval.native_zleq,
      native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
      SmtEval.native_int_to_nat] using hLowExtMatch
  have hLowNilNe : lowNil ≠ Term.Stuck := by
    have hLowNilEo' : __eo_typeof lowNil =
        Term.Apply (Term.UOp UserOp.BitVec) wl := by
      simpa [lowNil, lowExt] using hLowNilEo
    intro h
    rw [h] at hLowNilEo'
    cases hLowNilEo'
  have hLowNilTy : __smtx_typeof (__eo_to_smt lowNil) =
      SmtType.BitVec B := by
    simpa [lowNil, hLowExtConcrete] using
      (pullup_generated_nil_smt_type op B (by
        simpa [lowNil, hLowExtConcrete] using hLowNilNe))
  have hLowTailTy : __smtx_typeof
      (__eo_to_smt (op.apply y lowNil)) = SmtType.BitVec B :=
    op.binarySmtType y lowNil B hYTy hLowNilTy
  exact ⟨by simpa [highExt] using hHighExtTy,
    by simpa [highComp, highNil, highExt] using hHighTailTy,
    by simpa [lowExt] using hLowExtTy,
    by simpa [lowNil, lowExt] using hLowTailTy⟩

theorem typed_bvConcatPullup1Term
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup1Prem2 nxm z y ys) ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatPullup1Term op xs ws y z ys nxm ny nym) := by
  intro hXsTrans hWsTrans hPrem2Bool hBodyTy
  rcases bvConcatPullup1Prem2Type nxm z y ys hPrem2Bool with
    ⟨wz, wy, wys, hZTy, hYTy, hYsTy⟩
  have hLists := bvConcatPullup1ListsOfBodyType op
    xs ws y z ys nxm ny nym hBodyTy
  have hConcatTypes := bvConcatPullup1ConcatTypes z y ys wz wy wys
    hLists.2.2 hZTy hYTy hYsTy
  have hBase := bvConcatPullup1BaseContextFromFull op
    xs ws y z ys nxm ny nym (wys + wz + wy) hXsTrans hWsTrans
    hConcatTypes.1 hBodyTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2.2]
    intro h
    cases h
  have hComponents := bvConcatPullup1RhsSmtTypesOfBody op
    xs ws y z ys nxm ny nym (wys + wz) wy hAggTrans
    hConcatTypes.2 hYTy hBodyTy
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highTail := op.apply (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply y (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  have hLhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1Lhs op xs ws y z ys)) =
      SmtType.BitVec (wys + wz + wy) := by
    exact bvConcatPullupListSmtType op xs ws
      (bvConcatPullup1ConcatZYs z y ys) (wys + wz + wy)
      hBase.1 hBase.2.1 hBase.2.2.2.1 hBase.2.2.2.2.1
      hConcatTypes.1
  have hHighPartTy : __smtx_typeof (__eo_to_smt highPart) =
      SmtType.BitVec (wys + wz) := by
    exact op.binarySmtType highExt highTail (wys + wz)
      (by simpa [highExt] using hComponents.1)
      (by simpa [highTail, highExt] using hComponents.2.1)
  have hLowPartTy : __smtx_typeof (__eo_to_smt lowPart) =
      SmtType.BitVec wy := by
    exact op.binarySmtType lowExt lowTail wy
      (by simpa [lowExt] using hComponents.2.2.1)
      (by simpa [lowTail, lowExt] using hComponents.2.2.2)
  have hLowConcatTy := bvConcat_term_smt_type lowPart (Term.Binary 0 0)
    wy 0 hLowPartTy bvConcat_empty_smt_type
  have hRhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)) =
      SmtType.BitVec (wys + wz + wy) := by
    have hOuter := bvConcat_term_smt_type highPart
      (bvConcatPullupConcat lowPart (Term.Binary 0 0))
      (wys + wz) (wy + 0) hHighPartTy
      (by have hsimpa := hLowConcatTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
    have hsimpa := hOuter
    try simp [bvConcatPullup1Rhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, Nat.add_assoc] at hsimpa ⊢
    exact hsimpa
  unfold bvConcatPullup1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvConcatPullup1Lhs op xs ws y z ys)
    (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)
    (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; intro h; cases h)

private theorem pullup_model_eval_eq_numeral_left
    (v : SmtValue) (n : native_Int) :
    __smtx_model_eval_eq v (SmtValue.Numeral n) =
      SmtValue.Boolean true ->
    v = SmtValue.Numeral n := by
  intro h
  exact (RuleProofs.smt_value_rel_iff_eq v (SmtValue.Numeral n) (by
    rintro ⟨r1, r2, _hLeft, hRight⟩
    cases hRight)).mp h

theorem bvConcatPullup1Prem1Eval
    (M : SmtModel) (ny y : Term) (wy : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    eo_interprets M (bvConcatPullup1Prem1 ny y) true ->
    __smtx_model_eval M (__eo_to_smt ny) =
      SmtValue.Numeral (native_nat_to_int wy) := by
  intro hYTy hPrem
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M ny
    (Term.Apply (Term.UOp UserOp._at_bvsize) y)
    (by simpa [bvConcatPullup1Prem1, bvConcatPullup1Prem1Raw] using hPrem)
  rw [bvConcat_eval_bvsize_of_smt_bitvec_nat M y wy hYTy] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup1Prem2Eval
    (M : SmtModel) (nxm z y ys : Term) (wz wy wys : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    eo_interprets M (bvConcatPullup1Prem2 nxm z y ys) true ->
    __smtx_model_eval M (__eo_to_smt nxm) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg 1)) := by
  intro hZTy hYTy hYsTy hPrem
  let full := bvConcatPullupConcat z (bvConcatPullupConcat y ys)
  have hTailTy := bvConcat_term_smt_type y ys wy wys hYTy hYsTy
  have hFullTy := bvConcat_term_smt_type z
    (bvConcatPullupConcat y ys) wz (wy + wys) hZTy
    (by have hsimpa := hTailTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M full
    (wz + (wy + wys)) (by have hsimpa := hFullTy; (try simp [full, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nxm
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) full)) (Term.Numeral 1))
    (by simpa [bvConcatPullup1Prem2, bvConcatPullup1Prem2Raw,
      bvConcatPullupConcat, full] using hPrem)
  have hRhsEval : __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) full))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg 1)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hSize]
    simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
      native_zneg]
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp._at_bvsize) full))
          (Term.Numeral 1))) = _ by
        have hsimpa := hRhsEval; (try simp at hsimpa ⊢); exact hsimpa] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup1Prem3Eval
    (M : SmtModel) (nym y : Term) (wy : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    eo_interprets M (bvConcatPullup1Prem3 nym y) true ->
    __smtx_model_eval M (__eo_to_smt nym) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int wy) (native_zneg 1)) := by
  intro hYTy hPrem
  have hSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M y wy hYTy
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nym
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) y)) (Term.Numeral 1))
    (by simpa [bvConcatPullup1Prem3, bvConcatPullup1Prem3Raw] using hPrem)
  have hRhsEval : __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int wy) (native_zneg 1)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hSize]
    simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
      native_zneg]
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp._at_bvsize) y))
          (Term.Numeral 1))) = _ by
        have hsimpa := hRhsEval; (try simp at hsimpa ⊢); exact hsimpa] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup1Indices
    (M : SmtModel) (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (wz wy wys : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (wys + wz + wy) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup1Prem1 ny y) true ->
    eo_interprets M (bvConcatPullup1Prem2 nxm z y ys) true ->
    eo_interprets M (bvConcatPullup1Prem3 nym y) true ->
    nxm = Term.Numeral
        (native_nat_to_int (wys + wz + wy - 1)) ∧
      ny = Term.Numeral (native_nat_to_int wy) ∧
      nym = Term.Numeral (native_nat_to_int (wy - 1)) ∧
      __eo_typeof (bvConcatPullupAggregate op xs ws) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (wys + wz + wy))) ∧
      0 < wys + wz ∧ 0 < wy := by
  intro hAggTrans hAggTy hZTy hYTy hYsTy hBodyTy hP1 hP2 hP3
  have hExtracts := bvConcatPullup1ExtractTypesNonStuck op
    xs ws y z ys nxm ny nym hBodyTy
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nxm ny hAggTrans
      (by simpa [bvConcatPullup1High, bvConcatPullupExtract, bvExtractTerm]
        using hExtracts.1) with
    ⟨wH, hH, lH, hAggEoH, hNxm, hNy, hwH0, hlH0, hhHw,
      hHighWidth, hAggSmtH⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nym (Term.Numeral 0) hAggTrans
      (by simpa [bvConcatPullup1Low, bvConcatPullupExtract, bvExtractTerm]
        using hExtracts.2.1) with
    ⟨wL, hL, lL, hAggEoL, hNym, hZero, hwL0, hlL0, hhLw,
      hLowWidth, hAggSmtL⟩
  have hWHNat : native_int_to_nat wH = wys + wz + wy := by
    rw [hAggTy] at hAggSmtH
    injection hAggSmtH with h
    exact h.symm
  have hWLNat : native_int_to_nat wL = wys + wz + wy := by
    rw [hAggTy] at hAggSmtL
    injection hAggSmtL with h
    exact h.symm
  have hWH : wH = native_nat_to_int (wys + wz + wy) := by
    have hRound := native_int_to_nat_roundtrip wH hwH0
    rw [hWHNat] at hRound
    exact hRound.symm
  have hWL : wL = native_nat_to_int (wys + wz + wy) := by
    have hRound := native_int_to_nat_roundtrip wL hwL0
    rw [hWLNat] at hRound
    exact hRound.symm
  have hLH : lH = native_nat_to_int wy := by
    have hEval := bvConcatPullup1Prem1Eval M ny y wy hYTy hP1
    rw [hNy] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hHHRaw : hH =
      native_zplus (native_nat_to_int (wz + (wy + wys)))
        (native_zneg 1) := by
    have hEval := bvConcatPullup1Prem2Eval M nxm z y ys wz wy wys
      hZTy hYTy hYsTy hP2
    rw [hNxm] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLLRaw : hL =
      native_zplus (native_nat_to_int wy) (native_zneg 1) := by
    have hEval := bvConcatPullup1Prem3Eval M nym y wy hYTy hP3
    rw [hNym] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLZero : lL = 0 := by
    injection hZero with h
    exact h.symm
  have hWyPos : 0 < wy := by
    rw [hLLRaw, hLZero] at hLowWidth
    have hIntRaw : (0 : Int) < (↑wy : Int) + -1 + 1 := by
      simpa [SmtEval.native_zlt, SmtEval.native_zplus,
        SmtEval.native_zneg, native_nat_to_int,
        Smtm.native_nat_to_int] using hLowWidth
    have hInt : (0 : Int) < (↑wy : Int) := by omega
    exact_mod_cast hInt
  have hHighPos : 0 < wys + wz := by
    rw [hHHRaw, hLH] at hHighWidth
    have hIntRaw : (0 : Int) <
        (↑wz : Int) + (↑wy + ↑wys) + -1 + 1 + -↑wy := by
      have hsimpa := hHighWidth
      try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hInt : (0 : Int) < (↑(wys + wz) : Int) := by
      push_cast
      omega
    exact_mod_cast hInt
  have hHH : hH = native_nat_to_int (wys + wz + wy - 1) := by
    rw [hHHRaw]
    change (↑(wz + (wy + wys)) : Int) + -1 =
      ↑(wys + wz + wy - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wys + wz + wy)]
    push_cast
    omega
  have hLL : hL = native_nat_to_int (wy - 1) := by
    rw [hLLRaw]
    change (↑wy : Int) + -1 = ↑(wy - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wy)]
    push_cast
    omega
  refine ⟨hNxm.trans (congrArg Term.Numeral hHH),
    hNy.trans (congrArg Term.Numeral hLH),
    hNym.trans (congrArg Term.Numeral hLL), ?_, hHighPos, hWyPos⟩
  rw [hAggEoH, hWH]

theorem eval_bvConcatPullup1
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (wz wy wys : Nat) :
    __eo_is_list op.term xs = Term.Boolean true ->
    __eo_is_list op.term ws = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ->
    PullupListTypeOrNil xs (wys + wz + wy) ->
    __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec (wys + wz + wy) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (wys + wz + wy) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    nxm = Term.Numeral (native_nat_to_int (wys + wz + wy - 1)) ->
    ny = Term.Numeral (native_nat_to_int wy) ->
    nym = Term.Numeral (native_nat_to_int (wy - 1)) ->
    __eo_typeof (bvConcatPullupAggregate op xs ws) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (wys + wz + wy))) ->
    0 < wys + wz -> 0 < wy ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatPullup1Lhs op xs ws y z ys)) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)) := by
  intro hXsList hWsList hYsList hXsType hWsTy hAggTy hZTy hYTy hYsTy
    hNxm hNy hNym hAggEoTy hAPos hBPos hBodyTy
  have hConcatTypes := bvConcatPullup1ConcatTypes z y ys wz wy wys
    hYsList hZTy hYTy hYsTy
  have hFullTy := hConcatTypes.1
  have hHighCompTy := hConcatTypes.2
  have hLhsEval := bvConcatPullupListEval M hM op xs ws
    (bvConcatPullup1ConcatZYs z y ys) (wys + wz + wy)
    hXsList hWsList hXsType hWsTy hFullTy
  have hRhsTypes := bvConcatPullup1RhsSmtTypes op
    xs ws y z ys nxm ny nym (wys + wz) wy hNxm hNy hNym
    (by simpa [Nat.add_assoc] using hAggEoTy)
    (by simpa [Nat.add_assoc] using hAggTy) hHighCompTy hYTy hAPos hBPos
    hBodyTy
  let agg := bvConcatPullupAggregate op xs ws
  let full := bvConcatPullup1ConcatZYs z y ys
  let highComp := bvConcatPullup1ConcatZs z ys
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highTail := op.apply highComp
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply y (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt agg)
      (wys + wz + wy) (by simpa [agg] using hAggTy) with
    ⟨pa, hAggEval, hAggCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt full)
      (wys + wz + wy) (by simpa [full] using hFullTy) with
    ⟨pf, hFullEval, hFullCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt highComp)
      (wys + wz) (by simpa [highComp] using hHighCompTy) with
    ⟨ph, hHighCompEval, hHighCompCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) wy hYTy with
    ⟨py, hYEval, hYCan⟩
  have hNatWidth0 : ∀ w : Nat,
      native_zleq 0 (native_nat_to_int w) = true := by
    intro w
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hW0 := hNatWidth0 (wys + wz + wy)
  have hA0 := hNatWidth0 (wys + wz)
  have hB0 := hNatWidth0 wy
  have hAggRange := bitvec_payload_range_of_canonical hW0 hAggCan
  have hFullRange := bitvec_payload_range_of_canonical hW0 hFullCan
  have hHighRange := bitvec_payload_range_of_canonical hA0 hHighCompCan
  have hYRange := bitvec_payload_range_of_canonical hB0 hYCan
  have hAgg0 : 0 ≤ pa := by exact hAggRange.1
  have hAgg1 : pa < (2 : Int) ^ (wys + wz + wy) := by
    have hsimpa := hAggRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hFull0 : 0 ≤ pf := by exact hFullRange.1
  have hFull1 : pf < (2 : Int) ^ (wys + wz + wy) := by
    have hsimpa := hFullRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hHigh0 : 0 ≤ ph := by exact hHighRange.1
  have hHigh1 : ph < (2 : Int) ^ (wys + wz) := by
    have hsimpa := hHighRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hY0 : 0 ≤ py := by exact hYRange.1
  have hY1 : py < (2 : Int) ^ wy := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hYRange.2
  have hFullRelation := bvConcatPullup1FullEval M hM z y ys wz wy wys
    hYsList hZTy hYTy hYsTy
  have hConcatEval : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat highComp y)) =
      __smtx_model_eval_concat
        (SmtValue.Binary ↑(wys + wz) ph) (SmtValue.Binary ↑wy py) := by
    change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt highComp))
      (__smtx_model_eval M (__eo_to_smt y)) = _
    rw [hHighCompEval, hYEval]
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hFullAsConcat :
      SmtValue.Binary ↑(wys + wz + wy) pf =
        __smtx_model_eval_concat
          (SmtValue.Binary ↑(wys + wz) ph)
          (SmtValue.Binary ↑wy py) := by
    calc
      _ = __smtx_model_eval M (__eo_to_smt full) := hFullEval.symm
      _ = __smtx_model_eval M
          (__eo_to_smt (bvConcatPullupConcat highComp y)) := by
            simpa [full, highComp] using hFullRelation
      _ = _ := hConcatEval
  have hFullHigh :
      __smtx_model_eval_extract
          (SmtValue.Numeral ↑(wys + wz + wy - 1))
          (SmtValue.Numeral ↑wy)
          (SmtValue.Binary ↑(wys + wz + wy) pf) =
        SmtValue.Binary ↑(wys + wz) ph := by
    rw [hFullAsConcat]
    exact bvConcat_extract_high_full_value (wys + wz) wy ph py
      hHigh0 hHigh1 hY0 hY1 hAPos
  have hFullLow :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wy - 1))
          (SmtValue.Numeral 0)
          (SmtValue.Binary ↑(wys + wz + wy) pf) =
        SmtValue.Binary ↑wy py := by
    rw [hFullAsConcat]
    exact bvConcat_extract_low_full_value (wys + wz) wy ph py
      hHigh0 hHigh1 hY0 hY1 hBPos
  have hHighExtEval : __smtx_model_eval M (__eo_to_smt highExt) =
      __smtx_model_eval_extract
        (SmtValue.Numeral ↑(wys + wz + wy - 1))
        (SmtValue.Numeral ↑wy)
        (SmtValue.Binary ↑(wys + wz + wy) pa) := by
    unfold highExt bvConcatPullup1High bvConcatPullupExtract
    rw [hNxm, hNy]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (wys + wz + wy - 1)))
          (SmtTerm.Numeral (native_nat_to_int wy))
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hLowExtEval : __smtx_model_eval M (__eo_to_smt lowExt) =
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wy - 1))
        (SmtValue.Numeral 0)
        (SmtValue.Binary ↑(wys + wz + wy) pa) := by
    unfold lowExt bvConcatPullup1Low bvConcatPullupExtract
    rw [hNym]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (wy - 1)))
          (SmtTerm.Numeral 0)
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hHighTailEval : __smtx_model_eval M (__eo_to_smt highTail) =
      __smtx_model_eval M (__eo_to_smt highComp) := by
    exact bvConcatPullupEvalApplyGeneratedNil M hM op highComp
      (__eo_typeof highExt) (wys + wz) (wys + wz)
      (by simpa [highExt] using hRhsTypes.2.1)
      (by simpa [highComp] using hHighCompTy)
      (by simpa [highTail] using hRhsTypes.2.2.1)
  have hLowTailEval : __smtx_model_eval M (__eo_to_smt lowTail) =
      __smtx_model_eval M (__eo_to_smt y) := by
    exact bvConcatPullupEvalApplyGeneratedNil M hM op y
      (__eo_typeof lowExt) wy wy
      (by simpa [lowExt] using hRhsTypes.2.2.2.2.1)
      hYTy (by simpa [lowTail] using hRhsTypes.2.2.2.2.2)
  have hHighPartEval : __smtx_model_eval M (__eo_to_smt highPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt highExt))
        (__smtx_model_eval M (__eo_to_smt highComp)) := by
    rw [show __smtx_model_eval M (__eo_to_smt highPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highTail)) by
      simpa [highPart] using op.evalApply M highExt highTail]
    rw [hHighTailEval]
  have hLowPartEval : __smtx_model_eval M (__eo_to_smt lowPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
        (__smtx_model_eval M (__eo_to_smt y)) := by
    rw [show __smtx_model_eval M (__eo_to_smt lowPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt lowTail)) by
      simpa [lowPart] using op.evalApply M lowExt lowTail]
    rw [hLowTailEval]
  have hLowPartTy := op.binarySmtType lowExt lowTail wy
    (by simpa [lowExt] using hRhsTypes.2.2.2.1)
    (by simpa [lowTail] using hRhsTypes.2.2.2.2.2)
  have hLowEmpty := bvConcat_eval_right_empty M hM lowPart wy
    (by simpa [lowPart] using hLowPartTy)
  have hLowEmpty' : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt lowPart) := by
    simpa [bvConcatPullupConcat, bvConcatTerm] using hLowEmpty
  have hRhsEval : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)) =
      __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highComp)))
        (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt y))) := by
    change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt highPart))
      (__smtx_model_eval M
        (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0)))) = _
    rw [hHighPartEval, hLowEmpty', hLowPartEval]
  have hSplit := op.splitValue (wys + wz + wy) wy pa pf
    hAgg0 hAgg1 hFull0 hFull1 (by omega) (by omega)
  calc
    _ = op.eval
        (__smtx_model_eval M (__eo_to_smt agg))
        (__smtx_model_eval M (__eo_to_smt full)) := by
          have hsimpa := hLhsEval
          try simp [bvConcatPullup1Lhs, agg, full] at hsimpa ⊢
          exact hsimpa
    _ = op.eval (SmtValue.Binary ↑(wys + wz + wy) pa)
        (SmtValue.Binary ↑(wys + wz + wy) pf) := by
          rw [hAggEval, hFullEval]
          simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hSplit
    _ = __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highComp)))
        (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt y))) := by
          rw [hHighExtEval, hFullHigh, hHighCompEval,
            hLowExtEval, hFullLow, hYEval]
          simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hRhsEval.symm

theorem facts_bvConcatPullup1Term
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup1Prem2 nxm z y ys) ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup1Prem1 ny y) true ->
    eo_interprets M (bvConcatPullup1Prem2 nxm z y ys) true ->
    eo_interprets M (bvConcatPullup1Prem3 nym y) true ->
    eo_interprets M
      (bvConcatPullup1Term op xs ws y z ys nxm ny nym) true := by
  intro hXsTrans hWsTrans hPrem2Bool hBodyTy hP1 hP2 hP3
  rcases bvConcatPullup1Prem2Type nxm z y ys hPrem2Bool with
    ⟨wz, wy, wys, hZTy, hYTy, hYsTy⟩
  have hLists := bvConcatPullup1ListsOfBodyType op
    xs ws y z ys nxm ny nym hBodyTy
  have hConcatTypes := bvConcatPullup1ConcatTypes z y ys wz wy wys
    hLists.2.2 hZTy hYTy hYsTy
  have hBase := bvConcatPullup1BaseContextFromFull op
    xs ws y z ys nxm ny nym (wys + wz + wy) hXsTrans hWsTrans
    hConcatTypes.1 hBodyTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2.2]
    intro h
    cases h
  have hIndices := bvConcatPullup1Indices M op
    xs ws y z ys nxm ny nym wz wy wys hAggTrans
    hBase.2.2.2.2.2 hZTy hYTy hYsTy hBodyTy hP1 hP2 hP3
  have hRhsTypes := bvConcatPullup1RhsSmtTypes op
    xs ws y z ys nxm ny nym (wys + wz) wy
    hIndices.1 hIndices.2.1 hIndices.2.2.1
    (by simpa [Nat.add_assoc] using hIndices.2.2.2.1)
    (by simpa [Nat.add_assoc] using hBase.2.2.2.2.2)
    hConcatTypes.2 hYTy hIndices.2.2.2.2.1 hIndices.2.2.2.2.2
    hBodyTy
  let highExt := bvConcatPullup1High op xs ws nxm ny
  let lowExt := bvConcatPullup1Low op xs ws nym
  let highTail := op.apply (bvConcatPullup1ConcatZs z ys)
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply y (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  have hLhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1Lhs op xs ws y z ys)) =
      SmtType.BitVec (wys + wz + wy) := by
    exact bvConcatPullupListSmtType op xs ws
      (bvConcatPullup1ConcatZYs z y ys) (wys + wz + wy)
      hBase.1 hBase.2.1 hBase.2.2.2.1 hBase.2.2.2.2.1
      hConcatTypes.1
  have hHighPartTy : __smtx_typeof (__eo_to_smt highPart) =
      SmtType.BitVec (wys + wz) := by
    exact op.binarySmtType highExt highTail (wys + wz)
      (by simpa [highExt] using hRhsTypes.1)
      (by simpa [highTail, highExt] using hRhsTypes.2.2.1)
  have hLowPartTy : __smtx_typeof (__eo_to_smt lowPart) =
      SmtType.BitVec wy := by
    exact op.binarySmtType lowExt lowTail wy
      (by simpa [lowExt] using hRhsTypes.2.2.2.1)
      (by simpa [lowTail, lowExt] using hRhsTypes.2.2.2.2.2)
  have hLowConcatTy := bvConcat_term_smt_type lowPart (Term.Binary 0 0)
    wy 0 hLowPartTy bvConcat_empty_smt_type
  have hRhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)) =
      SmtType.BitVec (wys + wz + wy) := by
    have hOuter := bvConcat_term_smt_type highPart
      (bvConcatPullupConcat lowPart (Term.Binary 0 0))
      (wys + wz) (wy + 0) hHighPartTy
      (by have hsimpa := hLowConcatTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
    have hsimpa := hOuter
    try simp [bvConcatPullup1Rhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, Nat.add_assoc] at hsimpa ⊢
    exact hsimpa
  have hEqBool := RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvConcatPullup1Lhs op xs ws y z ys)
    (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym)
    (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; intro h; cases h)
  unfold bvConcatPullup1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [eval_bvConcatPullup1 M hM op xs ws y z ys nxm ny nym wz wy wys
      hBase.1 hBase.2.1 hLists.2.2 hBase.2.2.2.1
      hBase.2.2.2.2.1 hBase.2.2.2.2.2 hZTy hYTy hYsTy
      hIndices.1 hIndices.2.1 hIndices.2.2.1 hIndices.2.2.2.1
      hIndices.2.2.2.2.1 hIndices.2.2.2.2.2 hBodyTy]
    exact RuleProofs.smt_value_rel_refl _

theorem bvConcatPullup1ProgramProperties
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation ny ->
    RuleProofs.eo_has_smt_translation nym ->
    RuleProofs.eo_has_bool_type P1 ->
    RuleProofs.eo_has_bool_type P2 ->
    RuleProofs.eo_has_bool_type P3 ->
    __eo_typeof
        (bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3) =
      Term.Bool ->
    StepRuleProperties M [P1, P2, P3]
      (bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3) := by
  intro hXsTrans hWsTrans hYTrans hZTrans hYsTrans hNxmTrans hNyTrans
    hNymTrans hP1Bool hP2Bool hP3Bool hResultTy
  have hProg : bvConcatPullup1Program op xs ws y z ys nxm ny nym
      P1 P2 P3 ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  have hNorm := bvConcatPullup1Program_normalize op
    xs ws y z ys nxm ny nym P1 P2 P3 hXsTrans hWsTrans hYTrans
    hZTrans hYsTrans hNxmTrans hNyTrans hNymTrans hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmTrans
  have hNy := RuleProofs.term_ne_stuck_of_has_smt_translation ny hNyTrans
  have hNym := RuleProofs.term_ne_stuck_of_has_smt_translation nym hNymTrans
  have hProgramRaw :
      bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3 =
        bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym := by
    rw [hNorm.1, hNorm.2.1, hNorm.2.2]
    exact bvConcatPullup1Program_eq_raw op xs ws y z ys nxm ny nym
      hXs hWs hY hZ hYs hNxm hNy hNym
  have hRawNe : bvConcatPullup1BodyRaw op xs ws y z ys nxm ny nym ≠
      Term.Stuck := by
    rw [← hProgramRaw]
    exact hProg
  have hProgramTerm :
      bvConcatPullup1Program op xs ws y z ys nxm ny nym P1 P2 P3 =
        bvConcatPullup1Term op xs ws y z ys nxm ny nym :=
    hProgramRaw.trans
      (bvConcatPullup1BodyRaw_eq_term op xs ws y z ys nxm ny nym hRawNe)
  have hBodyTy : __eo_typeof
      (bvConcatPullup1Term op xs ws y z ys nxm ny nym) = Term.Bool := by
    rw [← hProgramTerm]
    exact hResultTy
  have hPrem2Bool : RuleProofs.eo_has_bool_type
      (bvConcatPullup1Prem2 nxm z y ys) := by
    rw [← hNorm.2.1]
    exact hP2Bool
  refine ⟨?_, ?_⟩
  · intro hPremEvidence
    have hP1True : eo_interprets M (bvConcatPullup1Prem1 ny y) true := by
      rw [← hNorm.1]
      exact hPremEvidence P1 (by simp)
    have hP2True : eo_interprets M
        (bvConcatPullup1Prem2 nxm z y ys) true := by
      rw [← hNorm.2.1]
      exact hPremEvidence P2 (by simp)
    have hP3True : eo_interprets M (bvConcatPullup1Prem3 nym y) true := by
      rw [← hNorm.2.2]
      exact hPremEvidence P3 (by simp)
    rw [hProgramTerm]
    exact facts_bvConcatPullup1Term M hM op
      xs ws y z ys nxm ny nym hXsTrans hWsTrans hPrem2Bool hBodyTy
      hP1True hP2True hP3True
  · rw [hProgramTerm]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_bvConcatPullup1Term op xs ws y z ys nxm ny nym
        hXsTrans hWsTrans hPrem2Bool hBodyTy)

/-! ## Two-segment concat pullup (the `pullup2` rules) -/

def bvConcatPullup2Full (z y ys : Term) : Term :=
  bvConcatPullupConcat z (bvConcatPullupConcat y ys)

def bvConcatPullup2LowComp (y ys : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (bvConcatPullupConcat y ys)

def bvConcatPullup2Prem1Raw
    (nyRef zRef yRef ysRef zSizeRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nyRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize)
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) zRef)
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) yRef) ysRef))))
      (Term.Apply (Term.UOp UserOp._at_bvsize) zSizeRef))

def bvConcatPullup2Prem2Raw (nxmRef zRef yRef ysRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nxmRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize)
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) zRef)
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) yRef) ysRef))))
      (Term.Numeral 1))

def bvConcatPullup2Prem3Raw
    (nymRef zRef yRef ysRef zSizeRef : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nymRef)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize)
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) zRef)
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) yRef) ysRef))))
        (Term.Apply (Term.UOp UserOp._at_bvsize) zSizeRef)))
      (Term.Numeral 1))

def bvConcatPullup2Prem1 (ny z y ys : Term) : Term :=
  bvConcatPullup2Prem1Raw ny z y ys z

def bvConcatPullup2Prem2 (nxm z y ys : Term) : Term :=
  bvConcatPullup2Prem2Raw nxm z y ys

def bvConcatPullup2Prem3 (nym z y ys : Term) : Term :=
  bvConcatPullup2Prem3Raw nym z y ys z

def bvConcatPullup2Program
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) : Term :=
  match op with
  | .band => __eo_prog_bv_and_concat_pullup2 xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
  | .bor => __eo_prog_bv_or_concat_pullup2 xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
  | .bxor => __eo_prog_bv_xor_concat_pullup2 xs ws y z ys nxm ny nym
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def bvConcatPullupTwoHigh
    (op : BvConcatPullupOp) (xs ws nxm ny : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nxm ny

def bvConcatPullupTwoLow
    (op : BvConcatPullupOp) (xs ws nym : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nym
    (Term.Numeral 0)

def bvConcatPullupTwoLhs
    (op : BvConcatPullupOp) (xs ws full : Term) : Term :=
  __eo_list_concat op.term xs (op.apply full ws)

def bvConcatPullupTwoRhs
    (op : BvConcatPullupOp) (xs ws highComp lowComp nxm ny nym : Term) :
    Term :=
  let highExt := bvConcatPullupTwoHigh op xs ws nxm ny
  let lowExt := bvConcatPullupTwoLow op xs ws nym
  bvConcatPullupConcat
    (op.apply highExt
      (op.apply highComp (__eo_nil op.term (__eo_typeof highExt))))
    (bvConcatPullupConcat
      (op.apply lowExt
        (op.apply lowComp (__eo_nil op.term (__eo_typeof lowExt))))
      (Term.Binary 0 0))

def bvConcatPullupTwoTerm
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvConcatPullupTwoLhs op xs ws full))
    (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym)

def bvConcatPullup2Term
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) : Term :=
  bvConcatPullupTwoTerm op xs ws (bvConcatPullup2Full z y ys) z
    (bvConcatPullup2LowComp y ys) nxm ny nym

private theorem pullup2_guard_refs
    {ny z y ys nxm nym
      nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2
      nymR zR4 yR3 ysR3 zR5 body : Term} :
    __eo_requires
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and
                        (__eo_and
                          (__eo_and
                            (__eo_and
                              (__eo_and (__eo_eq ny nyR) (__eo_eq z zR1))
                              (__eo_eq y yR1))
                            (__eo_eq ys ysR1))
                          (__eo_eq z zR2))
                        (__eo_eq nxm nxmR))
                      (__eo_eq z zR3))
                    (__eo_eq y yR2))
                  (__eo_eq ys ysR2))
                (__eo_eq nym nymR))
              (__eo_eq z zR4))
            (__eo_eq y yR3))
          (__eo_eq ys ysR3))
        (__eo_eq z zR5))
      (Term.Boolean true) body ≠ Term.Stuck ->
    nyR = ny ∧ zR1 = z ∧ yR1 = y ∧ ysR1 = ys ∧ zR2 = z ∧
      nxmR = nxm ∧ zR3 = z ∧ yR2 = y ∧ ysR2 = ys ∧ nymR = nym ∧
      zR4 = z ∧ yR3 = y ∧ ysR3 = ys ∧ zR5 = z := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  rcases pullup_and_true hGuard with ⟨h13, hz5⟩
  rcases pullup_and_true h13 with ⟨h12, hys3⟩
  rcases pullup_and_true h12 with ⟨h11, hy3⟩
  rcases pullup_and_true h11 with ⟨h10, hz4⟩
  rcases pullup_and_true h10 with ⟨h9, hnym⟩
  rcases pullup_and_true h9 with ⟨h8, hys2⟩
  rcases pullup_and_true h8 with ⟨h7, hy2⟩
  rcases pullup_and_true h7 with ⟨h6, hz3⟩
  rcases pullup_and_true h6 with ⟨h5, hnxm⟩
  rcases pullup_and_true h5 with ⟨h4, hz2⟩
  rcases pullup_and_true h4 with ⟨h3, hys1⟩
  rcases pullup_and_true h3 with ⟨h2, hy1⟩
  rcases pullup_and_true h2 with ⟨hny, hz1⟩
  exact ⟨support_eq_of_eo_eq_true ny nyR hny,
    support_eq_of_eo_eq_true z zR1 hz1,
    support_eq_of_eo_eq_true y yR1 hy1,
    support_eq_of_eo_eq_true ys ysR1 hys1,
    support_eq_of_eo_eq_true z zR2 hz2,
    support_eq_of_eo_eq_true nxm nxmR hnxm,
    support_eq_of_eo_eq_true z zR3 hz3,
    support_eq_of_eo_eq_true y yR2 hy2,
    support_eq_of_eo_eq_true ys ysR2 hys2,
    support_eq_of_eo_eq_true nym nymR hnym,
    support_eq_of_eo_eq_true z zR4 hz4,
    support_eq_of_eo_eq_true y yR3 hy3,
    support_eq_of_eo_eq_true ys ysR3 hys3,
    support_eq_of_eo_eq_true z zR5 hz5⟩


def BvConcatPullup2PremiseShape (P1 P2 P3 : Term) : Prop :=
  ∃ nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2
    nymR zR4 yR3 ysR3 zR5,
    P1 = bvConcatPullup2Prem1Raw nyR zR1 yR1 ysR1 zR2 ∧
    P2 = bvConcatPullup2Prem2Raw nxmR zR3 yR2 ysR2 ∧
    P3 = bvConcatPullup2Prem3Raw nymR zR4 yR3 ysR3 zR5

private theorem bvConcatPullup2_premise_shape
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> ys ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    ny ≠ Term.Stuck -> nym ≠ Term.Stuck ->
    bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3 ≠
      Term.Stuck ->
    BvConcatPullup2PremiseShape P1 P2 P3 := by
  intro hXs hWs hY hZ hYs hNxm hNy hNym hProg
  by_cases hShape : BvConcatPullup2PremiseShape P1 P2 P3
  · exact hShape
  · exfalso
    apply hProg
    cases op with
    | band =>
        exact __eo_prog_bv_and_concat_pullup2.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2
              nymR zR4 yR3 ysR3 zR5 hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            apply hShape
            exact ⟨nyR, zR1, yR1, ysR1, zR2, nxmR, zR3, yR2,
              ysR2, nymR, zR4, yR3, ysR3, zR5,
              by simpa [bvConcatPullup2Prem1Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP1',
              by simpa [bvConcatPullup2Prem2Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup2Prem3Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP3'⟩)
    | bor =>
        exact __eo_prog_bv_or_concat_pullup2.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2
              nymR zR4 yR3 ysR3 zR5 hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            apply hShape
            exact ⟨nyR, zR1, yR1, ysR1, zR2, nxmR, zR3, yR2,
              ysR2, nymR, zR4, yR3, ysR3, zR5,
              by simpa [bvConcatPullup2Prem1Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP1',
              by simpa [bvConcatPullup2Prem2Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup2Prem3Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP3'⟩)
    | bxor =>
        exact __eo_prog_bv_xor_concat_pullup2.eq_10
          xs ws y z ys nxm ny nym (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
          hXs hWs hY hZ hYs hNxm hNy hNym (by
            intro nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2
              nymR zR4 yR3 ysR3 zR5 hP1 hP2 hP3
            have hP1' := Proof.pf.inj hP1
            have hP2' := Proof.pf.inj hP2
            have hP3' := Proof.pf.inj hP3
            apply hShape
            exact ⟨nyR, zR1, yR1, ysR1, zR2, nxmR, zR3, yR2,
              ysR2, nymR, zR4, yR3, ysR3, zR5,
              by simpa [bvConcatPullup2Prem1Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP1',
              by simpa [bvConcatPullup2Prem2Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP2',
              by simpa [bvConcatPullup2Prem3Raw, bvConcatPullup2Full,
                bvConcatPullupConcat] using hP3'⟩)

theorem bvConcatPullup2Program_normalize
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation ny ->
    RuleProofs.eo_has_smt_translation nym ->
    bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvConcatPullup2Prem1 ny z y ys ∧
      P2 = bvConcatPullup2Prem2 nxm z y ys ∧
      P3 = bvConcatPullup2Prem3 nym z y ys := by
  intro hXsT hWsT hYT hZT hYsT hNxmT hNyT hNymT hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsT
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsT
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYT
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZT
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsT
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmT
  have hNy := RuleProofs.term_ne_stuck_of_has_smt_translation ny hNyT
  have hNym := RuleProofs.term_ne_stuck_of_has_smt_translation nym hNymT
  have hShape := bvConcatPullup2_premise_shape op xs ws y z ys nxm ny nym
    P1 P2 P3 hXs hWs hY hZ hYs hNxm hNy hNym hProg
  unfold BvConcatPullup2PremiseShape at hShape
  rcases hShape with
    ⟨nyR, zR1, yR1, ysR1, zR2, nxmR, zR3, yR2, ysR2,
      nymR, zR4, yR3, ysR3, zR5, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  cases op with
  | band =>
      simp only [bvConcatPullup2Program, bvConcatPullup2Prem1Raw,
        bvConcatPullup2Prem2Raw, bvConcatPullup2Prem3Raw,
        bvConcatPullup2Full, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_and_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2 nymR zR4 yR3 ysR3 zR5
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup2_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup2Prem1] using hP1,
        by simpa [bvConcatPullup2Prem2] using hP2,
        by simpa [bvConcatPullup2Prem3] using hP3⟩
  | bor =>
      simp only [bvConcatPullup2Program, bvConcatPullup2Prem1Raw,
        bvConcatPullup2Prem2Raw, bvConcatPullup2Prem3Raw,
        bvConcatPullup2Full, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_or_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2 nymR zR4 yR3 ysR3 zR5
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup2_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup2Prem1] using hP1,
        by simpa [bvConcatPullup2Prem2] using hP2,
        by simpa [bvConcatPullup2Prem3] using hP3⟩
  | bxor =>
      simp only [bvConcatPullup2Program, bvConcatPullup2Prem1Raw,
        bvConcatPullup2Prem2Raw, bvConcatPullup2Prem3Raw,
        bvConcatPullup2Full, bvConcatPullupConcat] at hReq
      rw [__eo_prog_bv_xor_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        nyR zR1 yR1 ysR1 zR2 nxmR zR3 yR2 ysR2 nymR zR4 yR3 ysR3 zR5
        hXs hWs hY hZ hYs hNxm hNy hNym] at hReq
      rcases pullup2_guard_refs hReq with
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl⟩
      exact ⟨by simpa [bvConcatPullup2Prem1] using hP1,
        by simpa [bvConcatPullup2Prem2] using hP2,
        by simpa [bvConcatPullup2Prem3] using hP3⟩

def bvConcatPullupTwoHighRaw
    (op : BvConcatPullupOp) (xs ws nxm ny : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nxm ny)
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullupTwoLowRaw
    (op : BvConcatPullupOp) (xs ws nym : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nym (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullupTwoLhsRaw
    (op : BvConcatPullupOp) (xs ws full : Term) : Term :=
  __eo_list_concat op.term xs
    (__eo_mk_apply (__eo_mk_apply op.term full) ws)

def bvConcatPullupTwoRhsRaw
    (op : BvConcatPullupOp)
    (xs ws highComp lowComp nxm ny nym : Term) : Term :=
  let highExt := bvConcatPullupTwoHighRaw op xs ws nxm ny
  let lowExt := bvConcatPullupTwoLowRaw op xs ws nym
  let high := __eo_mk_apply (__eo_mk_apply op.term highExt)
    (__eo_mk_apply (__eo_mk_apply op.term highComp)
      (__eo_nil op.term (__eo_typeof highExt)))
  let low := __eo_mk_apply (__eo_mk_apply op.term lowExt)
    (__eo_mk_apply (__eo_mk_apply op.term lowComp)
      (__eo_nil op.term (__eo_typeof lowExt)))
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) high)
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) low)
      (Term.Binary 0 0))

def bvConcatPullupTwoBodyRaw
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (bvConcatPullupTwoLhsRaw op xs ws full))
    (bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym)

private theorem bvConcatPullupTwoLhsRaw_eq
    (op : BvConcatPullupOp) (xs ws full : Term) :
    bvConcatPullupTwoLhsRaw op xs ws full ≠ Term.Stuck ->
    bvConcatPullupTwoLhsRaw op xs ws full =
      bvConcatPullupTwoLhs op xs ws full := by
  intro hLhs
  let head := __eo_mk_apply op.term full
  let tail := __eo_mk_apply head ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullupTwoLhsRaw, head, tail] using hLhs)
  have hTail : tail ≠ Term.Stuck :=
    pullup_term_ne_stuck_of_is_list_true op.term tail hLists.2
  have hHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck head ws hTail
  have hHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term full hHead
  have hTailEq := eo_mk_apply_eq_apply_of_ne_stuck head ws hTail
  calc
    bvConcatPullupTwoLhsRaw op xs ws full =
        __eo_list_concat op.term xs tail := by rfl
    _ = __eo_list_concat op.term xs (op.apply full ws) := by
      dsimp [tail, head, BvConcatPullupOp.apply] at hTailEq hHeadEq ⊢
      rw [hTailEq, hHeadEq]
    _ = bvConcatPullupTwoLhs op xs ws full := by rfl

private theorem bvConcatPullupTwoRhsRaw_eq
    (op : BvConcatPullupOp)
    (xs ws highComp lowComp nxm ny nym : Term) :
    bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym ≠
      Term.Stuck ->
    bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym =
      bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym := by
  intro hRhs
  let hiR := bvConcatPullupTwoHighRaw op xs ws nxm ny
  let loR := bvConcatPullupTwoLowRaw op xs ws nym
  let hiTailHead := __eo_mk_apply op.term highComp
  let hiTail := __eo_mk_apply hiTailHead
    (__eo_nil op.term (__eo_typeof hiR))
  let hiHead := __eo_mk_apply op.term hiR
  let hi := __eo_mk_apply hiHead hiTail
  let loTailHead := __eo_mk_apply op.term lowComp
  let loTail := __eo_mk_apply loTailHead
    (__eo_nil op.term (__eo_typeof loR))
  let loHead := __eo_mk_apply op.term loR
  let lo := __eo_mk_apply loHead loTail
  let loConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) lo
  let loConcat := __eo_mk_apply loConcatHead (Term.Binary 0 0)
  let hiConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) hi
  have hRhs' : __eo_mk_apply hiConcatHead loConcat ≠ Term.Stuck := by
    simpa [bvConcatPullupTwoRhsRaw, hiR, loR, hiTailHead, hiTail,
      hiHead, hi, loTailHead, loTail, loHead, lo, loConcatHead,
      loConcat, hiConcatHead] using hRhs
  have hHiConcatHead :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hiConcatHead loConcat hRhs'
  have hLoConcat :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck hiConcatHead loConcat hRhs'
  have hHi := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hLoConcatHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    loConcatHead (Term.Binary 0 0) hLoConcat
  have hLo := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hHiHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term hiR hHiHead
  have hHiTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hLoHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term loR hLoHead
  have hLoTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck loTailHead
    (__eo_nil op.term (__eo_typeof loR)) hLoTail
  have hHiREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nxm ny)
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hHiR; (try simp [hiR] at hsimpa ⊢); exact hsimpa)
  have hLoREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nym (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hLoR; (try simp [loR] at hsimpa ⊢); exact hsimpa)
  have hHiTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term
    highComp hHiTailHead
  have hHiTailEq := eo_mk_apply_eq_apply_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hHiHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term hiR hHiHead
  have hHiEq := eo_mk_apply_eq_apply_of_ne_stuck hiHead hiTail hHi
  have hLoTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term
    lowComp hLoTailHead
  have hLoTailEq := eo_mk_apply_eq_apply_of_ne_stuck loTailHead
    (__eo_nil op.term (__eo_typeof loR)) hLoTail
  have hLoHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term loR hLoHead
  have hLoEq := eo_mk_apply_eq_apply_of_ne_stuck loHead loTail hLo
  have hLoConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hLoConcatEq := eo_mk_apply_eq_apply_of_ne_stuck loConcatHead
    (Term.Binary 0 0) hLoConcat
  have hHiConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hRhsEq := eo_mk_apply_eq_apply_of_ne_stuck hiConcatHead loConcat hRhs'
  dsimp [bvConcatPullupTwoRhsRaw, bvConcatPullupTwoHighRaw,
    bvConcatPullupTwoLowRaw, hiR, loR, hiTailHead, hiTail,
    hiHead, hi, loTailHead, loTail, loHead, lo, loConcatHead,
    loConcat, hiConcatHead] at *
  simp only [hHiREq, hLoREq] at *
  rw [hRhsEq, hHiConcatHeadEq, hHiEq, hHiHeadEq,
    hHiTailEq, hHiTailHeadEq, hLoConcatEq, hLoConcatHeadEq,
    hLoEq, hLoHeadEq, hLoTailEq, hLoTailHeadEq]
  rfl

theorem bvConcatPullupTwoBodyRaw_eq_term
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) :
    bvConcatPullupTwoBodyRaw op xs ws full highComp lowComp nxm ny nym ≠
      Term.Stuck ->
    bvConcatPullupTwoBodyRaw op xs ws full highComp lowComp nxm ny nym =
      bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym := by
  intro hBody
  let lhsR := bvConcatPullupTwoLhsRaw op xs ws full
  let rhsR := bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhsR
  have hBody' : __eo_mk_apply eqHead rhsR ≠ Term.Stuck := by
    simpa [bvConcatPullupTwoBodyRaw, lhsR, rhsR, eqHead] using hBody
  have hEqHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hRhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hLhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hLhsEq := bvConcatPullupTwoLhsRaw_eq op xs ws full hLhs
  have hRhsEq := bvConcatPullupTwoRhsRaw_eq op xs ws highComp lowComp
    nxm ny nym hRhs
  have hHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck eqHead rhsR hBody'
  dsimp [lhsR, rhsR, eqHead] at hLhsEq hRhsEq hHeadEq hOuterEq ⊢
  calc
    bvConcatPullupTwoBodyRaw op xs ws full highComp lowComp nxm ny nym =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.eq)
            (bvConcatPullupTwoLhsRaw op xs ws full))
          (bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym) :=
      by rfl
    _ = Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (bvConcatPullupTwoLhsRaw op xs ws full))
          (bvConcatPullupTwoRhsRaw op xs ws highComp lowComp nxm ny nym) := by
      rw [hOuterEq, hHeadEq]
    _ = bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym := by
      rw [hLhsEq, hRhsEq]
      rfl

theorem bvConcatPullup2Program_eq_raw
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> ys ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    ny ≠ Term.Stuck -> nym ≠ Term.Stuck ->
    bvConcatPullup2Program op xs ws y z ys nxm ny nym
        (bvConcatPullup2Prem1 ny z y ys)
        (bvConcatPullup2Prem2 nxm z y ys)
        (bvConcatPullup2Prem3 nym z y ys) =
      bvConcatPullupTwoBodyRaw op xs ws (bvConcatPullup2Full z y ys) z
        (bvConcatPullup2LowComp y ys) nxm ny nym := by
  intro hXs hWs hY hZ hYs hNxm hNy hNym
  cases op with
  | band =>
      unfold bvConcatPullup2Program bvConcatPullup2Prem1
        bvConcatPullup2Prem2 bvConcatPullup2Prem3
        bvConcatPullup2Prem1Raw bvConcatPullup2Prem2Raw
        bvConcatPullup2Prem3Raw bvConcatPullup2Full bvConcatPullupConcat
      rw [__eo_prog_bv_and_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        ny z y ys z nxm z y ys nym z y ys z
        hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullupTwoBodyRaw, bvConcatPullupTwoLhsRaw,
        bvConcatPullupTwoRhsRaw, bvConcatPullupTwoHighRaw,
        bvConcatPullupTwoLowRaw, bvConcatPullup2LowComp,
        bvConcatPullupConcat,
        bvConcatPullupAggregate, BvConcatPullupOp.term,
        __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]
  | bor =>
      unfold bvConcatPullup2Program bvConcatPullup2Prem1
        bvConcatPullup2Prem2 bvConcatPullup2Prem3
        bvConcatPullup2Prem1Raw bvConcatPullup2Prem2Raw
        bvConcatPullup2Prem3Raw bvConcatPullup2Full bvConcatPullupConcat
      rw [__eo_prog_bv_or_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        ny z y ys z nxm z y ys nym z y ys z
        hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullupTwoBodyRaw, bvConcatPullupTwoLhsRaw,
        bvConcatPullupTwoRhsRaw, bvConcatPullupTwoHighRaw,
        bvConcatPullupTwoLowRaw, bvConcatPullup2LowComp,
        bvConcatPullupConcat,
        bvConcatPullupAggregate, BvConcatPullupOp.term,
        __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]
  | bxor =>
      unfold bvConcatPullup2Program bvConcatPullup2Prem1
        bvConcatPullup2Prem2 bvConcatPullup2Prem3
        bvConcatPullup2Prem1Raw bvConcatPullup2Prem2Raw
        bvConcatPullup2Prem3Raw bvConcatPullup2Full bvConcatPullupConcat
      rw [__eo_prog_bv_xor_concat_pullup2.eq_9 xs ws y z ys nxm ny nym
        ny z y ys z nxm z y ys nym z y ys z
        hXs hWs hY hZ hYs hNxm hNy hNym]
      simp [bvConcatPullupTwoBodyRaw, bvConcatPullupTwoLhsRaw,
        bvConcatPullupTwoRhsRaw, bvConcatPullupTwoHighRaw,
        bvConcatPullupTwoLowRaw, bvConcatPullup2LowComp,
        bvConcatPullupConcat,
        bvConcatPullupAggregate, BvConcatPullupOp.term,
        __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, SmtEval.native_and,
        hXs, hWs, hY, hZ, hYs, hNxm, hNy, hNym]

theorem bvConcatPullupTwoListsOfBodyType
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) :
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullupTwoLhs op xs ws full))
    (__eo_typeof
      (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullupTwoTerm] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullupTwoLhs op xs ws full ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullupTwoLhs, tail] using hLhsNe)
  exact ⟨hLists.1,
    eo_is_list_tail_true_of_cons_self op.term full ws hLists.2⟩

theorem bvConcatPullupTwoBaseContextFromFull
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) (w : Nat) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w ->
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true ∧
      PullupListTypeOrNil xs w ∧
      __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
        SmtType.BitVec w := by
  intro hXsTrans hWsTrans hFullTy hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullupTwoLhs op xs ws full))
    (__eo_typeof
      (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullupTwoTerm] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullupTwoLhs op xs ws full ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullupTwoLhs, tail] using hLhsNe)
  have hXsList := hLists.1
  have hTailList := hLists.2
  have hWsList : __eo_is_list op.term ws = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op.term full ws hTailList
  have hRecTypeNe : __eo_typeof (__eo_list_concat_rec xs tail) ≠
      Term.Stuck := by
    rw [← pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
    simpa [bvConcatPullupTwoLhs, tail] using hSides.1
  have hTailTypeNe := pullup_list_concat_rec_right_type_non_stuck op xs tail
    hXsList hRecTypeNe
  have hTailTypeNe' :
      __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) ≠
        Term.Stuck := by
    rw [← pullup_typeof_apply op]
    exact hTailTypeNe
  rcases pullup_typeof_bvand_arg_types_of_ne_stuck hTailTypeNe' with
    ⟨width, hFullEoTy, hWsEoTy⟩
  have hFullMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
    full (by rw [hFullTy]; simp)
  have hWidthTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) width) =
        SmtType.BitVec w := by
    rw [hFullEoTy] at hFullMatch
    exact hFullMatch.symm.trans hFullTy
  have hWsMatch := TranslationProofs.eo_to_smt_typeof_matches_translation ws
    hWsTrans
  have hWsTy : __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w := by
    rw [hWsEoTy] at hWsMatch
    exact hWsMatch.trans hWidthTy
  have hTailEoTy :
      __eo_typeof tail = Term.Apply (Term.UOp UserOp.BitVec) width := by
    have hReduced :
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) =
          Term.Apply (Term.UOp UserOp.BitVec) width := by
      rw [hFullEoTy, hWsEoTy]
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        subst width
        simp [__eo_to_smt_type] at hWidthTy
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
    rw [show __eo_typeof tail =
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) by
      simpa [tail] using pullup_typeof_apply op full ws]
    exact hReduced
  have hRecEoTy := pullup_list_concat_rec_result_eo_type op xs tail width
    hXsList hTailEoTy hRecTypeNe
  have hTailNe : tail ≠ Term.Stuck := by
    simp [tail, BvConcatPullupOp.apply]
  have hXsType := pullup_list_type_or_nil_of_concat_eo_type op xs tail
    width w hXsTrans hXsList hTailNe hRecEoTy hWidthTy
  let c := __eo_list_concat op.term xs ws
  have hCList : __eo_is_list op.term c = Term.Boolean true := by
    dsimp [c]
    rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
    exact eo_list_concat_rec_is_list_true_of_lists op.term xs ws
      hXsList hWsList
  have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
    rcases hXsType with hXsTy | hXsNil
    · dsimp [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact op.listConcatRecSmtType xs ws w hXsList hWsList hXsTy hWsTy
    · have hCeq : c = ws := by
        dsimp [c]
        rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList,
          hXsNil ws]
      rw [hCeq]
      exact hWsTy
  have hAggTy := op.listSingletonElimSmtType c w hCList hCTy
  exact ⟨hXsList, hWsList, hXsType, hWsTy,
    by simpa [bvConcatPullupAggregate, c] using hAggTy⟩

theorem bvConcatPullupTwoRhsEoContext
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) :
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    ∃ wh wl : Term,
      __eo_typeof (bvConcatPullupTwoHigh op xs ws nxm ny) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof highComp = Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullupTwoHigh op xs ws nxm ny))) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof (bvConcatPullupTwoLow op xs ws nym) =
          Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof lowComp = Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullupTwoLow op xs ws nym))) =
          Term.Apply (Term.UOp UserOp.BitVec) wl := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullupTwoLhs op xs ws full))
    (__eo_typeof
      (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullupTwoTerm] at hsimpa ⊢); exact hsimpa)
  let highExt := bvConcatPullupTwoHigh op xs ws nxm ny
  let lowExt := bvConcatPullupTwoLow op xs ws nym
  let highTail := op.apply highComp
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply lowComp
    (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  let lowConcat := bvConcatPullupConcat lowPart (Term.Binary 0 0)
  have hOuter : __eo_typeof_concat (__eo_typeof highPart)
      (__eo_typeof lowConcat) ≠ Term.Stuck := by
    have hsimpa := hSides.2
    try simp [bvConcatPullupTwoRhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hOuter with
    ⟨wh, _wlOuter, hHighPartTy, hLowConcatTy⟩
  have hLowOuter : __eo_typeof_concat (__eo_typeof lowPart)
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hNe : __eo_typeof lowConcat ≠ Term.Stuck := by
      rw [hLowConcatTy]
      intro h
      cases h
    have hsimpa := hNe
    try simp [lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hLowOuter with
    ⟨wl, _we, hLowPartTy, _hEmptyTy⟩
  have hHighArgs := pullup_typeof_apply_args_of_result_bitvec op
    highExt highTail wh (by simpa [highPart] using hHighPartTy)
  have hLowArgs := pullup_typeof_apply_args_of_result_bitvec op
    lowExt lowTail wl (by simpa [lowPart] using hLowPartTy)
  have hHighTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    highComp (__eo_nil op.term (__eo_typeof highExt)) wh
    (by simpa [highTail] using hHighArgs.2)
  have hLowTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    lowComp (__eo_nil op.term (__eo_typeof lowExt)) wl
    (by simpa [lowTail] using hLowArgs.2)
  exact ⟨wh, wl,
    by simpa [highExt] using hHighArgs.1,
    hHighTailArgs.1,
    by simpa [highExt] using hHighTailArgs.2,
    by simpa [lowExt] using hLowArgs.1,
    hLowTailArgs.1,
    by simpa [lowExt] using hLowTailArgs.2⟩

private theorem pullup_extract_segment_smt_types
    (op : BvConcatPullupOp)
    (agg comp hi lo ext : Term) (w : Nat) :
    ext = bvConcatPullupExtract agg hi lo ->
    RuleProofs.eo_has_smt_translation agg ->
    __smtx_typeof (__eo_to_smt comp) = SmtType.BitVec w ->
    (∃ width : Term,
      __eo_typeof ext = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof comp = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (__eo_nil op.term (__eo_typeof ext)) =
        Term.Apply (Term.UOp UserOp.BitVec) width) ->
    __smtx_typeof (__eo_to_smt ext) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt
            (op.apply comp (__eo_nil op.term (__eo_typeof ext)))) =
        SmtType.BitVec w := by
  intro hExtDef hAggTrans hCompTy hEo
  rcases hEo with ⟨width, hExtEo, hCompEo, hNilEo⟩
  have hCompTrans : RuleProofs.eo_has_smt_translation comp := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hCompTy]
    intro h
    cases h
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width comp width
      hCompTrans hCompEo with
    ⟨wi, hWidth, hWi0, hCompRawTy⟩
  have hWiNat : native_int_to_nat wi = w := by
    rw [hCompTy] at hCompRawTy
    injection hCompRawTy with h
    exact h.symm
  have hWi : wi = native_nat_to_int w := by
    have hRound := native_int_to_nat_roundtrip wi hWi0
    rw [hWiNat] at hRound
    exact hRound.symm
  have hExtConcrete : __eo_typeof ext =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
    rw [hExtEo, hWidth, hWi]
  have hExtNe : __eo_typeof ext ≠ Term.Stuck := by
    rw [hExtConcrete]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck agg hi lo hAggTrans
      (by simpa [hExtDef, bvConcatPullupExtract, bvExtractTerm] using hExtNe) with
    ⟨wE, hE, lE, _hAggEo, hHi, hLo, hwE0, hlE0, hhEw,
      hExtWidth, hAggSmt⟩
  have hExtRawTy : __smtx_typeof (__eo_to_smt ext) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_zplus hE 1) (native_zneg lE))) := by
    rw [hExtDef]
    unfold bvConcatPullupExtract
    rw [hHi, hLo]
    simpa [bvExtractTerm] using
      (smt_typeof_extract_of_context agg wE hE lE hAggSmt hwE0 hlE0
        hhEw hExtWidth)
  have hExtMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation ext (by
      rw [hExtRawTy]
      intro h
      cases h)
  have hExtTy : __smtx_typeof (__eo_to_smt ext) = SmtType.BitVec w := by
    rw [hExtConcrete] at hExtMatch
    simpa [__eo_to_smt_type, native_ite, SmtEval.native_zleq,
      native_nat_to_int, native_int_to_nat, Smtm.native_nat_to_int,
      SmtEval.native_int_to_nat] using hExtMatch
  let nil := __eo_nil op.term (__eo_typeof ext)
  have hNilNe : nil ≠ Term.Stuck := by
    have hNilEo' : __eo_typeof nil =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
      simpa [nil] using hNilEo
    intro h
    rw [h] at hNilEo'
    cases hNilEo'
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w := by
    simpa [nil, hExtConcrete] using
      (pullup_generated_nil_smt_type op w (by
        simpa [nil, hExtConcrete] using hNilNe))
  exact ⟨hExtTy, by
    simpa [nil] using op.binarySmtType comp nil w hCompTy hNilTy⟩

theorem bvConcatPullupTwoRhsSmtTypesOfBody
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) (A B : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof (__eo_to_smt highComp) = SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt lowComp) = SmtType.BitVec B ->
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupTwoHigh op xs ws nxm ny)) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply highComp
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullupTwoHigh op xs ws nxm ny))))) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt (bvConcatPullupTwoLow op xs ws nym)) =
        SmtType.BitVec B ∧
      __smtx_typeof
        (__eo_to_smt
          (op.apply lowComp
            (__eo_nil op.term
              (__eo_typeof (bvConcatPullupTwoLow op xs ws nym))))) =
        SmtType.BitVec B := by
  intro hAggTrans hHighCompTy hLowCompTy hBodyTy
  rcases bvConcatPullupTwoRhsEoContext op xs ws full highComp lowComp
      nxm ny nym hBodyTy with
    ⟨wh, wl, hHighExtEo, hHighCompEo, hHighNilEo,
      hLowExtEo, hLowCompEo, hLowNilEo⟩
  have hHigh := pullup_extract_segment_smt_types op
    (bvConcatPullupAggregate op xs ws) highComp nxm ny
    (bvConcatPullupTwoHigh op xs ws nxm ny) A
    (by rfl) hAggTrans hHighCompTy
    ⟨wh, hHighExtEo, hHighCompEo, hHighNilEo⟩
  have hLow := pullup_extract_segment_smt_types op
    (bvConcatPullupAggregate op xs ws) lowComp nym (Term.Numeral 0)
    (bvConcatPullupTwoLow op xs ws nym) B
    (by rfl) hAggTrans hLowCompTy
    ⟨wl, hLowExtEo, hLowCompEo, hLowNilEo⟩
  exact ⟨hHigh.1, hHigh.2, hLow.1, hLow.2⟩

theorem typed_bvConcatPullupTwoTerm
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) (A B : Nat) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    __smtx_typeof (__eo_to_smt full) = SmtType.BitVec (A + B) ->
    __smtx_typeof (__eo_to_smt highComp) = SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt lowComp) = SmtType.BitVec B ->
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) := by
  intro hXsTrans hWsTrans hFullTy hHighCompTy hLowCompTy hBodyTy
  have hBase := bvConcatPullupTwoBaseContextFromFull op
    xs ws full highComp lowComp nxm ny nym (A + B)
    hXsTrans hWsTrans hFullTy hBodyTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2]
    intro h
    cases h
  have hComponents := bvConcatPullupTwoRhsSmtTypesOfBody op
    xs ws full highComp lowComp nxm ny nym A B hAggTrans
    hHighCompTy hLowCompTy hBodyTy
  let highExt := bvConcatPullupTwoHigh op xs ws nxm ny
  let lowExt := bvConcatPullupTwoLow op xs ws nym
  let highTail := op.apply highComp
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply lowComp
    (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  have hLhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullupTwoLhs op xs ws full)) =
      SmtType.BitVec (A + B) := by
    exact bvConcatPullupListSmtType op xs ws full (A + B)
      hBase.1 hBase.2.1 hBase.2.2.1 hBase.2.2.2.1 hFullTy
  have hHighPartTy : __smtx_typeof (__eo_to_smt highPart) =
      SmtType.BitVec A := by
    exact op.binarySmtType highExt highTail A
      (by simpa [highExt] using hComponents.1)
      (by simpa [highTail, highExt] using hComponents.2.1)
  have hLowPartTy : __smtx_typeof (__eo_to_smt lowPart) =
      SmtType.BitVec B := by
    exact op.binarySmtType lowExt lowTail B
      (by simpa [lowExt] using hComponents.2.2.1)
      (by simpa [lowTail, lowExt] using hComponents.2.2.2)
  have hLowConcatTy := bvConcat_term_smt_type lowPart (Term.Binary 0 0)
    B 0 hLowPartTy bvConcat_empty_smt_type
  have hRhsTy : __smtx_typeof
      (__eo_to_smt
        (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym)) =
      SmtType.BitVec (A + B) := by
    have hOuter := bvConcat_term_smt_type highPart
      (bvConcatPullupConcat lowPart (Term.Binary 0 0))
      A (B + 0) hHighPartTy
      (by have hsimpa := hLowConcatTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
    have hsimpa := hOuter
    try simp [bvConcatPullupTwoRhs, highExt, lowExt, highTail, lowTail, highPart, lowPart, Nat.add_assoc] at hsimpa ⊢
    exact hsimpa
  unfold bvConcatPullupTwoTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvConcatPullupTwoLhs op xs ws full)
    (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym)
    (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; intro h; cases h)

private theorem pullup_singleton_elim_list_of_ne_stuck
    (f c : Term) :
    __eo_list_singleton_elim f c ≠ Term.Stuck ->
    __eo_is_list f c = Term.Boolean true := by
  intro h
  change __eo_requires (__eo_is_list f c) (Term.Boolean true)
      (__eo_list_singleton_elim_2 c) ≠ Term.Stuck at h
  exact support_eo_requires_cond_eq_of_non_stuck h

theorem bvConcatPullup2Prem2Type (nxm z y ys : Term) :
    RuleProofs.eo_has_bool_type (bvConcatPullup2Prem2 nxm z y ys) ->
    ∃ wz wy wys : Nat,
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys := by
  simpa [bvConcatPullup2Prem2, bvConcatPullup2Prem2Raw,
    bvConcatPullup1Prem2, bvConcatPullup1Prem2Raw,
    bvConcatPullupConcat] using bvConcatPullup1Prem2Type nxm z y ys

theorem bvConcatPullup2ConcatTypes
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (wz wy wys : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __eo_typeof (bvConcatPullup2Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat)
        (bvConcatPullupConcat y ys) = Term.Boolean true ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullup2Full z y ys)) =
        SmtType.BitVec (wz + (wy + wys)) ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullup2LowComp y ys)) =
        SmtType.BitVec (wy + wys) := by
  intro hZTy hYTy hYsTy hBodyTy
  rcases bvConcatPullupTwoRhsEoContext op xs ws
      (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
      nxm ny nym (by simpa [bvConcatPullup2Term] using hBodyTy) with
    ⟨_wh, _wl, _hHighExt, _hZ, _hHighNil,
      _hLowExt, hLowCompEo, _hLowNil⟩
  have hLowCompNe : bvConcatPullup2LowComp y ys ≠ Term.Stuck := by
    intro h
    rw [h] at hLowCompEo
    cases hLowCompEo
  have hTailList : __eo_is_list (Term.UOp UserOp.concat)
      (bvConcatPullupConcat y ys) = Term.Boolean true :=
    pullup_singleton_elim_list_of_ne_stuck (Term.UOp UserOp.concat)
      (bvConcatPullupConcat y ys)
      (by simpa [bvConcatPullup2LowComp] using hLowCompNe)
  have hTailTy := bvConcat_term_smt_type y ys wy wys hYTy hYsTy
  have hLowCompTy := bvConcat_singleton_elim_smt_type
    (bvConcatPullupConcat y ys) (wy + wys) hTailList
    (by have hsimpa := hTailTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hFullTy := bvConcat_term_smt_type z
    (bvConcatPullupConcat y ys) wz (wy + wys) hZTy
    (by have hsimpa := hTailTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  exact ⟨hTailList,
    by have hsimpa := hFullTy; (try simp [bvConcatPullup2Full, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa,
    by simpa [bvConcatPullup2LowComp] using hLowCompTy⟩

theorem typed_bvConcatPullup2Term
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup2Prem2 nxm z y ys) ->
    __eo_typeof (bvConcatPullup2Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatPullup2Term op xs ws y z ys nxm ny nym) := by
  intro hXsTrans hWsTrans hPrem2Bool hBodyTy
  rcases bvConcatPullup2Prem2Type nxm z y ys hPrem2Bool with
    ⟨wz, wy, wys, hZTy, hYTy, hYsTy⟩
  have hConcat := bvConcatPullup2ConcatTypes op
    xs ws y z ys nxm ny nym wz wy wys hZTy hYTy hYsTy hBodyTy
  exact typed_bvConcatPullupTwoTerm op xs ws
    (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
    nxm ny nym wz (wy + wys) hXsTrans hWsTrans hConcat.2.1 hZTy
    hConcat.2.2 (by simpa [bvConcatPullup2Term] using hBodyTy)

theorem eval_bvConcatPullupTwo
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws full highComp lowComp nxm ny nym : Term) (A B : Nat) :
    __eo_is_list op.term xs = Term.Boolean true ->
    __eo_is_list op.term ws = Term.Boolean true ->
    PullupListTypeOrNil xs (A + B) ->
    __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec (A + B) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (A + B) ->
    __smtx_typeof (__eo_to_smt full) = SmtType.BitVec (A + B) ->
    __smtx_typeof (__eo_to_smt highComp) = SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt lowComp) = SmtType.BitVec B ->
    __smtx_model_eval M (__eo_to_smt full) =
      __smtx_model_eval M
        (__eo_to_smt (bvConcatPullupConcat highComp lowComp)) ->
    nxm = Term.Numeral (native_nat_to_int (A + B - 1)) ->
    ny = Term.Numeral (native_nat_to_int B) ->
    nym = Term.Numeral (native_nat_to_int (B - 1)) ->
    0 < A -> 0 < B ->
    __eo_typeof
        (bvConcatPullupTwoTerm op xs ws full highComp lowComp nxm ny nym) =
      Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatPullupTwoLhs op xs ws full)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym)) := by
  intro hXsList hWsList hXsType hWsTy hAggTy hFullTy hHighCompTy
    hLowCompTy hFullRelation hNxm hNy hNym hAPos hBPos hBodyTy
  have hLhsEval := bvConcatPullupListEval M hM op xs ws full (A + B)
    hXsList hWsList hXsType hWsTy hFullTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hAggTy]
    intro h
    cases h
  have hRhsTypes := bvConcatPullupTwoRhsSmtTypesOfBody op
    xs ws full highComp lowComp nxm ny nym A B hAggTrans
    hHighCompTy hLowCompTy hBodyTy
  let agg := bvConcatPullupAggregate op xs ws
  let highExt := bvConcatPullupTwoHigh op xs ws nxm ny
  let lowExt := bvConcatPullupTwoLow op xs ws nym
  let highTail := op.apply highComp
    (__eo_nil op.term (__eo_typeof highExt))
  let lowTail := op.apply lowComp
    (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let lowPart := op.apply lowExt lowTail
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt agg)
      (A + B) (by simpa [agg] using hAggTy) with
    ⟨pa, hAggEval, hAggCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt full)
      (A + B) hFullTy with
    ⟨pf, hFullEval, hFullCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt highComp) A hHighCompTy with
    ⟨ph, hHighCompEval, hHighCompCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt lowComp) B hLowCompTy with
    ⟨pl, hLowCompEval, hLowCompCan⟩
  have hNatWidth0 : ∀ w : Nat,
      native_zleq 0 (native_nat_to_int w) = true := by
    intro w
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hW0 := hNatWidth0 (A + B)
  have hA0 := hNatWidth0 A
  have hB0 := hNatWidth0 B
  have hAggRange := bitvec_payload_range_of_canonical hW0 hAggCan
  have hFullRange := bitvec_payload_range_of_canonical hW0 hFullCan
  have hHighRange := bitvec_payload_range_of_canonical hA0 hHighCompCan
  have hLowRange := bitvec_payload_range_of_canonical hB0 hLowCompCan
  have hAgg0 : 0 ≤ pa := hAggRange.1
  have hAgg1 : pa < (2 : Int) ^ (A + B) := by
    have hsimpa := hAggRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hFull0 : 0 ≤ pf := hFullRange.1
  have hFull1 : pf < (2 : Int) ^ (A + B) := by
    have hsimpa := hFullRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hHigh0 : 0 ≤ ph := hHighRange.1
  have hHigh1 : ph < (2 : Int) ^ A := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hHighRange.2
  have hLow0 : 0 ≤ pl := hLowRange.1
  have hLow1 : pl < (2 : Int) ^ B := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hLowRange.2
  have hConcatEval : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat highComp lowComp)) =
      __smtx_model_eval_concat
        (SmtValue.Binary ↑A ph) (SmtValue.Binary ↑B pl) := by
    change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt highComp))
      (__smtx_model_eval M (__eo_to_smt lowComp)) = _
    rw [hHighCompEval, hLowCompEval]
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hFullAsConcat :
      SmtValue.Binary ↑(A + B) pf =
        __smtx_model_eval_concat
          (SmtValue.Binary ↑A ph) (SmtValue.Binary ↑B pl) := by
    calc
      _ = __smtx_model_eval M (__eo_to_smt full) := hFullEval.symm
      _ = __smtx_model_eval M
          (__eo_to_smt (bvConcatPullupConcat highComp lowComp)) :=
        hFullRelation
      _ = _ := hConcatEval
  have hFullHigh :
      __smtx_model_eval_extract
          (SmtValue.Numeral ↑(A + B - 1))
          (SmtValue.Numeral ↑B)
          (SmtValue.Binary ↑(A + B) pf) =
        SmtValue.Binary ↑A ph := by
    rw [hFullAsConcat]
    exact bvConcat_extract_high_full_value A B ph pl
      hHigh0 hHigh1 hLow0 hLow1 hAPos
  have hFullLow :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(B - 1))
          (SmtValue.Numeral 0) (SmtValue.Binary ↑(A + B) pf) =
        SmtValue.Binary ↑B pl := by
    rw [hFullAsConcat]
    exact bvConcat_extract_low_full_value A B ph pl
      hHigh0 hHigh1 hLow0 hLow1 hBPos
  have hHighExtEval : __smtx_model_eval M (__eo_to_smt highExt) =
      __smtx_model_eval_extract
        (SmtValue.Numeral ↑(A + B - 1)) (SmtValue.Numeral ↑B)
        (SmtValue.Binary ↑(A + B) pa) := by
    unfold highExt bvConcatPullupTwoHigh bvConcatPullupExtract
    rw [hNxm, hNy]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (A + B - 1)))
          (SmtTerm.Numeral (native_nat_to_int B))
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hLowExtEval : __smtx_model_eval M (__eo_to_smt lowExt) =
      __smtx_model_eval_extract (SmtValue.Numeral ↑(B - 1))
        (SmtValue.Numeral 0) (SmtValue.Binary ↑(A + B) pa) := by
    unfold lowExt bvConcatPullupTwoLow bvConcatPullupExtract
    rw [hNym]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (B - 1)))
          (SmtTerm.Numeral 0)
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hHighTailEval : __smtx_model_eval M (__eo_to_smt highTail) =
      __smtx_model_eval M (__eo_to_smt highComp) := by
    exact bvConcatPullupEvalApplyGeneratedNil M hM op highComp
      (__eo_typeof highExt) A A
      (by simpa [highExt] using
        pullup_eo_typeof_eq_bitvec_of_smt_bitvec _ A hRhsTypes.1)
      hHighCompTy
      (by simpa [highTail] using hRhsTypes.2.1)
  have hLowTailEval : __smtx_model_eval M (__eo_to_smt lowTail) =
      __smtx_model_eval M (__eo_to_smt lowComp) := by
    exact bvConcatPullupEvalApplyGeneratedNil M hM op lowComp
      (__eo_typeof lowExt) B B
      (by simpa [lowExt] using
        pullup_eo_typeof_eq_bitvec_of_smt_bitvec _ B hRhsTypes.2.2.1)
      hLowCompTy
      (by simpa [lowTail] using hRhsTypes.2.2.2)
  have hHighPartEval : __smtx_model_eval M (__eo_to_smt highPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt highExt))
        (__smtx_model_eval M (__eo_to_smt highComp)) := by
    rw [show __smtx_model_eval M (__eo_to_smt highPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highTail)) by
      simpa [highPart] using op.evalApply M highExt highTail]
    rw [hHighTailEval]
  have hLowPartEval : __smtx_model_eval M (__eo_to_smt lowPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
        (__smtx_model_eval M (__eo_to_smt lowComp)) := by
    rw [show __smtx_model_eval M (__eo_to_smt lowPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt lowTail)) by
      simpa [lowPart] using op.evalApply M lowExt lowTail]
    rw [hLowTailEval]
  have hLowPartTy := op.binarySmtType lowExt lowTail B
    (by simpa [lowExt] using hRhsTypes.2.2.1)
    (by simpa [lowTail] using hRhsTypes.2.2.2)
  have hLowEmpty := bvConcat_eval_right_empty M hM lowPart B
    (by simpa [lowPart] using hLowPartTy)
  have hLowEmpty' : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt lowPart) := by
    simpa [bvConcatPullupConcat, bvConcatTerm] using hLowEmpty
  have hRhsEval : __smtx_model_eval M
      (__eo_to_smt
        (bvConcatPullupTwoRhs op xs ws highComp lowComp nxm ny nym)) =
      __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highComp)))
        (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt lowComp))) := by
    change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt highPart))
      (__smtx_model_eval M
        (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0)))) = _
    rw [hHighPartEval, hLowEmpty', hLowPartEval]
  have hSplit := op.splitValue (A + B) B pa pf
    hAgg0 hAgg1 hFull0 hFull1 (by omega) (by omega)
  calc
    _ = op.eval (__smtx_model_eval M (__eo_to_smt agg))
        (__smtx_model_eval M (__eo_to_smt full)) := by
      have hsimpa := hLhsEval
      try simp [bvConcatPullupTwoLhs, agg] at hsimpa ⊢
      exact hsimpa
    _ = op.eval (SmtValue.Binary ↑(A + B) pa)
        (SmtValue.Binary ↑(A + B) pf) := by
      rw [hAggEval, hFullEval]
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hSplit
    _ = __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highComp)))
        (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt lowComp))) := by
      rw [hHighExtEval, hFullHigh, hHighCompEval,
        hLowExtEval, hFullLow, hLowCompEval]
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hRhsEval.symm

theorem bvConcatPullup2Prem1Eval
    (M : SmtModel) (ny z y ys : Term) (wz wy wys : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    eo_interprets M (bvConcatPullup2Prem1 ny z y ys) true ->
    __smtx_model_eval M (__eo_to_smt ny) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg (native_nat_to_int wz))) := by
  intro hZTy hYTy hYsTy hPrem
  let tail := bvConcatPullupConcat y ys
  let full := bvConcatPullupConcat z tail
  have hTailTy := bvConcat_term_smt_type y ys wy wys hYTy hYsTy
  have hFullTy := bvConcat_term_smt_type z tail wz (wy + wys) hZTy
    (by have hsimpa := hTailTy; (try simp [tail, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hFullSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M full
    (wz + (wy + wys))
    (by have hsimpa := hFullTy; (try simp [full, tail, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hZSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M z wz hZTy
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.UOp UserOp._at_bvsize) full))
    (Term.Apply (Term.UOp UserOp._at_bvsize) z)
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M ny rhs
    (by simpa [bvConcatPullup2Prem1, bvConcatPullup2Prem1Raw,
      bvConcatPullupConcat, full, tail, rhs] using hPrem)
  have hRhsEvalSmt : __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) full))
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) z))) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg (native_nat_to_int wz))) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hFullSize, hZSize]
    simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
      native_zneg]
  have hRhsEval : __smtx_model_eval M (__eo_to_smt rhs) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg (native_nat_to_int wz))) := by
    have hsimpa := hRhsEvalSmt
    try simp [rhs] at hsimpa ⊢
    exact hsimpa
  rw [hRhsEval] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup2Prem3Eval
    (M : SmtModel) (nym z y ys : Term) (wz wy wys : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    eo_interprets M (bvConcatPullup2Prem3 nym z y ys) true ->
    __smtx_model_eval M (__eo_to_smt nym) =
      SmtValue.Numeral
        (native_zplus
          (native_zplus (native_nat_to_int (wz + (wy + wys)))
            (native_zneg (native_nat_to_int wz)))
          (native_zneg 1)) := by
  intro hZTy hYTy hYsTy hPrem
  let tail := bvConcatPullupConcat y ys
  let full := bvConcatPullupConcat z tail
  have hTailTy := bvConcat_term_smt_type y ys wy wys hYTy hYsTy
  have hFullTy := bvConcat_term_smt_type z tail wz (wy + wys) hZTy
    (by have hsimpa := hTailTy; (try simp [tail, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hFullSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M full
    (wz + (wy + wys))
    (by have hsimpa := hFullTy; (try simp [full, tail, bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hZSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M z wz hZTy
  let inner := Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.UOp UserOp._at_bvsize) full))
    (Term.Apply (Term.UOp UserOp._at_bvsize) z)
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg) inner)
    (Term.Numeral 1)
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nym rhs
    (by simpa [bvConcatPullup2Prem3, bvConcatPullup2Prem3Raw,
      bvConcatPullupConcat, full, tail, inner, rhs] using hPrem)
  have hRhsEvalSmt : __smtx_model_eval M
      (SmtTerm.neg
        (SmtTerm.neg
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) full))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) z)))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral
        (native_zplus
          (native_zplus (native_nat_to_int (wz + (wy + wys)))
            (native_zneg (native_nat_to_int wz)))
          (native_zneg 1)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hFullSize, hZSize]
    simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
      native_zneg]
  have hRhsEval : __smtx_model_eval M (__eo_to_smt rhs) =
      SmtValue.Numeral
        (native_zplus
          (native_zplus (native_nat_to_int (wz + (wy + wys)))
            (native_zneg (native_nat_to_int wz)))
          (native_zneg 1)) := by
    have hsimpa := hRhsEvalSmt
    try simp [rhs, inner] at hsimpa ⊢
    exact hsimpa
  rw [hRhsEval] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup2Indices
    (M : SmtModel) (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) (wz wy wys : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (wz + (wy + wys)) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __eo_typeof (bvConcatPullup2Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup2Prem1 ny z y ys) true ->
    eo_interprets M (bvConcatPullup2Prem2 nxm z y ys) true ->
    eo_interprets M (bvConcatPullup2Prem3 nym z y ys) true ->
    nxm = Term.Numeral
        (native_nat_to_int (wz + (wy + wys) - 1)) ∧
      ny = Term.Numeral (native_nat_to_int (wy + wys)) ∧
      nym = Term.Numeral (native_nat_to_int (wy + wys - 1)) ∧
      0 < wz ∧ 0 < wy + wys := by
  intro hAggTrans hAggTy hZTy hYTy hYsTy hBodyTy hP1 hP2 hP3
  rcases bvConcatPullupTwoRhsEoContext op xs ws
      (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
      nxm ny nym (by simpa [bvConcatPullup2Term] using hBodyTy) with
    ⟨_wh, _wl, hHighExtEo, _hZEo, _hHighNil,
      hLowExtEo, _hLowCompEo, _hLowNil⟩
  have hHighExtNe : __eo_typeof
      (bvConcatPullupTwoHigh op xs ws nxm ny) ≠ Term.Stuck := by
    rw [hHighExtEo]
    intro h
    cases h
  have hLowExtNe : __eo_typeof
      (bvConcatPullupTwoLow op xs ws nym) ≠ Term.Stuck := by
    rw [hLowExtEo]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nxm ny hAggTrans
      (by simpa [bvConcatPullupTwoHigh, bvConcatPullupExtract,
        bvExtractTerm] using hHighExtNe) with
    ⟨wH, hH, lH, _hAggEoH, hNxm, hNy, hwH0, _hlH0, _hhHw,
      hHighWidth, hAggSmtH⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nym (Term.Numeral 0) hAggTrans
      (by simpa [bvConcatPullupTwoLow, bvConcatPullupExtract,
        bvExtractTerm] using hLowExtNe) with
    ⟨wL, hL, lL, _hAggEoL, hNym, hZero, hwL0, _hlL0, _hhLw,
      hLowWidth, hAggSmtL⟩
  have hWHNat : native_int_to_nat wH = wz + (wy + wys) := by
    rw [hAggTy] at hAggSmtH
    injection hAggSmtH with h
    exact h.symm
  have hWLNat : native_int_to_nat wL = wz + (wy + wys) := by
    rw [hAggTy] at hAggSmtL
    injection hAggSmtL with h
    exact h.symm
  have hWH : wH = native_nat_to_int (wz + (wy + wys)) := by
    have hRound := native_int_to_nat_roundtrip wH hwH0
    rw [hWHNat] at hRound
    exact hRound.symm
  have hWL : wL = native_nat_to_int (wz + (wy + wys)) := by
    have hRound := native_int_to_nat_roundtrip wL hwL0
    rw [hWLNat] at hRound
    exact hRound.symm
  have hLHRaw : lH =
      native_zplus (native_nat_to_int (wz + (wy + wys)))
        (native_zneg (native_nat_to_int wz)) := by
    have hEval := bvConcatPullup2Prem1Eval M ny z y ys wz wy wys
      hZTy hYTy hYsTy hP1
    rw [hNy] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hHHRaw : hH =
      native_zplus (native_nat_to_int (wz + (wy + wys)))
        (native_zneg 1) := by
    have hEval := bvConcatPullup1Prem2Eval M nxm z y ys wz wy wys
      hZTy hYTy hYsTy
      (by simpa [bvConcatPullup2Prem2, bvConcatPullup2Prem2Raw,
        bvConcatPullup1Prem2, bvConcatPullup1Prem2Raw,
        bvConcatPullupConcat] using hP2)
    rw [hNxm] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLLRaw : hL =
      native_zplus
        (native_zplus (native_nat_to_int (wz + (wy + wys)))
          (native_zneg (native_nat_to_int wz)))
        (native_zneg 1) := by
    have hEval := bvConcatPullup2Prem3Eval M nym z y ys wz wy wys
      hZTy hYTy hYsTy hP3
    rw [hNym] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLZero : lL = 0 := by
    injection hZero with h
    exact h.symm
  have hBPos : 0 < wy + wys := by
    rw [hLLRaw, hLZero] at hLowWidth
    have hIntRaw : (0 : Int) <
        (↑(wz + (wy + wys)) : Int) + -↑wz + -1 + 1 := by
      simpa [SmtEval.native_zlt, SmtEval.native_zplus,
        SmtEval.native_zneg, native_nat_to_int,
        Smtm.native_nat_to_int] using hLowWidth
    have hInt : (0 : Int) < ↑(wy + wys) := by
      push_cast
      omega
    exact_mod_cast hInt
  have hAPos : 0 < wz := by
    rw [hHHRaw, hLHRaw] at hHighWidth
    have hIntRaw : (0 : Int) <
        (↑(wz + (wy + wys)) : Int) + -1 + 1 +
          -((↑(wz + (wy + wys)) : Int) + -↑wz) := by
      have hsimpa := hHighWidth
      try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hInt : (0 : Int) < ↑wz := by
      push_cast
      omega
    exact_mod_cast hInt
  have hHH : hH = native_nat_to_int (wz + (wy + wys) - 1) := by
    rw [hHHRaw]
    change (↑(wz + (wy + wys)) : Int) + -1 =
      ↑(wz + (wy + wys) - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wz + (wy + wys))]
    push_cast
    omega
  have hLH : lH = native_nat_to_int (wy + wys) := by
    rw [hLHRaw]
    change (↑(wz + (wy + wys)) : Int) + -↑wz = ↑(wy + wys)
    push_cast
    omega
  have hLL : hL = native_nat_to_int (wy + wys - 1) := by
    rw [hLLRaw]
    change (↑(wz + (wy + wys)) : Int) + -↑wz + -1 =
      ↑(wy + wys - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wy + wys)]
    push_cast
    omega
  exact ⟨hNxm.trans (congrArg Term.Numeral hHH),
    hNy.trans (congrArg Term.Numeral hLH),
    hNym.trans (congrArg Term.Numeral hLL), hAPos, hBPos⟩

theorem bvConcatPullup2FullEval
    (M : SmtModel) (hM : model_wf M)
    (y z ys : Term) (wz wy wys : Nat) :
    __eo_is_list (Term.UOp UserOp.concat)
        (bvConcatPullupConcat y ys) = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec wys ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatPullup2Full z y ys)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatPullupConcat z (bvConcatPullup2LowComp y ys))) := by
  intro hTailList hZTy hYTy hYsTy
  have hTailTy := bvConcat_term_smt_type y ys wy wys hYTy hYsTy
  have hElim := bvConcat_singleton_elim_eval_eq M hM
    (bvConcatPullupConcat y ys) (wy + wys) hTailList
    (by have hsimpa := hTailTy; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt z))
      (__smtx_model_eval M
        (__eo_to_smt (bvConcatPullupConcat y ys))) =
    __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt z))
      (__smtx_model_eval M
        (__eo_to_smt (bvConcatPullup2LowComp y ys)))
  exact congrArg
    (fun v => __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt z)) v)
    (by simpa [bvConcatPullup2LowComp] using hElim.symm)

theorem facts_bvConcatPullup2Term
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup2Prem2 nxm z y ys) ->
    __eo_typeof (bvConcatPullup2Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup2Prem1 ny z y ys) true ->
    eo_interprets M (bvConcatPullup2Prem2 nxm z y ys) true ->
    eo_interprets M (bvConcatPullup2Prem3 nym z y ys) true ->
    eo_interprets M
      (bvConcatPullup2Term op xs ws y z ys nxm ny nym) true := by
  intro hXsTrans hWsTrans hPrem2Bool hBodyTy hP1 hP2 hP3
  rcases bvConcatPullup2Prem2Type nxm z y ys hPrem2Bool with
    ⟨wz, wy, wys, hZTy, hYTy, hYsTy⟩
  have hConcat := bvConcatPullup2ConcatTypes op
    xs ws y z ys nxm ny nym wz wy wys hZTy hYTy hYsTy hBodyTy
  have hBase := bvConcatPullupTwoBaseContextFromFull op xs ws
    (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
    nxm ny nym (wz + (wy + wys)) hXsTrans hWsTrans hConcat.2.1
    (by simpa [bvConcatPullup2Term] using hBodyTy)
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2]
    intro h
    cases h
  have hIndices := bvConcatPullup2Indices M op
    xs ws y z ys nxm ny nym wz wy wys hAggTrans hBase.2.2.2.2
    hZTy hYTy hYsTy hBodyTy hP1 hP2 hP3
  have hFullRelation := bvConcatPullup2FullEval M hM y z ys wz wy wys
    hConcat.1 hZTy hYTy hYsTy
  have hEval := eval_bvConcatPullupTwo M hM op xs ws
    (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
    nxm ny nym wz (wy + wys) hBase.1 hBase.2.1 hBase.2.2.1
    hBase.2.2.2.1 hBase.2.2.2.2 hConcat.2.1 hZTy hConcat.2.2
    hFullRelation hIndices.1 hIndices.2.1 hIndices.2.2.1
    hIndices.2.2.2.1 hIndices.2.2.2.2
    (by simpa [bvConcatPullup2Term] using hBodyTy)
  have hEqBool := typed_bvConcatPullup2Term op xs ws y z ys nxm ny nym
    hXsTrans hWsTrans hPrem2Bool hBodyTy
  unfold bvConcatPullup2Term bvConcatPullupTwoTerm at hEqBool ⊢
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [hEval]
    exact RuleProofs.smt_value_rel_refl _

theorem bvConcatPullup2ProgramProperties
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z ys nxm ny nym P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation ys ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation ny ->
    RuleProofs.eo_has_smt_translation nym ->
    RuleProofs.eo_has_bool_type P1 ->
    RuleProofs.eo_has_bool_type P2 ->
    RuleProofs.eo_has_bool_type P3 ->
    __eo_typeof
        (bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3) =
      Term.Bool ->
    StepRuleProperties M [P1, P2, P3]
      (bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3) := by
  intro hXsTrans hWsTrans hYTrans hZTrans hYsTrans hNxmTrans hNyTrans
    hNymTrans hP1Bool hP2Bool hP3Bool hResultTy
  have hProg : bvConcatPullup2Program op xs ws y z ys nxm ny nym
      P1 P2 P3 ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  have hNorm := bvConcatPullup2Program_normalize op
    xs ws y z ys nxm ny nym P1 P2 P3 hXsTrans hWsTrans hYTrans
    hZTrans hYsTrans hNxmTrans hNyTrans hNymTrans hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hYs := RuleProofs.term_ne_stuck_of_has_smt_translation ys hYsTrans
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmTrans
  have hNy := RuleProofs.term_ne_stuck_of_has_smt_translation ny hNyTrans
  have hNym := RuleProofs.term_ne_stuck_of_has_smt_translation nym hNymTrans
  have hProgramRaw :
      bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3 =
        bvConcatPullupTwoBodyRaw op xs ws (bvConcatPullup2Full z y ys) z
          (bvConcatPullup2LowComp y ys) nxm ny nym := by
    rw [hNorm.1, hNorm.2.1, hNorm.2.2]
    exact bvConcatPullup2Program_eq_raw op xs ws y z ys nxm ny nym
      hXs hWs hY hZ hYs hNxm hNy hNym
  have hRawNe : bvConcatPullupTwoBodyRaw op xs ws
      (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
      nxm ny nym ≠ Term.Stuck := by
    rw [← hProgramRaw]
    exact hProg
  have hProgramTerm :
      bvConcatPullup2Program op xs ws y z ys nxm ny nym P1 P2 P3 =
        bvConcatPullup2Term op xs ws y z ys nxm ny nym := by
    rw [hProgramRaw, bvConcatPullup2Term]
    exact bvConcatPullupTwoBodyRaw_eq_term op xs ws
      (bvConcatPullup2Full z y ys) z (bvConcatPullup2LowComp y ys)
      nxm ny nym hRawNe
  have hBodyTy : __eo_typeof
      (bvConcatPullup2Term op xs ws y z ys nxm ny nym) = Term.Bool := by
    rw [← hProgramTerm]
    exact hResultTy
  have hPrem2Bool : RuleProofs.eo_has_bool_type
      (bvConcatPullup2Prem2 nxm z y ys) := by
    rw [← hNorm.2.1]
    exact hP2Bool
  refine ⟨?_, ?_⟩
  · intro hPremEvidence
    have hP1True : eo_interprets M
        (bvConcatPullup2Prem1 ny z y ys) true := by
      rw [← hNorm.1]
      exact hPremEvidence P1 (by simp)
    have hP2True : eo_interprets M
        (bvConcatPullup2Prem2 nxm z y ys) true := by
      rw [← hNorm.2.1]
      exact hPremEvidence P2 (by simp)
    have hP3True : eo_interprets M
        (bvConcatPullup2Prem3 nym z y ys) true := by
      rw [← hNorm.2.2]
      exact hPremEvidence P3 (by simp)
    rw [hProgramTerm]
    exact facts_bvConcatPullup2Term M hM op xs ws y z ys nxm ny nym
      hXsTrans hWsTrans hPrem2Bool hBodyTy hP1True hP2True hP3True
  · rw [hProgramTerm]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_bvConcatPullup2Term op xs ws y z ys nxm ny nym
        hXsTrans hWsTrans hPrem2Bool hBodyTy)

def BvConcatPullupOp.pullup2Rule : BvConcatPullupOp → CRule
  | .band => CRule.bv_and_concat_pullup2
  | .bor => CRule.bv_or_concat_pullup2
  | .bxor => CRule.bv_xor_concat_pullup2

theorem cmd_step_bvConcatPullup2_properties
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (s : CState) (args : CArgList) (premises : CIndexList) :
    cmdTranslationOk (CCmd.step op.pullup2Rule args premises) ->
    AllHaveBoolType (premiseTermList s premises) ->
    __eo_typeof
        (__eo_cmd_step_proven s op.pullup2Rule args premises) = Term.Bool ->
    StepRuleProperties M (premiseTermList s premises)
      (__eo_cmd_step_proven s op.pullup2Rule args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s op.pullup2Rule args premises ≠
      Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg (by cases op <;> rfl))
  | cons xs args =>
    cases args with
    | nil => exact False.elim (hProg (by cases op <;> rfl))
    | cons ws args =>
      cases args with
      | nil => exact False.elim (hProg (by cases op <;> rfl))
      | cons y args =>
        cases args with
        | nil => exact False.elim (hProg (by cases op <;> rfl))
        | cons z args =>
          cases args with
          | nil => exact False.elim (hProg (by cases op <;> rfl))
          | cons ys args =>
            cases args with
            | nil => exact False.elim (hProg (by cases op <;> rfl))
            | cons nxm args =>
              cases args with
              | nil => exact False.elim (hProg (by cases op <;> rfl))
              | cons ny args =>
                cases args with
                | nil => exact False.elim (hProg (by cases op <;> rfl))
                | cons nym args =>
                  cases args with
                  | cons _ _ =>
                    exact False.elim (hProg (by cases op <;> rfl))
                  | nil =>
                    cases premises with
                    | nil => exact False.elim (hProg (by cases op <;> rfl))
                    | cons n1 premises =>
                      cases premises with
                      | nil =>
                        exact False.elim (hProg (by cases op <;> rfl))
                      | cons n2 premises =>
                        cases premises with
                        | nil =>
                          exact False.elim (hProg (by cases op <;> rfl))
                        | cons n3 premises =>
                          cases premises with
                          | cons _ _ =>
                            exact False.elim (hProg (by cases op <;> rfl))
                          | nil =>
                            let P1 := __eo_state_proven_nth s n1
                            let P2 := __eo_state_proven_nth s n2
                            let P3 := __eo_state_proven_nth s n3
                            have hCommandEq :
                                __eo_cmd_step_proven s op.pullup2Rule
                                    (CArgList.cons xs (CArgList.cons ws
                                      (CArgList.cons y (CArgList.cons z
                                        (CArgList.cons ys (CArgList.cons nxm
                                          (CArgList.cons ny (CArgList.cons nym
                                            CArgList.nil))))))))
                                    (CIndexList.cons n1 (CIndexList.cons n2
                                      (CIndexList.cons n3 CIndexList.nil))) =
                                  bvConcatPullup2Program op xs ws y z ys
                                    nxm ny nym P1 P2 P3 := by
                              cases op <;> rfl
                            rw [hCommandEq]
                            have hArgsTrans :
                                RuleProofs.eo_has_smt_translation xs ∧
                                RuleProofs.eo_has_smt_translation ws ∧
                                RuleProofs.eo_has_smt_translation y ∧
                                RuleProofs.eo_has_smt_translation z ∧
                                RuleProofs.eo_has_smt_translation ys ∧
                                RuleProofs.eo_has_smt_translation nxm ∧
                                RuleProofs.eo_has_smt_translation ny ∧
                                RuleProofs.eo_has_smt_translation nym ∧
                                True := by
                              cases op <;> simpa [BvConcatPullupOp.pullup2Rule,
                                cmdTranslationOk, cArgListTranslationOk]
                                using hCmdTrans
                            have hP1Bool := hPremisesBool P1 (by
                              simp [premiseTermList, P1, P2, P3])
                            have hP2Bool := hPremisesBool P2 (by
                              simp [premiseTermList, P1, P2, P3])
                            have hP3Bool := hPremisesBool P3 (by
                              simp [premiseTermList, P1, P2, P3])
                            have hResultTyLocal : __eo_typeof
                                (bvConcatPullup2Program op xs ws y z ys
                                  nxm ny nym P1 P2 P3) = Term.Bool := by
                              rw [← hCommandEq]
                              exact hResultTy
                            exact bvConcatPullup2ProgramProperties M hM op
                              xs ws y z ys nxm ny nym P1 P2 P3
                              hArgsTrans.1 hArgsTrans.2.1
                              hArgsTrans.2.2.1 hArgsTrans.2.2.2.1
                              hArgsTrans.2.2.2.2.1
                              hArgsTrans.2.2.2.2.2.1
                              hArgsTrans.2.2.2.2.2.2.1
                              hArgsTrans.2.2.2.2.2.2.2.1
                              hP1Bool hP2Bool hP3Bool hResultTyLocal

/-! ## Three-segment concat pullup (the `pullup3` rules) -/

def bvConcatPullup3Full (z y u : Term) : Term :=
  bvConcatPullupConcat z
    (bvConcatPullupConcat y
      (bvConcatPullupConcat u (Term.Binary 0 0)))

def bvConcatPullup3Prem1Raw
    (nxmR uR yR zR : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nxmR)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.UOp UserOp._at_bvsize) uR))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
          (Term.Apply (Term.UOp UserOp._at_bvsize) yR))
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
            (Term.Apply (Term.UOp UserOp._at_bvsize) zR))
            (Term.Numeral 0)))))
      (Term.Numeral 1))

def bvConcatPullup3Prem2Raw (nyuR yR uR : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nyuR)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
      (Term.Apply (Term.UOp UserOp._at_bvsize) yR))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.UOp UserOp._at_bvsize) uR))
        (Term.Numeral 0)))

def bvConcatPullup3Prem3Raw (nyumR yR uR : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nyumR)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.UOp UserOp._at_bvsize) yR))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
          (Term.Apply (Term.UOp UserOp._at_bvsize) uR))
          (Term.Numeral 0))))
      (Term.Numeral 1))

def bvConcatPullup3Prem4Raw (nuR uR : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nuR)
    (Term.Apply (Term.UOp UserOp._at_bvsize) uR)

def bvConcatPullup3Prem5Raw (numR uR : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) numR)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) uR))
      (Term.Numeral 1))

def bvConcatPullup3Prem1 (nxm u y z : Term) : Term :=
  bvConcatPullup3Prem1Raw nxm u y z

def bvConcatPullup3Prem2 (nyu y u : Term) : Term :=
  bvConcatPullup3Prem2Raw nyu y u

def bvConcatPullup3Prem3 (nyum y u : Term) : Term :=
  bvConcatPullup3Prem3Raw nyum y u

def bvConcatPullup3Prem4 (nu u : Term) : Term :=
  bvConcatPullup3Prem4Raw nu u

def bvConcatPullup3Prem5 (num u : Term) : Term :=
  bvConcatPullup3Prem5Raw num u

def bvConcatPullup3Program
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5 : Term) : Term :=
  match op with
  | .band => __eo_prog_bv_and_concat_pullup3 xs ws y z u nxm nyu nyum nu num
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)
  | .bor => __eo_prog_bv_or_concat_pullup3 xs ws y z u nxm nyu nyum nu num
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)
  | .bxor => __eo_prog_bv_xor_concat_pullup3 xs ws y z u nxm nyu nyum nu num
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)

def bvConcatPullup3High
    (op : BvConcatPullupOp) (xs ws nxm nyu : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nxm nyu

def bvConcatPullup3Mid
    (op : BvConcatPullupOp) (xs ws nyum nu : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) nyum nu

def bvConcatPullup3Low
    (op : BvConcatPullupOp) (xs ws num : Term) : Term :=
  bvConcatPullupExtract (bvConcatPullupAggregate op xs ws) num
    (Term.Numeral 0)

def bvConcatPullup3Lhs
    (op : BvConcatPullupOp) (xs ws z y u : Term) : Term :=
  __eo_list_concat op.term xs (op.apply (bvConcatPullup3Full z y u) ws)

def bvConcatPullup3Rhs
    (op : BvConcatPullupOp)
    (xs ws z y u nxm nyu nyum nu num : Term) : Term :=
  let highExt := bvConcatPullup3High op xs ws nxm nyu
  let midExt := bvConcatPullup3Mid op xs ws nyum nu
  let lowExt := bvConcatPullup3Low op xs ws num
  let highPart := op.apply highExt
    (op.apply z (__eo_nil op.term (__eo_typeof highExt)))
  let midPart := op.apply midExt
    (op.apply y (__eo_nil op.term (__eo_typeof midExt)))
  let lowPart := op.apply lowExt
    (op.apply u (__eo_nil op.term (__eo_typeof lowExt)))
  bvConcatPullupConcat highPart
    (bvConcatPullupConcat midPart
      (bvConcatPullupConcat lowPart (Term.Binary 0 0)))

def bvConcatPullup3Term
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvConcatPullup3Lhs op xs ws z y u))
    (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num)

private theorem pullup3_guard_refs
    {nxm u y z nyu nyum nu num
      nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3
      nuR uR4 numR uR5 body : Term} :
    __eo_requires
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and
                        (__eo_and
                          (__eo_and
                            (__eo_and
                              (__eo_and (__eo_eq nxm nxmR) (__eo_eq u uR1))
                              (__eo_eq y yR1))
                            (__eo_eq z zR1))
                          (__eo_eq nyu nyuR))
                        (__eo_eq y yR2))
                      (__eo_eq u uR2))
                    (__eo_eq nyum nyumR))
                  (__eo_eq y yR3))
                (__eo_eq u uR3))
              (__eo_eq nu nuR))
            (__eo_eq u uR4))
          (__eo_eq num numR))
        (__eo_eq u uR5))
      (Term.Boolean true) body ≠ Term.Stuck ->
    nxmR = nxm ∧ uR1 = u ∧ yR1 = y ∧ zR1 = z ∧ nyuR = nyu ∧
      yR2 = y ∧ uR2 = u ∧ nyumR = nyum ∧ yR3 = y ∧ uR3 = u ∧
      nuR = nu ∧ uR4 = u ∧ numR = num ∧ uR5 = u := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  rcases pullup_and_true hGuard with ⟨h13, hu5⟩
  rcases pullup_and_true h13 with ⟨h12, hnum⟩
  rcases pullup_and_true h12 with ⟨h11, hu4⟩
  rcases pullup_and_true h11 with ⟨h10, hnu⟩
  rcases pullup_and_true h10 with ⟨h9, hu3⟩
  rcases pullup_and_true h9 with ⟨h8, hy3⟩
  rcases pullup_and_true h8 with ⟨h7, hnyum⟩
  rcases pullup_and_true h7 with ⟨h6, hu2⟩
  rcases pullup_and_true h6 with ⟨h5, hy2⟩
  rcases pullup_and_true h5 with ⟨h4, hnyu⟩
  rcases pullup_and_true h4 with ⟨h3, hz1⟩
  rcases pullup_and_true h3 with ⟨h2, hy1⟩
  rcases pullup_and_true h2 with ⟨hnxm, hu1⟩
  exact ⟨support_eq_of_eo_eq_true nxm nxmR hnxm,
    support_eq_of_eo_eq_true u uR1 hu1,
    support_eq_of_eo_eq_true y yR1 hy1,
    support_eq_of_eo_eq_true z zR1 hz1,
    support_eq_of_eo_eq_true nyu nyuR hnyu,
    support_eq_of_eo_eq_true y yR2 hy2,
    support_eq_of_eo_eq_true u uR2 hu2,
    support_eq_of_eo_eq_true nyum nyumR hnyum,
    support_eq_of_eo_eq_true y yR3 hy3,
    support_eq_of_eo_eq_true u uR3 hu3,
    support_eq_of_eo_eq_true nu nuR hnu,
    support_eq_of_eo_eq_true u uR4 hu4,
    support_eq_of_eo_eq_true num numR hnum,
    support_eq_of_eo_eq_true u uR5 hu5⟩

def BvConcatPullup3PremiseShape (P1 P2 P3 P4 P5 : Term) : Prop :=
  ∃ nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3
    nuR uR4 numR uR5,
    P1 = bvConcatPullup3Prem1Raw nxmR uR1 yR1 zR1 ∧
    P2 = bvConcatPullup3Prem2Raw nyuR yR2 uR2 ∧
    P3 = bvConcatPullup3Prem3Raw nyumR yR3 uR3 ∧
    P4 = bvConcatPullup3Prem4Raw nuR uR4 ∧
    P5 = bvConcatPullup3Prem5Raw numR uR5

private theorem bvConcatPullup3_premise_shape
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5 : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> u ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    nyu ≠ Term.Stuck -> nyum ≠ Term.Stuck -> nu ≠ Term.Stuck ->
    num ≠ Term.Stuck ->
    bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
      P1 P2 P3 P4 P5 ≠ Term.Stuck ->
    BvConcatPullup3PremiseShape P1 P2 P3 P4 P5 := by
  intro hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum hProg
  by_cases hShape : BvConcatPullup3PremiseShape P1 P2 P3 P4 P5
  · exact hShape
  · exfalso
    apply hProg
    cases op with
    | band =>
      exact __eo_prog_bv_and_concat_pullup3.eq_12
        xs ws y z u nxm nyu nyum nu num
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)
        hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum (by
          intro nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3
            nuR uR4 numR uR5 hP1 hP2 hP3 hP4 hP5
          apply hShape
          exact ⟨nxmR, uR1, yR1, zR1, nyuR, yR2, uR2, nyumR,
            yR3, uR3, nuR, uR4, numR, uR5,
            by simpa [bvConcatPullup3Prem1Raw] using Proof.pf.inj hP1,
            by simpa [bvConcatPullup3Prem2Raw] using Proof.pf.inj hP2,
            by simpa [bvConcatPullup3Prem3Raw] using Proof.pf.inj hP3,
            by simpa [bvConcatPullup3Prem4Raw] using Proof.pf.inj hP4,
            by simpa [bvConcatPullup3Prem5Raw] using Proof.pf.inj hP5⟩)
    | bor =>
      exact __eo_prog_bv_or_concat_pullup3.eq_12
        xs ws y z u nxm nyu nyum nu num
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)
        hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum (by
          intro nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3
            nuR uR4 numR uR5 hP1 hP2 hP3 hP4 hP5
          apply hShape
          exact ⟨nxmR, uR1, yR1, zR1, nyuR, yR2, uR2, nyumR,
            yR3, uR3, nuR, uR4, numR, uR5,
            by simpa [bvConcatPullup3Prem1Raw] using Proof.pf.inj hP1,
            by simpa [bvConcatPullup3Prem2Raw] using Proof.pf.inj hP2,
            by simpa [bvConcatPullup3Prem3Raw] using Proof.pf.inj hP3,
            by simpa [bvConcatPullup3Prem4Raw] using Proof.pf.inj hP4,
            by simpa [bvConcatPullup3Prem5Raw] using Proof.pf.inj hP5⟩)
    | bxor =>
      exact __eo_prog_bv_xor_concat_pullup3.eq_12
        xs ws y z u nxm nyu nyum nu num
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) (Proof.pf P5)
        hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum (by
          intro nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3
            nuR uR4 numR uR5 hP1 hP2 hP3 hP4 hP5
          apply hShape
          exact ⟨nxmR, uR1, yR1, zR1, nyuR, yR2, uR2, nyumR,
            yR3, uR3, nuR, uR4, numR, uR5,
            by simpa [bvConcatPullup3Prem1Raw] using Proof.pf.inj hP1,
            by simpa [bvConcatPullup3Prem2Raw] using Proof.pf.inj hP2,
            by simpa [bvConcatPullup3Prem3Raw] using Proof.pf.inj hP3,
            by simpa [bvConcatPullup3Prem4Raw] using Proof.pf.inj hP4,
            by simpa [bvConcatPullup3Prem5Raw] using Proof.pf.inj hP5⟩)

theorem bvConcatPullup3Program_normalize
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation u ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation nyu ->
    RuleProofs.eo_has_smt_translation nyum ->
    RuleProofs.eo_has_smt_translation nu ->
    RuleProofs.eo_has_smt_translation num ->
    bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
      P1 P2 P3 P4 P5 ≠ Term.Stuck ->
    P1 = bvConcatPullup3Prem1 nxm u y z ∧
      P2 = bvConcatPullup3Prem2 nyu y u ∧
      P3 = bvConcatPullup3Prem3 nyum y u ∧
      P4 = bvConcatPullup3Prem4 nu u ∧
      P5 = bvConcatPullup3Prem5 num u := by
  intro hXsT hWsT hYT hZT hUT hNxmT hNyuT hNyumT hNuT hNumT hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsT
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsT
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYT
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZT
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUT
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmT
  have hNyu := RuleProofs.term_ne_stuck_of_has_smt_translation nyu hNyuT
  have hNyum := RuleProofs.term_ne_stuck_of_has_smt_translation nyum hNyumT
  have hNu := RuleProofs.term_ne_stuck_of_has_smt_translation nu hNuT
  have hNum := RuleProofs.term_ne_stuck_of_has_smt_translation num hNumT
  have hShape := bvConcatPullup3_premise_shape op
    xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5
    hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum hProg
  unfold BvConcatPullup3PremiseShape at hShape
  rcases hShape with
    ⟨nxmR, uR1, yR1, zR1, nyuR, yR2, uR2, nyumR, yR3, uR3,
      nuR, uR4, numR, uR5, hP1, hP2, hP3, hP4, hP5⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4, hP5] at hReq
  cases op with
  | band =>
    simp only [bvConcatPullup3Program, bvConcatPullup3Prem1Raw,
      bvConcatPullup3Prem2Raw, bvConcatPullup3Prem3Raw,
      bvConcatPullup3Prem4Raw, bvConcatPullup3Prem5Raw] at hReq
    rw [__eo_prog_bv_and_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3 nuR uR4 numR uR5
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum] at hReq
    rcases pullup3_guard_refs hReq with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    exact ⟨by simpa [bvConcatPullup3Prem1] using hP1,
      by simpa [bvConcatPullup3Prem2] using hP2,
      by simpa [bvConcatPullup3Prem3] using hP3,
      by simpa [bvConcatPullup3Prem4] using hP4,
      by simpa [bvConcatPullup3Prem5] using hP5⟩
  | bor =>
    simp only [bvConcatPullup3Program, bvConcatPullup3Prem1Raw,
      bvConcatPullup3Prem2Raw, bvConcatPullup3Prem3Raw,
      bvConcatPullup3Prem4Raw, bvConcatPullup3Prem5Raw] at hReq
    rw [__eo_prog_bv_or_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3 nuR uR4 numR uR5
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum] at hReq
    rcases pullup3_guard_refs hReq with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    exact ⟨by simpa [bvConcatPullup3Prem1] using hP1,
      by simpa [bvConcatPullup3Prem2] using hP2,
      by simpa [bvConcatPullup3Prem3] using hP3,
      by simpa [bvConcatPullup3Prem4] using hP4,
      by simpa [bvConcatPullup3Prem5] using hP5⟩
  | bxor =>
    simp only [bvConcatPullup3Program, bvConcatPullup3Prem1Raw,
      bvConcatPullup3Prem2Raw, bvConcatPullup3Prem3Raw,
      bvConcatPullup3Prem4Raw, bvConcatPullup3Prem5Raw] at hReq
    rw [__eo_prog_bv_xor_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxmR uR1 yR1 zR1 nyuR yR2 uR2 nyumR yR3 uR3 nuR uR4 numR uR5
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum] at hReq
    rcases pullup3_guard_refs hReq with
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    exact ⟨by simpa [bvConcatPullup3Prem1] using hP1,
      by simpa [bvConcatPullup3Prem2] using hP2,
      by simpa [bvConcatPullup3Prem3] using hP3,
      by simpa [bvConcatPullup3Prem4] using hP4,
      by simpa [bvConcatPullup3Prem5] using hP5⟩

def bvConcatPullup3HighRaw
    (op : BvConcatPullupOp) (xs ws nxm nyu : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nxm nyu)
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullup3MidRaw
    (op : BvConcatPullupOp) (xs ws nyum nu : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract nyum nu)
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullup3LowRaw
    (op : BvConcatPullupOp) (xs ws num : Term) : Term :=
  __eo_mk_apply (Term.UOp2 UserOp2.extract num (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws)

def bvConcatPullup3RhsRaw
    (op : BvConcatPullupOp)
    (xs ws z y u nxm nyu nyum nu num : Term) : Term :=
  let highExt := bvConcatPullup3HighRaw op xs ws nxm nyu
  let midExt := bvConcatPullup3MidRaw op xs ws nyum nu
  let lowExt := bvConcatPullup3LowRaw op xs ws num
  let highPart := __eo_mk_apply (__eo_mk_apply op.term highExt)
    (__eo_mk_apply (__eo_mk_apply op.term z)
      (__eo_nil op.term (__eo_typeof highExt)))
  let midPart := __eo_mk_apply (__eo_mk_apply op.term midExt)
    (__eo_mk_apply (__eo_mk_apply op.term y)
      (__eo_nil op.term (__eo_typeof midExt)))
  let lowPart := __eo_mk_apply (__eo_mk_apply op.term lowExt)
    (__eo_mk_apply (__eo_mk_apply op.term u)
      (__eo_nil op.term (__eo_typeof lowExt)))
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) highPart)
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) midPart)
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat) lowPart)
        (Term.Binary 0 0)))

def bvConcatPullup3BodyRaw
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (bvConcatPullupTwoLhsRaw op xs ws (bvConcatPullup3Full z y u)))
    (bvConcatPullup3RhsRaw op xs ws z y u nxm nyu nyum nu num)

private theorem bvConcatPullup3RhsRaw_eq
    (op : BvConcatPullupOp)
    (xs ws z y u nxm nyu nyum nu num : Term) :
    bvConcatPullup3RhsRaw op xs ws z y u nxm nyu nyum nu num ≠
      Term.Stuck ->
    bvConcatPullup3RhsRaw op xs ws z y u nxm nyu nyum nu num =
      bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num := by
  intro hRhs
  let hiR := bvConcatPullup3HighRaw op xs ws nxm nyu
  let miR := bvConcatPullup3MidRaw op xs ws nyum nu
  let loR := bvConcatPullup3LowRaw op xs ws num
  let hiTailHead := __eo_mk_apply op.term z
  let hiTail := __eo_mk_apply hiTailHead (__eo_nil op.term (__eo_typeof hiR))
  let hiHead := __eo_mk_apply op.term hiR
  let hi := __eo_mk_apply hiHead hiTail
  let miTailHead := __eo_mk_apply op.term y
  let miTail := __eo_mk_apply miTailHead (__eo_nil op.term (__eo_typeof miR))
  let miHead := __eo_mk_apply op.term miR
  let mi := __eo_mk_apply miHead miTail
  let loTailHead := __eo_mk_apply op.term u
  let loTail := __eo_mk_apply loTailHead (__eo_nil op.term (__eo_typeof loR))
  let loHead := __eo_mk_apply op.term loR
  let lo := __eo_mk_apply loHead loTail
  let loConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) lo
  let loConcat := __eo_mk_apply loConcatHead (Term.Binary 0 0)
  let miConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) mi
  let miConcat := __eo_mk_apply miConcatHead loConcat
  let hiConcatHead := __eo_mk_apply (Term.UOp UserOp.concat) hi
  have hOuter : __eo_mk_apply hiConcatHead miConcat ≠ Term.Stuck := by
    simpa [bvConcatPullup3RhsRaw, hiR, miR, loR, hiTailHead, hiTail,
      hiHead, hi, miTailHead, miTail, miHead, mi, loTailHead, loTail,
      loHead, lo, loConcatHead, loConcat, miConcatHead, miConcat,
      hiConcatHead] using hRhs
  have hHiConcatHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    hiConcatHead miConcat hOuter
  have hMiConcat := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    hiConcatHead miConcat hOuter
  have hHi := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hMiConcatHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    miConcatHead loConcat hMiConcat
  have hLoConcat := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    miConcatHead loConcat hMiConcat
  have hMi := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) mi hMiConcatHead
  have hLoConcatHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck
    loConcatHead (Term.Binary 0 0) hLoConcat
  have hLo := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hHiHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck hiHead hiTail hHi
  have hHiR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term hiR hHiHead
  have hHiTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hMiHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck miHead miTail hMi
  have hMiTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck miHead miTail hMi
  have hMiR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term miR hMiHead
  have hMiTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck miTailHead
    (__eo_nil op.term (__eo_typeof miR)) hMiTail
  have hLoHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoTail := eo_mk_apply_arg_ne_stuck_of_ne_stuck loHead loTail hLo
  have hLoR := eo_mk_apply_arg_ne_stuck_of_ne_stuck op.term loR hLoHead
  have hLoTailHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck loTailHead
    (__eo_nil op.term (__eo_typeof loR)) hLoTail
  have hHiREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nxm nyu)
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hHiR; (try simp [hiR] at hsimpa ⊢); exact hsimpa)
  have hMiREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract nyum nu)
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hMiR; (try simp [miR] at hsimpa ⊢); exact hsimpa)
  have hLoREq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp2 UserOp2.extract num (Term.Numeral 0))
    (bvConcatPullupAggregate op xs ws) (by have hsimpa := hLoR; (try simp [loR] at hsimpa ⊢); exact hsimpa)
  have hHiTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term z hHiTailHead
  have hHiTailEq := eo_mk_apply_eq_apply_of_ne_stuck hiTailHead
    (__eo_nil op.term (__eo_typeof hiR)) hHiTail
  have hHiHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term hiR hHiHead
  have hHiEq := eo_mk_apply_eq_apply_of_ne_stuck hiHead hiTail hHi
  have hMiTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term y hMiTailHead
  have hMiTailEq := eo_mk_apply_eq_apply_of_ne_stuck miTailHead
    (__eo_nil op.term (__eo_typeof miR)) hMiTail
  have hMiHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term miR hMiHead
  have hMiEq := eo_mk_apply_eq_apply_of_ne_stuck miHead miTail hMi
  have hLoTailHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term u hLoTailHead
  have hLoTailEq := eo_mk_apply_eq_apply_of_ne_stuck loTailHead
    (__eo_nil op.term (__eo_typeof loR)) hLoTail
  have hLoHeadEq := eo_mk_apply_eq_apply_of_ne_stuck op.term loR hLoHead
  have hLoEq := eo_mk_apply_eq_apply_of_ne_stuck loHead loTail hLo
  have hLoConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) lo hLoConcatHead
  have hLoConcatEq := eo_mk_apply_eq_apply_of_ne_stuck loConcatHead
    (Term.Binary 0 0) hLoConcat
  have hMiConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) mi hMiConcatHead
  have hMiConcatEq := eo_mk_apply_eq_apply_of_ne_stuck miConcatHead
    loConcat hMiConcat
  have hHiConcatHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.concat) hi hHiConcatHead
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck hiConcatHead miConcat hOuter
  dsimp [bvConcatPullup3RhsRaw, bvConcatPullup3HighRaw,
    bvConcatPullup3MidRaw, bvConcatPullup3LowRaw, hiR, miR, loR,
    hiTailHead, hiTail, hiHead, hi, miTailHead, miTail, miHead, mi,
    loTailHead, loTail, loHead, lo, loConcatHead, loConcat,
    miConcatHead, miConcat, hiConcatHead] at *
  simp only [hHiREq, hMiREq, hLoREq] at *
  rw [hOuterEq, hHiConcatHeadEq, hHiEq, hHiHeadEq, hHiTailEq,
    hHiTailHeadEq, hMiConcatEq, hMiConcatHeadEq, hMiEq, hMiHeadEq,
    hMiTailEq, hMiTailHeadEq, hLoConcatEq, hLoConcatHeadEq,
    hLoEq, hLoHeadEq, hLoTailEq, hLoTailHeadEq]
  rfl

theorem bvConcatPullup3BodyRaw_eq_term
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) :
    bvConcatPullup3BodyRaw op xs ws y z u nxm nyu nyum nu num ≠
      Term.Stuck ->
    bvConcatPullup3BodyRaw op xs ws y z u nxm nyu nyum nu num =
      bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num := by
  intro hBody
  let lhsR := bvConcatPullupTwoLhsRaw op xs ws (bvConcatPullup3Full z y u)
  let rhsR := bvConcatPullup3RhsRaw op xs ws z y u nxm nyu nyum nu num
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhsR
  have hBody' : __eo_mk_apply eqHead rhsR ≠ Term.Stuck := by
    simpa [bvConcatPullup3BodyRaw, lhsR, rhsR, eqHead] using hBody
  have hEqHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hRhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck eqHead rhsR hBody'
  have hLhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hLhsEq := bvConcatPullupTwoLhsRaw_eq op xs ws
    (bvConcatPullup3Full z y u) hLhs
  have hRhsEq := bvConcatPullup3RhsRaw_eq op xs ws z y u
    nxm nyu nyum nu num hRhs
  have hHeadEq := eo_mk_apply_eq_apply_of_ne_stuck
    (Term.UOp UserOp.eq) lhsR hEqHead
  have hOuterEq := eo_mk_apply_eq_apply_of_ne_stuck eqHead rhsR hBody'
  dsimp [bvConcatPullup3BodyRaw, lhsR, rhsR, eqHead]
    at hLhsEq hRhsEq hHeadEq hOuterEq ⊢
  rw [hOuterEq, hHeadEq, hLhsEq, hRhsEq]
  rfl

theorem bvConcatPullup3Program_eq_raw
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) :
    xs ≠ Term.Stuck -> ws ≠ Term.Stuck -> y ≠ Term.Stuck ->
    z ≠ Term.Stuck -> u ≠ Term.Stuck -> nxm ≠ Term.Stuck ->
    nyu ≠ Term.Stuck -> nyum ≠ Term.Stuck -> nu ≠ Term.Stuck ->
    num ≠ Term.Stuck ->
    bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
        (bvConcatPullup3Prem1 nxm u y z)
        (bvConcatPullup3Prem2 nyu y u)
        (bvConcatPullup3Prem3 nyum y u)
        (bvConcatPullup3Prem4 nu u)
        (bvConcatPullup3Prem5 num u) =
      bvConcatPullup3BodyRaw op xs ws y z u nxm nyu nyum nu num := by
  intro hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum
  cases op with
  | band =>
    unfold bvConcatPullup3Program bvConcatPullup3Prem1
      bvConcatPullup3Prem2 bvConcatPullup3Prem3 bvConcatPullup3Prem4
      bvConcatPullup3Prem5 bvConcatPullup3Prem1Raw
      bvConcatPullup3Prem2Raw bvConcatPullup3Prem3Raw
      bvConcatPullup3Prem4Raw bvConcatPullup3Prem5Raw
    rw [__eo_prog_bv_and_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxm u y z nyu y u nyum y u nu u num u
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum]
    simp [bvConcatPullup3BodyRaw, bvConcatPullupTwoLhsRaw,
      bvConcatPullup3RhsRaw, bvConcatPullup3HighRaw,
      bvConcatPullup3MidRaw, bvConcatPullup3LowRaw,
      bvConcatPullup3Full, bvConcatPullupConcat,
      bvConcatPullupAggregate, BvConcatPullupOp.term,
      __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and,
      hXs, hWs, hY, hZ, hU, hNxm, hNyu, hNyum, hNu, hNum]
  | bor =>
    unfold bvConcatPullup3Program bvConcatPullup3Prem1
      bvConcatPullup3Prem2 bvConcatPullup3Prem3 bvConcatPullup3Prem4
      bvConcatPullup3Prem5 bvConcatPullup3Prem1Raw
      bvConcatPullup3Prem2Raw bvConcatPullup3Prem3Raw
      bvConcatPullup3Prem4Raw bvConcatPullup3Prem5Raw
    rw [__eo_prog_bv_or_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxm u y z nyu y u nyum y u nu u num u
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum]
    simp [bvConcatPullup3BodyRaw, bvConcatPullupTwoLhsRaw,
      bvConcatPullup3RhsRaw, bvConcatPullup3HighRaw,
      bvConcatPullup3MidRaw, bvConcatPullup3LowRaw,
      bvConcatPullup3Full, bvConcatPullupConcat,
      bvConcatPullupAggregate, BvConcatPullupOp.term,
      __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and,
      hXs, hWs, hY, hZ, hU, hNxm, hNyu, hNyum, hNu, hNum]
  | bxor =>
    unfold bvConcatPullup3Program bvConcatPullup3Prem1
      bvConcatPullup3Prem2 bvConcatPullup3Prem3 bvConcatPullup3Prem4
      bvConcatPullup3Prem5 bvConcatPullup3Prem1Raw
      bvConcatPullup3Prem2Raw bvConcatPullup3Prem3Raw
      bvConcatPullup3Prem4Raw bvConcatPullup3Prem5Raw
    rw [__eo_prog_bv_xor_concat_pullup3.eq_11 xs ws y z u nxm nyu nyum nu num
      nxm u y z nyu y u nyum y u nu u num u
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum]
    simp [bvConcatPullup3BodyRaw, bvConcatPullupTwoLhsRaw,
      bvConcatPullup3RhsRaw, bvConcatPullup3HighRaw,
      bvConcatPullup3MidRaw, bvConcatPullup3LowRaw,
      bvConcatPullup3Full, bvConcatPullupConcat,
      bvConcatPullupAggregate, BvConcatPullupOp.term,
      __eo_mk_apply, __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and,
      hXs, hWs, hY, hZ, hU, hNxm, hNyu, hNyum, hNu, hNum]

theorem bvConcatPullup3BaseContextFromFull
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) (w : Nat) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    __smtx_typeof (__eo_to_smt (bvConcatPullup3Full z y u)) =
      SmtType.BitVec w ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true ∧
      PullupListTypeOrNil xs w ∧
      __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
        SmtType.BitVec w := by
  intro hXsTrans hWsTrans hFullTy hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup3Lhs op xs ws z y u))
    (__eo_typeof
      (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup3Term] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullup3Lhs op xs ws z y u ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let full := bvConcatPullup3Full z y u
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullup3Lhs, full, tail] using hLhsNe)
  have hXsList := hLists.1
  have hTailList := hLists.2
  have hWsList : __eo_is_list op.term ws = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op.term full ws hTailList
  have hRecTypeNe : __eo_typeof (__eo_list_concat_rec xs tail) ≠
      Term.Stuck := by
    rw [← pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
    simpa [bvConcatPullup3Lhs, full, tail] using hSides.1
  have hTailTypeNe := pullup_list_concat_rec_right_type_non_stuck op xs tail
    hXsList hRecTypeNe
  have hTailTypeNe' :
      __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) ≠
        Term.Stuck := by
    rw [← pullup_typeof_apply op]
    exact hTailTypeNe
  rcases pullup_typeof_bvand_arg_types_of_ne_stuck hTailTypeNe' with
    ⟨width, hFullEoTy, hWsEoTy⟩
  have hFullMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
    full (by rw [show __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w by
      simpa [full] using hFullTy]; simp)
  have hWidthTy :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) width) =
        SmtType.BitVec w := by
    rw [hFullEoTy] at hFullMatch
    exact hFullMatch.symm.trans (by simpa [full] using hFullTy)
  have hWsMatch := TranslationProofs.eo_to_smt_typeof_matches_translation ws
    hWsTrans
  have hWsTy : __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w := by
    rw [hWsEoTy] at hWsMatch
    exact hWsMatch.trans hWidthTy
  have hTailEoTy :
      __eo_typeof tail = Term.Apply (Term.UOp UserOp.BitVec) width := by
    have hReduced :
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) =
          Term.Apply (Term.UOp UserOp.BitVec) width := by
      rw [hFullEoTy, hWsEoTy]
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        subst width
        simp [__eo_to_smt_type] at hWidthTy
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
    rw [show __eo_typeof tail =
        __eo_typeof_bvand (__eo_typeof full) (__eo_typeof ws) by
      simpa [tail] using pullup_typeof_apply op full ws]
    exact hReduced
  have hRecEoTy := pullup_list_concat_rec_result_eo_type op xs tail width
    hXsList hTailEoTy hRecTypeNe
  have hTailNe : tail ≠ Term.Stuck := by
    simp [tail, BvConcatPullupOp.apply]
  have hXsType := pullup_list_type_or_nil_of_concat_eo_type op xs tail
    width w hXsTrans hXsList hTailNe hRecEoTy hWidthTy
  let c := __eo_list_concat op.term xs ws
  have hCList : __eo_is_list op.term c = Term.Boolean true := by
    dsimp [c]
    rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
    exact eo_list_concat_rec_is_list_true_of_lists op.term xs ws
      hXsList hWsList
  have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
    rcases hXsType with hXsTy | hXsNil
    · dsimp [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact op.listConcatRecSmtType xs ws w hXsList hWsList hXsTy hWsTy
    · have hCeq : c = ws := by
        dsimp [c]
        rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList,
          hXsNil ws]
      rw [hCeq]
      exact hWsTy
  have hAggTy := op.listSingletonElimSmtType c w hCList hCTy
  exact ⟨hXsList, hWsList, hXsType, hWsTy,
    by simpa [bvConcatPullupAggregate, c] using hAggTy⟩

theorem bvConcatPullup3RhsEoContext
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) :
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    ∃ wh wm wl : Term,
      __eo_typeof (bvConcatPullup3High op xs ws nxm nyu) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3High op xs ws nxm nyu))) =
          Term.Apply (Term.UOp UserOp.BitVec) wh ∧
      __eo_typeof (bvConcatPullup3Mid op xs ws nyum nu) =
          Term.Apply (Term.UOp UserOp.BitVec) wm ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) wm ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3Mid op xs ws nyum nu))) =
          Term.Apply (Term.UOp UserOp.BitVec) wm ∧
      __eo_typeof (bvConcatPullup3Low op xs ws num) =
          Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof u = Term.Apply (Term.UOp UserOp.BitVec) wl ∧
      __eo_typeof
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3Low op xs ws num))) =
          Term.Apply (Term.UOp UserOp.BitVec) wl := by
  intro hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup3Lhs op xs ws z y u))
    (__eo_typeof
      (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup3Term] at hsimpa ⊢); exact hsimpa)
  let highExt := bvConcatPullup3High op xs ws nxm nyu
  let midExt := bvConcatPullup3Mid op xs ws nyum nu
  let lowExt := bvConcatPullup3Low op xs ws num
  let highTail := op.apply z (__eo_nil op.term (__eo_typeof highExt))
  let midTail := op.apply y (__eo_nil op.term (__eo_typeof midExt))
  let lowTail := op.apply u (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let midPart := op.apply midExt midTail
  let lowPart := op.apply lowExt lowTail
  let lowConcat := bvConcatPullupConcat lowPart (Term.Binary 0 0)
  let midConcat := bvConcatPullupConcat midPart lowConcat
  have hOuter : __eo_typeof_concat (__eo_typeof highPart)
      (__eo_typeof midConcat) ≠ Term.Stuck := by
    have hsimpa := hSides.2
    try simp [bvConcatPullup3Rhs, highExt, midExt, lowExt, highTail, midTail, lowTail, highPart, midPart, lowPart, lowConcat, midConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hOuter with
    ⟨wh, _wrest, hHighPartTy, hMidConcatTy⟩
  have hMidOuter : __eo_typeof_concat (__eo_typeof midPart)
      (__eo_typeof lowConcat) ≠ Term.Stuck := by
    have hNe : __eo_typeof midConcat ≠ Term.Stuck := by
      rw [hMidConcatTy]
      intro h
      cases h
    have hsimpa := hNe
    try simp [midConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hMidOuter with
    ⟨wm, _wlow, hMidPartTy, hLowConcatTy⟩
  have hLowOuter : __eo_typeof_concat (__eo_typeof lowPart)
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hNe : __eo_typeof lowConcat ≠ Term.Stuck := by
      rw [hLowConcatTy]
      intro h
      cases h
    have hsimpa := hNe
    try simp [lowConcat, bvConcatPullupConcat] at hsimpa ⊢
    exact hsimpa
  rcases bvConcat_eo_typeof_concat_args_bitvec hLowOuter with
    ⟨wl, _we, hLowPartTy, _hEmptyTy⟩
  have hHighArgs := pullup_typeof_apply_args_of_result_bitvec op
    highExt highTail wh (by simpa [highPart] using hHighPartTy)
  have hMidArgs := pullup_typeof_apply_args_of_result_bitvec op
    midExt midTail wm (by simpa [midPart] using hMidPartTy)
  have hLowArgs := pullup_typeof_apply_args_of_result_bitvec op
    lowExt lowTail wl (by simpa [lowPart] using hLowPartTy)
  have hHighTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    z (__eo_nil op.term (__eo_typeof highExt)) wh
    (by simpa [highTail] using hHighArgs.2)
  have hMidTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    y (__eo_nil op.term (__eo_typeof midExt)) wm
    (by simpa [midTail] using hMidArgs.2)
  have hLowTailArgs := pullup_typeof_apply_args_of_result_bitvec op
    u (__eo_nil op.term (__eo_typeof lowExt)) wl
    (by simpa [lowTail] using hLowArgs.2)
  exact ⟨wh, wm, wl,
    by simpa [highExt] using hHighArgs.1, hHighTailArgs.1,
    by simpa [highExt] using hHighTailArgs.2,
    by simpa [midExt] using hMidArgs.1, hMidTailArgs.1,
    by simpa [midExt] using hMidTailArgs.2,
    by simpa [lowExt] using hLowArgs.1, hLowTailArgs.1,
    by simpa [lowExt] using hLowTailArgs.2⟩

theorem bvConcatPullup3RhsSmtTypesOfBody
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) (A B C : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec A ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec B ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec C ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvConcatPullup3High op xs ws nxm nyu)) =
        SmtType.BitVec A ∧
      __smtx_typeof
        (__eo_to_smt (op.apply z
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3High op xs ws nxm nyu))))) =
        SmtType.BitVec A ∧
      __smtx_typeof (__eo_to_smt (bvConcatPullup3Mid op xs ws nyum nu)) =
        SmtType.BitVec B ∧
      __smtx_typeof
        (__eo_to_smt (op.apply y
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3Mid op xs ws nyum nu))))) =
        SmtType.BitVec B ∧
      __smtx_typeof (__eo_to_smt (bvConcatPullup3Low op xs ws num)) =
        SmtType.BitVec C ∧
      __smtx_typeof
        (__eo_to_smt (op.apply u
          (__eo_nil op.term
            (__eo_typeof (bvConcatPullup3Low op xs ws num))))) =
        SmtType.BitVec C := by
  intro hAggTrans hZTy hYTy hUTy hBodyTy
  rcases bvConcatPullup3RhsEoContext op xs ws y z u nxm nyu nyum nu num
      hBodyTy with
    ⟨wh, wm, wl, hHighExtEo, hZEo, hHighNilEo,
      hMidExtEo, hYEo, hMidNilEo, hLowExtEo, hUEo, hLowNilEo⟩
  have hHigh := pullup_extract_segment_smt_types op
    (bvConcatPullupAggregate op xs ws) z nxm nyu
    (bvConcatPullup3High op xs ws nxm nyu) A (by rfl)
    hAggTrans hZTy ⟨wh, hHighExtEo, hZEo, hHighNilEo⟩
  have hMid := pullup_extract_segment_smt_types op
    (bvConcatPullupAggregate op xs ws) y nyum nu
    (bvConcatPullup3Mid op xs ws nyum nu) B (by rfl)
    hAggTrans hYTy ⟨wm, hMidExtEo, hYEo, hMidNilEo⟩
  have hLow := pullup_extract_segment_smt_types op
    (bvConcatPullupAggregate op xs ws) u num (Term.Numeral 0)
    (bvConcatPullup3Low op xs ws num) C (by rfl)
    hAggTrans hUTy ⟨wl, hLowExtEo, hUEo, hLowNilEo⟩
  exact ⟨hHigh.1, hHigh.2, hMid.1, hMid.2, hLow.1, hLow.2⟩

theorem bvConcatPullup3Prem1Type (nxm u y z : Term) :
    RuleProofs.eo_has_bool_type (bvConcatPullup3Prem1 nxm u y z) ->
    ∃ wz wy wu : Nat,
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu := by
  intro hPrem
  let sz := Term.Apply (Term.UOp UserOp._at_bvsize) z
  let sy := Term.Apply (Term.UOp UserOp._at_bvsize) y
  let su := Term.Apply (Term.UOp UserOp._at_bvsize) u
  let pz := Term.Apply (Term.Apply (Term.UOp UserOp.plus) sz) (Term.Numeral 0)
  let py := Term.Apply (Term.Apply (Term.UOp UserOp.plus) sy) pz
  let pu := Term.Apply (Term.Apply (Term.UOp UserOp.plus) su) py
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg) pu) (Term.Numeral 1)
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type nxm rhs
      (by simpa [bvConcatPullup3Prem1, bvConcatPullup3Prem1Raw,
        sz, sy, su, pz, py, pu, rhs] using hPrem) with
    ⟨hSame, hNxmNN⟩
  have hRhsNN : __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
    rw [← hSame]
    exact hNxmNN
  have hNegNN : term_has_non_none_type
      (SmtTerm.neg (__eo_to_smt pu) (SmtTerm.Numeral 1)) := by
    unfold term_has_non_none_type
    have hsimpa := hRhsNN
    try simp [rhs] at hsimpa ⊢
    exact hsimpa
  have hBvsizeNeReal (t : Term) :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) ≠
        SmtType.Real := by
    intro hReal
    have hNN : __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) ≠
        SmtType.None := by
      rw [hReal]
      intro h
      cases h
    rcases bvConcat_bvsize_smt_type_of_non_none t hNN with
      ⟨_w, _hTy, hInt⟩
    rw [hReal] at hInt
    cases hInt
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt pu) (SmtTerm.Numeral 1)) hNegNN with
    hNegArgs | hNegArgs
  · have hPuTy := hNegArgs.1
    change __smtx_typeof (SmtTerm.plus
      (__eo_to_smt su) (__eo_to_smt py)) = SmtType.Int at hPuTy
    have hPuNN : term_has_non_none_type (SmtTerm.plus
        (__eo_to_smt su) (__eo_to_smt py)) := by
      unfold term_has_non_none_type
      rw [hPuTy]
      intro h
      cases h
    rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
        (typeof_plus_eq (__eo_to_smt su) (__eo_to_smt py)) hPuNN with
      hPuArgs | hPuArgs
    · have hPyTy := hPuArgs.2
      change __smtx_typeof (SmtTerm.plus
        (__eo_to_smt sy) (__eo_to_smt pz)) = SmtType.Int at hPyTy
      have hPyNN : term_has_non_none_type (SmtTerm.plus
          (__eo_to_smt sy) (__eo_to_smt pz)) := by
        unfold term_has_non_none_type
        rw [hPyTy]
        intro h
        cases h
      rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
          (typeof_plus_eq (__eo_to_smt sy) (__eo_to_smt pz)) hPyNN with
        hPyArgs | hPyArgs
      · have hPzTy := hPyArgs.2
        change __smtx_typeof (SmtTerm.plus
          (__eo_to_smt sz) (SmtTerm.Numeral 0)) = SmtType.Int at hPzTy
        have hPzNN : term_has_non_none_type (SmtTerm.plus
            (__eo_to_smt sz) (SmtTerm.Numeral 0)) := by
          unfold term_has_non_none_type
          rw [hPzTy]
          intro h
          cases h
        rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
            (typeof_plus_eq (__eo_to_smt sz) (SmtTerm.Numeral 0)) hPzNN with
          hPzArgs | hPzArgs
        · rcases bvConcat_bvsize_smt_type_inv u
              (by simpa [su] using hPuArgs.1) with ⟨wu, hUTy⟩
          rcases bvConcat_bvsize_smt_type_inv y
              (by simpa [sy] using hPyArgs.1) with ⟨wy, hYTy⟩
          rcases bvConcat_bvsize_smt_type_inv z
              (by simpa [sz] using hPzArgs.1) with ⟨wz, hZTy⟩
          exact ⟨wz, wy, wu, hZTy, hYTy, hUTy⟩
        · have hZeroReal := hPzArgs.2
          change SmtType.Int = SmtType.Real at hZeroReal
          cases hZeroReal
      · exact (hBvsizeNeReal y (by simpa [sy] using hPyArgs.1)).elim
    · exact (hBvsizeNeReal u (by simpa [su] using hPuArgs.1)).elim
  · have hOneReal := hNegArgs.2
    change SmtType.Int = SmtType.Real at hOneReal
    cases hOneReal

theorem bvConcatPullup3FullType
    (z y u : Term) (wz wy wu : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    __smtx_typeof (__eo_to_smt (bvConcatPullup3Full z y u)) =
      SmtType.BitVec (wz + (wy + (wu + 0))) := by
  intro hZTy hYTy hUTy
  have hUEmpty := bvConcat_term_smt_type u (Term.Binary 0 0) wu 0
    hUTy bvConcat_empty_smt_type
  have hYTail := bvConcat_term_smt_type y
    (bvConcatPullupConcat u (Term.Binary 0 0)) wy (wu + 0) hYTy
    (by have hsimpa := hUEmpty; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hFull := bvConcat_term_smt_type z
    (bvConcatPullupConcat y
      (bvConcatPullupConcat u (Term.Binary 0 0)))
    wz (wy + (wu + 0)) hZTy
    (by have hsimpa := hYTail; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hsimpa := hFull
  try simp [bvConcatPullup3Full, bvConcatPullupConcat] at hsimpa ⊢
  exact hsimpa

theorem typed_bvConcatPullup3Term
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup3Prem1 nxm u y z) ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) := by
  intro hXsTrans hWsTrans hP1Bool hBodyTy
  rcases bvConcatPullup3Prem1Type nxm u y z hP1Bool with
    ⟨wz, wy, wu, hZTy, hYTy, hUTy⟩
  have hFullTy := bvConcatPullup3FullType z y u wz wy wu hZTy hYTy hUTy
  have hBase := bvConcatPullup3BaseContextFromFull op
    xs ws y z u nxm nyu nyum nu num (wz + (wy + (wu + 0)))
    hXsTrans hWsTrans hFullTy hBodyTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2]
    intro h
    cases h
  have hComp := bvConcatPullup3RhsSmtTypesOfBody op
    xs ws y z u nxm nyu nyum nu num wz wy wu hAggTrans
    hZTy hYTy hUTy hBodyTy
  let highExt := bvConcatPullup3High op xs ws nxm nyu
  let midExt := bvConcatPullup3Mid op xs ws nyum nu
  let lowExt := bvConcatPullup3Low op xs ws num
  let highTail := op.apply z (__eo_nil op.term (__eo_typeof highExt))
  let midTail := op.apply y (__eo_nil op.term (__eo_typeof midExt))
  let lowTail := op.apply u (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let midPart := op.apply midExt midTail
  let lowPart := op.apply lowExt lowTail
  have hLhsTy : __smtx_typeof
      (__eo_to_smt (bvConcatPullup3Lhs op xs ws z y u)) =
      SmtType.BitVec (wz + (wy + (wu + 0))) :=
    bvConcatPullupListSmtType op xs ws (bvConcatPullup3Full z y u)
      (wz + (wy + (wu + 0))) hBase.1 hBase.2.1 hBase.2.2.1
      hBase.2.2.2.1 hFullTy
  have hHighPartTy : __smtx_typeof (__eo_to_smt highPart) =
      SmtType.BitVec wz := op.binarySmtType highExt highTail wz
        (by simpa [highExt] using hComp.1)
        (by simpa [highTail, highExt] using hComp.2.1)
  have hMidPartTy : __smtx_typeof (__eo_to_smt midPart) =
      SmtType.BitVec wy := op.binarySmtType midExt midTail wy
        (by simpa [midExt] using hComp.2.2.1)
        (by simpa [midTail, midExt] using hComp.2.2.2.1)
  have hLowPartTy : __smtx_typeof (__eo_to_smt lowPart) =
      SmtType.BitVec wu := op.binarySmtType lowExt lowTail wu
        (by simpa [lowExt] using hComp.2.2.2.2.1)
        (by simpa [lowTail, lowExt] using hComp.2.2.2.2.2)
  have hLowConcat := bvConcat_term_smt_type lowPart (Term.Binary 0 0)
    wu 0 hLowPartTy bvConcat_empty_smt_type
  have hMidConcat := bvConcat_term_smt_type midPart
    (bvConcatPullupConcat lowPart (Term.Binary 0 0)) wy (wu + 0)
    hMidPartTy (by have hsimpa := hLowConcat; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
  have hRhsTy : __smtx_typeof
      (__eo_to_smt
        (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num)) =
      SmtType.BitVec (wz + (wy + (wu + 0))) := by
    have hOuter := bvConcat_term_smt_type highPart
      (bvConcatPullupConcat midPart
        (bvConcatPullupConcat lowPart (Term.Binary 0 0)))
      wz (wy + (wu + 0)) hHighPartTy
      (by have hsimpa := hMidConcat; (try simp [bvConcatPullupConcat] at hsimpa ⊢); exact hsimpa)
    have hsimpa := hOuter
    try simp [bvConcatPullup3Rhs, highExt, midExt, lowExt, highTail, midTail, lowTail, highPart, midPart, lowPart] at hsimpa ⊢
    exact hsimpa
  unfold bvConcatPullup3Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvConcatPullup3Lhs op xs ws z y u)
    (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num)
    (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; intro h; cases h)

theorem bvConcatPullup3Prem1Eval
    (M : SmtModel) (nxm u y z : Term) (wz wy wu : Nat) :
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    eo_interprets M (bvConcatPullup3Prem1 nxm u y z) true ->
    __smtx_model_eval M (__eo_to_smt nxm) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + wy + wu))
          (native_zneg 1)) := by
  intro hZTy hYTy hUTy hPrem
  have hZSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M z wz hZTy
  have hYSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M y wy hYTy
  have hUSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M u wu hUTy
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
      (Term.Apply (Term.UOp UserOp._at_bvsize) u))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.UOp UserOp._at_bvsize) y))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
          (Term.Apply (Term.UOp UserOp._at_bvsize) z))
          (Term.Numeral 0))))) (Term.Numeral 1)
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nxm rhs
    (by simpa [bvConcatPullup3Prem1, bvConcatPullup3Prem1Raw, rhs]
      using hPrem)
  have hRhsEvalSmt : __smtx_model_eval M
      (SmtTerm.neg
        (SmtTerm.plus
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u))
          (SmtTerm.plus
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y))
            (SmtTerm.plus
              (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) z))
              (SmtTerm.Numeral 0))))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + wy + wu))
          (native_zneg 1)) := by
    change __smtx_model_eval__
        (__smtx_model_eval_plus
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u)))
          (__smtx_model_eval_plus
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)))
            (__smtx_model_eval_plus
              (__smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) z)))
              (SmtValue.Numeral 0))))
        (SmtValue.Numeral 1) = _
    rw [hUSize, hYSize, hZSize]
    simp [__smtx_model_eval, __smtx_model_eval__,
      __smtx_model_eval_plus, native_zplus,
      native_zneg, native_nat_to_int, Smtm.native_nat_to_int]
    push_cast
    omega
  have hRhsEval : __smtx_model_eval M (__eo_to_smt rhs) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wz + wy + wu))
          (native_zneg 1)) := by
    have hsimpa := hRhsEvalSmt
    try simp [rhs] at hsimpa ⊢
    exact hsimpa
  rw [hRhsEval] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup3Prem2Eval
    (M : SmtModel) (nyu y u : Term) (wy wu : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    eo_interprets M (bvConcatPullup3Prem2 nyu y u) true ->
    __smtx_model_eval M (__eo_to_smt nyu) =
      SmtValue.Numeral (native_nat_to_int (wy + wu)) := by
  intro hYTy hUTy hPrem
  have hYSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M y wy hYTy
  have hUSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M u wu hUTy
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.plus)
    (Term.Apply (Term.UOp UserOp._at_bvsize) y))
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
      (Term.Apply (Term.UOp UserOp._at_bvsize) u)) (Term.Numeral 0))
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nyu rhs
    (by simpa [bvConcatPullup3Prem2, bvConcatPullup3Prem2Raw, rhs]
      using hPrem)
  have hRhsEvalSmt : __smtx_model_eval M
      (SmtTerm.plus
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y))
        (SmtTerm.plus
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u))
          (SmtTerm.Numeral 0))) =
      SmtValue.Numeral (native_nat_to_int (wy + wu)) := by
    change __smtx_model_eval_plus
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)))
        (__smtx_model_eval_plus
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u)))
          (SmtValue.Numeral 0)) = _
    rw [hYSize, hUSize]
    simp [__smtx_model_eval, __smtx_model_eval__,
      __smtx_model_eval_plus, native_zplus,
      native_nat_to_int, Smtm.native_nat_to_int]
  have hRhsEval : __smtx_model_eval M (__eo_to_smt rhs) =
      SmtValue.Numeral (native_nat_to_int (wy + wu)) := by
    have hsimpa := hRhsEvalSmt
    try simp [rhs] at hsimpa ⊢
    exact hsimpa
  rw [hRhsEval] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup3Prem3Eval
    (M : SmtModel) (nyum y u : Term) (wy wu : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    eo_interprets M (bvConcatPullup3Prem3 nyum y u) true ->
    __smtx_model_eval M (__eo_to_smt nyum) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wy + wu)) (native_zneg 1)) := by
  intro hYTy hUTy hPrem
  have hYSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M y wy hYTy
  have hUSize := bvConcat_eval_bvsize_of_smt_bitvec_nat M u wu hUTy
  let sum := Term.Apply (Term.Apply (Term.UOp UserOp.plus)
    (Term.Apply (Term.UOp UserOp._at_bvsize) y))
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
      (Term.Apply (Term.UOp UserOp._at_bvsize) u)) (Term.Numeral 0))
  let rhs := Term.Apply (Term.Apply (Term.UOp UserOp.neg) sum)
    (Term.Numeral 1)
  have hEq := bvConcat_model_eval_eq_true_of_eo_eq_true M nyum rhs
    (by simpa [bvConcatPullup3Prem3, bvConcatPullup3Prem3Raw, sum, rhs]
      using hPrem)
  have hRhsEvalSmt : __smtx_model_eval M
      (SmtTerm.neg
        (SmtTerm.plus
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y))
          (SmtTerm.plus
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u))
            (SmtTerm.Numeral 0)))
        (SmtTerm.Numeral 1)) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wy + wu)) (native_zneg 1)) := by
    change __smtx_model_eval__
        (__smtx_model_eval_plus
          (__smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) y)))
          (__smtx_model_eval_plus
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) u)))
            (SmtValue.Numeral 0)))
        (SmtValue.Numeral 1) = _
    rw [hYSize, hUSize]
    simp [__smtx_model_eval, __smtx_model_eval__,
      __smtx_model_eval_plus, native_zplus,
      native_zneg, native_nat_to_int, Smtm.native_nat_to_int]
  have hRhsEval : __smtx_model_eval M (__eo_to_smt rhs) =
      SmtValue.Numeral
        (native_zplus (native_nat_to_int (wy + wu)) (native_zneg 1)) := by
    have hsimpa := hRhsEvalSmt
    try simp [rhs, sum] at hsimpa ⊢
    exact hsimpa
  rw [hRhsEval] at hEq
  exact pullup_model_eval_eq_numeral_left _ _ hEq

theorem bvConcatPullup3Indices
    (M : SmtModel) (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) (wz wy wu : Nat) :
    RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (wz + wy + wu) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup3Prem1 nxm u y z) true ->
    eo_interprets M (bvConcatPullup3Prem2 nyu y u) true ->
    eo_interprets M (bvConcatPullup3Prem3 nyum y u) true ->
    eo_interprets M (bvConcatPullup3Prem4 nu u) true ->
    eo_interprets M (bvConcatPullup3Prem5 num u) true ->
    nxm = Term.Numeral (native_nat_to_int (wz + wy + wu - 1)) ∧
      nyu = Term.Numeral (native_nat_to_int (wy + wu)) ∧
      nyum = Term.Numeral (native_nat_to_int (wy + wu - 1)) ∧
      nu = Term.Numeral (native_nat_to_int wu) ∧
      num = Term.Numeral (native_nat_to_int (wu - 1)) ∧
      0 < wz ∧ 0 < wy ∧ 0 < wu := by
  intro hAggTrans hAggTy hZTy hYTy hUTy hBodyTy hP1 hP2 hP3 hP4 hP5
  rcases bvConcatPullup3RhsEoContext op xs ws y z u nxm nyu nyum nu num
      hBodyTy with
    ⟨_wh, _wm, _wl, hHighEo, _hZ, _hHN, hMidEo, _hY, _hMN,
      hLowEo, _hU, _hLN⟩
  have hHighNe : __eo_typeof (bvConcatPullup3High op xs ws nxm nyu) ≠
      Term.Stuck := by rw [hHighEo]; intro h; cases h
  have hMidNe : __eo_typeof (bvConcatPullup3Mid op xs ws nyum nu) ≠
      Term.Stuck := by rw [hMidEo]; intro h; cases h
  have hLowNe : __eo_typeof (bvConcatPullup3Low op xs ws num) ≠
      Term.Stuck := by rw [hLowEo]; intro h; cases h
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nxm nyu hAggTrans
      (by simpa [bvConcatPullup3High, bvConcatPullupExtract, bvExtractTerm]
        using hHighNe) with
    ⟨wH, hH, lH, _hAEH, hNxm, hNyu, hwH0, _hlH0, _hhHw,
      hHighWidth, hAggSmtH⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) nyum nu hAggTrans
      (by simpa [bvConcatPullup3Mid, bvConcatPullupExtract, bvExtractTerm]
        using hMidNe) with
    ⟨wM, hMhi, lM, _hAEM, hNyum, hNu, hwM0, _hlM0, _hhMw,
      hMidWidth, hAggSmtM⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatPullupAggregate op xs ws) num (Term.Numeral 0) hAggTrans
      (by simpa [bvConcatPullup3Low, bvConcatPullupExtract, bvExtractTerm]
        using hLowNe) with
    ⟨wL, hL, lL, _hAEL, hNum, hZero, hwL0, _hlL0, _hhLw,
      hLowWidth, hAggSmtL⟩
  have hWidth (wi : native_Int) (hwi0 : native_zleq 0 wi = true)
      (hSmt : __smtx_typeof (__eo_to_smt
        (bvConcatPullupAggregate op xs ws)) =
        SmtType.BitVec (native_int_to_nat wi)) :
      wi = native_nat_to_int (wz + wy + wu) := by
    have hn : native_int_to_nat wi = wz + wy + wu := by
      rw [hAggTy] at hSmt
      injection hSmt with h
      exact h.symm
    have hr := native_int_to_nat_roundtrip wi hwi0
    rw [hn] at hr
    exact hr.symm
  have hWH := hWidth wH hwH0 hAggSmtH
  have hWM := hWidth wM hwM0 hAggSmtM
  have hWL := hWidth wL hwL0 hAggSmtL
  have hHHRaw : hH = native_zplus
      (native_nat_to_int (wz + wy + wu)) (native_zneg 1) := by
    have hEval := bvConcatPullup3Prem1Eval M nxm u y z wz wy wu
      hZTy hYTy hUTy hP1
    rw [hNxm] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLH : lH = native_nat_to_int (wy + wu) := by
    have hEval := bvConcatPullup3Prem2Eval M nyu y u wy wu hYTy hUTy hP2
    rw [hNyu] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hMHRaw : hMhi = native_zplus
      (native_nat_to_int (wy + wu)) (native_zneg 1) := by
    have hEval := bvConcatPullup3Prem3Eval M nyum y u wy wu hYTy hUTy hP3
    rw [hNyum] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hML : lM = native_nat_to_int wu := by
    have hEval := bvConcatPullup1Prem1Eval M nu u wu hUTy
      (by simpa [bvConcatPullup3Prem4, bvConcatPullup3Prem4Raw,
        bvConcatPullup1Prem1, bvConcatPullup1Prem1Raw] using hP4)
    rw [hNu] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLLRaw : hL = native_zplus
      (native_nat_to_int wu) (native_zneg 1) := by
    have hEval := bvConcatPullup1Prem3Eval M num u wu hUTy
      (by simpa [bvConcatPullup3Prem5, bvConcatPullup3Prem5Raw,
        bvConcatPullup1Prem3, bvConcatPullup1Prem3Raw] using hP5)
    rw [hNum] at hEval
    rw [__smtx_model_eval.eq_def] at hEval <;> simp only at hEval
    injection hEval
  have hLZero : lL = 0 := by injection hZero with h; exact h.symm
  have hWuPos : 0 < wu := by
    rw [hLLRaw, hLZero] at hLowWidth
    have hIntRaw : (0 : Int) < (↑wu : Int) + -1 + 1 := by
      simpa [SmtEval.native_zlt, SmtEval.native_zplus,
        SmtEval.native_zneg, native_nat_to_int,
        Smtm.native_nat_to_int] using hLowWidth
    have hInt : (0 : Int) < ↑wu := by
      omega
    exact_mod_cast hInt
  have hWyPos : 0 < wy := by
    rw [hMHRaw, hML] at hMidWidth
    have hIntRaw : (0 : Int) <
        (↑(wy + wu) : Int) + -1 + 1 + -↑wu := by
      have hsimpa := hMidWidth
      try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hInt : (0 : Int) < ↑wy := by
      push_cast
      omega
    exact_mod_cast hInt
  have hWzPos : 0 < wz := by
    rw [hHHRaw, hLH] at hHighWidth
    have hIntRaw : (0 : Int) <
        (↑(wz + wy + wu) : Int) + -1 + 1 + -↑(wy + wu) := by
      have hsimpa := hHighWidth
      try simp [SmtEval.native_zlt, SmtEval.native_zplus, SmtEval.native_zneg, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hInt : (0 : Int) < ↑wz := by
      push_cast
      omega
    exact_mod_cast hInt
  have hHH : hH = native_nat_to_int (wz + wy + wu - 1) := by
    rw [hHHRaw]
    change (↑(wz + wy + wu) : Int) + -1 = ↑(wz + wy + wu - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wz + wy + wu)]
    push_cast
    omega
  have hMH : hMhi = native_nat_to_int (wy + wu - 1) := by
    rw [hMHRaw]
    change (↑(wy + wu) : Int) + -1 = ↑(wy + wu - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wy + wu)]
    push_cast
    omega
  have hLL : hL = native_nat_to_int (wu - 1) := by
    rw [hLLRaw]
    change (↑wu : Int) + -1 = ↑(wu - 1)
    rw [Int.ofNat_sub (by omega : 1 ≤ wu)]
    push_cast
    omega
  exact ⟨hNxm.trans (congrArg Term.Numeral hHH),
    hNyu.trans (congrArg Term.Numeral hLH),
    hNyum.trans (congrArg Term.Numeral hMH),
    hNu.trans (congrArg Term.Numeral hML),
    hNum.trans (congrArg Term.Numeral hLL), hWzPos, hWyPos, hWuPos⟩

theorem eval_bvConcatPullup3
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) (wz wy wu : Nat) :
    __eo_is_list op.term xs = Term.Boolean true ->
    __eo_is_list op.term ws = Term.Boolean true ->
    PullupListTypeOrNil xs (wz + wy + wu) ->
    __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec (wz + wy + wu) ->
    __smtx_typeof
        (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
      SmtType.BitVec (wz + wy + wu) ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt u) = SmtType.BitVec wu ->
    nxm = Term.Numeral (native_nat_to_int (wz + wy + wu - 1)) ->
    nyu = Term.Numeral (native_nat_to_int (wy + wu)) ->
    nyum = Term.Numeral (native_nat_to_int (wy + wu - 1)) ->
    nu = Term.Numeral (native_nat_to_int wu) ->
    num = Term.Numeral (native_nat_to_int (wu - 1)) ->
    0 < wz -> 0 < wy -> 0 < wu ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatPullup3Lhs op xs ws z y u)) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num)) := by
  intro hXsList hWsList hXsType hWsTy hAggTy hZTy hYTy hUTy
    hNxm hNyu hNyum hNu hNum hWzPos hWyPos hWuPos hBodyTy
  have hFullTy0 := bvConcatPullup3FullType z y u wz wy wu hZTy hYTy hUTy
  have hFullTy : __smtx_typeof (__eo_to_smt (bvConcatPullup3Full z y u)) =
      SmtType.BitVec (wz + wy + wu) := by
    simpa [Nat.add_assoc] using hFullTy0
  have hLhsEval := bvConcatPullupListEval M hM op xs ws
    (bvConcatPullup3Full z y u) (wz + wy + wu)
    hXsList hWsList hXsType hWsTy hFullTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hAggTy]
    intro h
    cases h
  have hRhsTypes := bvConcatPullup3RhsSmtTypesOfBody op
    xs ws y z u nxm nyu nyum nu num wz wy wu hAggTrans
    hZTy hYTy hUTy hBodyTy
  let agg := bvConcatPullupAggregate op xs ws
  let full := bvConcatPullup3Full z y u
  let highExt := bvConcatPullup3High op xs ws nxm nyu
  let midExt := bvConcatPullup3Mid op xs ws nyum nu
  let lowExt := bvConcatPullup3Low op xs ws num
  let highTail := op.apply z (__eo_nil op.term (__eo_typeof highExt))
  let midTail := op.apply y (__eo_nil op.term (__eo_typeof midExt))
  let lowTail := op.apply u (__eo_nil op.term (__eo_typeof lowExt))
  let highPart := op.apply highExt highTail
  let midPart := op.apply midExt midTail
  let lowPart := op.apply lowExt lowTail
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt agg)
      (wz + wy + wu) (by simpa [agg] using hAggTy) with
    ⟨pa, hAggEval, hAggCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt full)
      (wz + wy + wu) (by simpa [full] using hFullTy) with
    ⟨pf, hFullEval, hFullCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z)
      wz hZTy with ⟨pz, hZEval, hZCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y)
      wy hYTy with ⟨py, hYEval, hYCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt u)
      wu hUTy with ⟨pu, hUEval, hUCan⟩
  have hNatWidth0 : ∀ w : Nat,
      native_zleq 0 (native_nat_to_int w) = true := by
    intro w
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hAggRange := bitvec_payload_range_of_canonical
    (hNatWidth0 (wz + wy + wu)) hAggCan
  have hFullRange := bitvec_payload_range_of_canonical
    (hNatWidth0 (wz + wy + wu)) hFullCan
  have hZRange := bitvec_payload_range_of_canonical (hNatWidth0 wz) hZCan
  have hYRange := bitvec_payload_range_of_canonical (hNatWidth0 wy) hYCan
  have hURange := bitvec_payload_range_of_canonical (hNatWidth0 wu) hUCan
  have hAgg0 : 0 ≤ pa := hAggRange.1
  have hAgg1 : pa < (2 : Int) ^ (wz + wy + wu) := by
    have hsimpa := hAggRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hFull0 : 0 ≤ pf := hFullRange.1
  have hFull1 : pf < (2 : Int) ^ (wz + wy + wu) := by
    have hsimpa := hFullRange.2
    try simp [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  have hZ0 : 0 ≤ pz := hZRange.1
  have hZ1 : pz < (2 : Int) ^ wz := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hZRange.2
  have hY0 : 0 ≤ py := hYRange.1
  have hY1 : py < (2 : Int) ^ wy := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hYRange.2
  have hU0 : 0 ≤ pu := hURange.1
  have hU1 : pu < (2 : Int) ^ wu := by
    simpa [natpow2_eq, native_nat_to_int, Smtm.native_nat_to_int]
      using hURange.2
  have hUEmpty0 := bvConcat_eval_right_empty M hM u wu hUTy
  have hUEmpty : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat u (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt u) := by
    simpa [bvConcatPullupConcat, bvConcatTerm] using hUEmpty0
  have hFullAsThree :
      SmtValue.Binary ↑(wz + wy + wu) pf =
        __smtx_model_eval_concat (SmtValue.Binary ↑wz pz)
          (__smtx_model_eval_concat
            (SmtValue.Binary ↑wy py) (SmtValue.Binary ↑wu pu)) := by
    calc
      _ = __smtx_model_eval M (__eo_to_smt full) := hFullEval.symm
      _ = __smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt z))
          (__smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt y))
            (__smtx_model_eval M
              (__eo_to_smt (bvConcatPullupConcat u (Term.Binary 0 0))))) := by
        rfl
      _ = _ := by
        rw [hUEmpty, hZEval, hYEval, hUEval]
        simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hFullHigh :
      __smtx_model_eval_extract
          (SmtValue.Numeral ↑(wz + wy + wu - 1))
          (SmtValue.Numeral ↑(wy + wu))
          (SmtValue.Binary ↑(wz + wy + wu) pf) =
        SmtValue.Binary ↑wz pz := by
    rw [hFullAsThree]
    exact bvConcat_extract_high_three_value wz wy wu pz py pu
      hZ0 hZ1 hY0 hY1 hU0 hU1 hWzPos
  have hFullMid :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wy + wu - 1))
          (SmtValue.Numeral ↑wu)
          (SmtValue.Binary ↑(wz + wy + wu) pf) =
        SmtValue.Binary ↑wy py := by
    rw [hFullAsThree]
    exact bvConcat_extract_mid_three_value wz wy wu pz py pu
      hZ0 hZ1 hY0 hY1 hU0 hU1 hWyPos
  have hFullLow :
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wu - 1))
          (SmtValue.Numeral 0)
          (SmtValue.Binary ↑(wz + wy + wu) pf) =
        SmtValue.Binary ↑wu pu := by
    rw [hFullAsThree]
    exact bvConcat_extract_low_three_value wz wy wu pz py pu
      hZ0 hZ1 hY0 hY1 hU0 hU1 hWuPos
  have hHighExtEval : __smtx_model_eval M (__eo_to_smt highExt) =
      __smtx_model_eval_extract
        (SmtValue.Numeral ↑(wz + wy + wu - 1))
        (SmtValue.Numeral ↑(wy + wu))
        (SmtValue.Binary ↑(wz + wy + wu) pa) := by
    unfold highExt bvConcatPullup3High bvConcatPullupExtract
    rw [hNxm, hNyu]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (wz + wy + wu - 1)))
          (SmtTerm.Numeral (native_nat_to_int (wy + wu)))
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hMidExtEval : __smtx_model_eval M (__eo_to_smt midExt) =
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wy + wu - 1))
        (SmtValue.Numeral ↑wu)
        (SmtValue.Binary ↑(wz + wy + wu) pa) := by
    unfold midExt bvConcatPullup3Mid bvConcatPullupExtract
    rw [hNyum, hNu]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (wy + wu - 1)))
          (SmtTerm.Numeral (native_nat_to_int wu))
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hLowExtEval : __smtx_model_eval M (__eo_to_smt lowExt) =
      __smtx_model_eval_extract (SmtValue.Numeral ↑(wu - 1))
        (SmtValue.Numeral 0)
        (SmtValue.Binary ↑(wz + wy + wu) pa) := by
    unfold lowExt bvConcatPullup3Low bvConcatPullupExtract
    rw [hNum]
    change __smtx_model_eval M
        (SmtTerm.extract
          (SmtTerm.Numeral (native_nat_to_int (wu - 1)))
          (SmtTerm.Numeral 0)
          (__eo_to_smt (bvConcatPullupAggregate op xs ws))) = _
    rw [smtx_eval_extract_term_eq, hAggEval]
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hHighTailEval : __smtx_model_eval M (__eo_to_smt highTail) =
      __smtx_model_eval M (__eo_to_smt z) :=
    bvConcatPullupEvalApplyGeneratedNil M hM op z
      (__eo_typeof highExt) wz wz
      (by simpa [highExt] using
        pullup_eo_typeof_eq_bitvec_of_smt_bitvec _ wz hRhsTypes.1)
      hZTy
      (by simpa [highTail] using hRhsTypes.2.1)
  have hMidTailEval : __smtx_model_eval M (__eo_to_smt midTail) =
      __smtx_model_eval M (__eo_to_smt y) :=
    bvConcatPullupEvalApplyGeneratedNil M hM op y
      (__eo_typeof midExt) wy wy
      (by simpa [midExt] using
        pullup_eo_typeof_eq_bitvec_of_smt_bitvec _ wy hRhsTypes.2.2.1)
      hYTy
      (by simpa [midTail] using hRhsTypes.2.2.2.1)
  have hLowTailEval : __smtx_model_eval M (__eo_to_smt lowTail) =
      __smtx_model_eval M (__eo_to_smt u) :=
    bvConcatPullupEvalApplyGeneratedNil M hM op u
      (__eo_typeof lowExt) wu wu
      (by
        have hLowExtEo := pullup_eo_typeof_eq_bitvec_of_smt_bitvec
          (bvConcatPullup3Low op xs ws num) wu hRhsTypes.2.2.2.2.1
        simpa [lowExt] using hLowExtEo)
      hUTy
      (by simpa [lowTail] using hRhsTypes.2.2.2.2.2)
  have hHighPartEval : __smtx_model_eval M (__eo_to_smt highPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt highExt))
        (__smtx_model_eval M (__eo_to_smt z)) := by
    rw [show __smtx_model_eval M (__eo_to_smt highPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt highTail)) by
      simpa [highPart] using op.evalApply M highExt highTail,
      hHighTailEval]
  have hMidPartEval : __smtx_model_eval M (__eo_to_smt midPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt midExt))
        (__smtx_model_eval M (__eo_to_smt y)) := by
    rw [show __smtx_model_eval M (__eo_to_smt midPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt midExt))
          (__smtx_model_eval M (__eo_to_smt midTail)) by
      simpa [midPart] using op.evalApply M midExt midTail,
      hMidTailEval]
  have hLowPartEval : __smtx_model_eval M (__eo_to_smt lowPart) =
      op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
        (__smtx_model_eval M (__eo_to_smt u)) := by
    rw [show __smtx_model_eval M (__eo_to_smt lowPart) =
        op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
          (__smtx_model_eval M (__eo_to_smt lowTail)) by
      simpa [lowPart] using op.evalApply M lowExt lowTail,
      hLowTailEval]
  have hLowPartTy := op.binarySmtType lowExt lowTail wu
    (by simpa [lowExt] using hRhsTypes.2.2.2.2.1)
    (by simpa [lowTail] using hRhsTypes.2.2.2.2.2)
  have hLowEmpty0 := bvConcat_eval_right_empty M hM lowPart wu
    (by simpa [lowPart] using hLowPartTy)
  have hLowEmpty : __smtx_model_eval M
      (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt lowPart) := by
    simpa [bvConcatPullupConcat, bvConcatTerm] using hLowEmpty0
  have hRhsEval : __smtx_model_eval M
      (__eo_to_smt
        (bvConcatPullup3Rhs op xs ws z y u nxm nyu nyum nu num)) =
      __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt z)))
        (__smtx_model_eval_concat
          (op.eval (__smtx_model_eval M (__eo_to_smt midExt))
            (__smtx_model_eval M (__eo_to_smt y)))
          (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
            (__smtx_model_eval M (__eo_to_smt u)))) := by
    change __smtx_model_eval_concat
      (__smtx_model_eval M (__eo_to_smt highPart))
      (__smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt midPart))
        (__smtx_model_eval M
          (__eo_to_smt (bvConcatPullupConcat lowPart (Term.Binary 0 0))))) = _
    rw [hHighPartEval, hMidPartEval, hLowEmpty, hLowPartEval]
  have hSplitOuter := op.splitValue (wz + wy + wu) (wy + wu) pa pf
    hAgg0 hAgg1 hFull0 hFull1 (by omega) (by omega)
  have hSplitInner := op.splitSliceValue (wz + wy + wu) pa pf
    hAgg0 hFull0 (wy + wu - 1) wu (by omega) (by omega)
  calc
    _ = op.eval (__smtx_model_eval M (__eo_to_smt agg))
        (__smtx_model_eval M (__eo_to_smt full)) := by
      have hsimpa := hLhsEval
      try simp [bvConcatPullup3Lhs, agg, full] at hsimpa ⊢
      exact hsimpa
    _ = op.eval (SmtValue.Binary ↑(wz + wy + wu) pa)
        (SmtValue.Binary ↑(wz + wy + wu) pf) := by
      rw [hAggEval, hFullEval]
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hSplitOuter
    _ = __smtx_model_eval_concat
        (op.eval
          (__smtx_model_eval_extract
            (SmtValue.Numeral ↑(wz + wy + wu - 1))
            (SmtValue.Numeral ↑(wy + wu))
            (SmtValue.Binary ↑(wz + wy + wu) pa))
          (__smtx_model_eval_extract
            (SmtValue.Numeral ↑(wz + wy + wu - 1))
            (SmtValue.Numeral ↑(wy + wu))
            (SmtValue.Binary ↑(wz + wy + wu) pf)))
        (__smtx_model_eval_concat
          (op.eval
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(wy + wu - 1))
              (SmtValue.Numeral ↑wu)
              (SmtValue.Binary ↑(wz + wy + wu) pa))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(wy + wu - 1))
              (SmtValue.Numeral ↑wu)
              (SmtValue.Binary ↑(wz + wy + wu) pf)))
          (op.eval
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(wu - 1))
              (SmtValue.Numeral 0)
              (SmtValue.Binary ↑(wz + wy + wu) pa))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(wu - 1))
              (SmtValue.Numeral 0)
              (SmtValue.Binary ↑(wz + wy + wu) pf)))) := by
      rw [hSplitInner]
    _ = __smtx_model_eval_concat
        (op.eval (__smtx_model_eval M (__eo_to_smt highExt))
          (__smtx_model_eval M (__eo_to_smt z)))
        (__smtx_model_eval_concat
          (op.eval (__smtx_model_eval M (__eo_to_smt midExt))
            (__smtx_model_eval M (__eo_to_smt y)))
          (op.eval (__smtx_model_eval M (__eo_to_smt lowExt))
            (__smtx_model_eval M (__eo_to_smt u)))) := by
      rw [hHighExtEval, hFullHigh, hZEval, hMidExtEval, hFullMid, hYEval,
        hLowExtEval, hFullLow, hUEval]
      simp [native_nat_to_int, Smtm.native_nat_to_int]
    _ = _ := hRhsEval.symm

theorem facts_bvConcatPullup3Term
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_bool_type (bvConcatPullup3Prem1 nxm u y z) ->
    __eo_typeof (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool ->
    eo_interprets M (bvConcatPullup3Prem1 nxm u y z) true ->
    eo_interprets M (bvConcatPullup3Prem2 nyu y u) true ->
    eo_interprets M (bvConcatPullup3Prem3 nyum y u) true ->
    eo_interprets M (bvConcatPullup3Prem4 nu u) true ->
    eo_interprets M (bvConcatPullup3Prem5 num u) true ->
    eo_interprets M
      (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) true := by
  intro hXsTrans hWsTrans hP1Bool hBodyTy hP1 hP2 hP3 hP4 hP5
  rcases bvConcatPullup3Prem1Type nxm u y z hP1Bool with
    ⟨wz, wy, wu, hZTy, hYTy, hUTy⟩
  have hFullTy0 := bvConcatPullup3FullType z y u wz wy wu hZTy hYTy hUTy
  have hFullTy : __smtx_typeof (__eo_to_smt (bvConcatPullup3Full z y u)) =
      SmtType.BitVec (wz + wy + wu) := by
    simpa [Nat.add_assoc] using hFullTy0
  have hBase := bvConcatPullup3BaseContextFromFull op
    xs ws y z u nxm nyu nyum nu num (wz + wy + wu)
    hXsTrans hWsTrans hFullTy hBodyTy
  have hAggTrans : RuleProofs.eo_has_smt_translation
      (bvConcatPullupAggregate op xs ws) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBase.2.2.2.2]
    intro h
    cases h
  have hIndices := bvConcatPullup3Indices M op
    xs ws y z u nxm nyu nyum nu num wz wy wu hAggTrans
    hBase.2.2.2.2 hZTy hYTy hUTy hBodyTy hP1 hP2 hP3 hP4 hP5
  have hEval := eval_bvConcatPullup3 M hM op
    xs ws y z u nxm nyu nyum nu num wz wy wu
    hBase.1 hBase.2.1 hBase.2.2.1 hBase.2.2.2.1 hBase.2.2.2.2
    hZTy hYTy hUTy hIndices.1 hIndices.2.1 hIndices.2.2.1
    hIndices.2.2.2.1 hIndices.2.2.2.2.1
    hIndices.2.2.2.2.2.1 hIndices.2.2.2.2.2.2.1
    hIndices.2.2.2.2.2.2.2 hBodyTy
  have hEqBool := typed_bvConcatPullup3Term op
    xs ws y z u nxm nyu nyum nu num hXsTrans hWsTrans hP1Bool hBodyTy
  unfold bvConcatPullup3Term at hEqBool ⊢
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [hEval]
    exact RuleProofs.smt_value_rel_refl _

theorem bvConcatPullup3ProgramProperties
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5 : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation ws ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation u ->
    RuleProofs.eo_has_smt_translation nxm ->
    RuleProofs.eo_has_smt_translation nyu ->
    RuleProofs.eo_has_smt_translation nyum ->
    RuleProofs.eo_has_smt_translation nu ->
    RuleProofs.eo_has_smt_translation num ->
    RuleProofs.eo_has_bool_type P1 ->
    RuleProofs.eo_has_bool_type P2 ->
    RuleProofs.eo_has_bool_type P3 ->
    RuleProofs.eo_has_bool_type P4 ->
    RuleProofs.eo_has_bool_type P5 ->
    __eo_typeof
        (bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
          P1 P2 P3 P4 P5) = Term.Bool ->
    StepRuleProperties M [P1, P2, P3, P4, P5]
      (bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
        P1 P2 P3 P4 P5) := by
  intro hXsT hWsT hYT hZT hUT hNxmT hNyuT hNyumT hNuT hNumT
    hP1Bool hP2Bool hP3Bool hP4Bool hP5Bool hResultTy
  have hProg : bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
      P1 P2 P3 P4 P5 ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  have hNorm := bvConcatPullup3Program_normalize op
    xs ws y z u nxm nyu nyum nu num P1 P2 P3 P4 P5
    hXsT hWsT hYT hZT hUT hNxmT hNyuT hNyumT hNuT hNumT hProg
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsT
  have hWs := RuleProofs.term_ne_stuck_of_has_smt_translation ws hWsT
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYT
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZT
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUT
  have hNxm := RuleProofs.term_ne_stuck_of_has_smt_translation nxm hNxmT
  have hNyu := RuleProofs.term_ne_stuck_of_has_smt_translation nyu hNyuT
  have hNyum := RuleProofs.term_ne_stuck_of_has_smt_translation nyum hNyumT
  have hNu := RuleProofs.term_ne_stuck_of_has_smt_translation nu hNuT
  have hNum := RuleProofs.term_ne_stuck_of_has_smt_translation num hNumT
  have hProgramRaw :
      bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
          P1 P2 P3 P4 P5 =
        bvConcatPullup3BodyRaw op xs ws y z u nxm nyu nyum nu num := by
    rw [hNorm.1, hNorm.2.1, hNorm.2.2.1, hNorm.2.2.2.1,
      hNorm.2.2.2.2]
    exact bvConcatPullup3Program_eq_raw op
      xs ws y z u nxm nyu nyum nu num
      hXs hWs hY hZ hU hNxm hNyu hNyum hNu hNum
  have hRawNe : bvConcatPullup3BodyRaw op
      xs ws y z u nxm nyu nyum nu num ≠ Term.Stuck := by
    rw [← hProgramRaw]
    exact hProg
  have hProgramTerm :
      bvConcatPullup3Program op xs ws y z u nxm nyu nyum nu num
          P1 P2 P3 P4 P5 =
        bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num :=
    hProgramRaw.trans (bvConcatPullup3BodyRaw_eq_term op
      xs ws y z u nxm nyu nyum nu num hRawNe)
  have hBodyTy : __eo_typeof
      (bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num) =
      Term.Bool := by rw [← hProgramTerm]; exact hResultTy
  have hPrem1Bool : RuleProofs.eo_has_bool_type
      (bvConcatPullup3Prem1 nxm u y z) := by
    rw [← hNorm.1]
    exact hP1Bool
  refine ⟨?_, ?_⟩
  · intro hPremEvidence
    have hP1True : eo_interprets M
        (bvConcatPullup3Prem1 nxm u y z) true := by
      rw [← hNorm.1]
      exact hPremEvidence P1 (by simp)
    have hP2True : eo_interprets M
        (bvConcatPullup3Prem2 nyu y u) true := by
      rw [← hNorm.2.1]
      exact hPremEvidence P2 (by simp)
    have hP3True : eo_interprets M
        (bvConcatPullup3Prem3 nyum y u) true := by
      rw [← hNorm.2.2.1]
      exact hPremEvidence P3 (by simp)
    have hP4True : eo_interprets M
        (bvConcatPullup3Prem4 nu u) true := by
      rw [← hNorm.2.2.2.1]
      exact hPremEvidence P4 (by simp)
    have hP5True : eo_interprets M
        (bvConcatPullup3Prem5 num u) true := by
      rw [← hNorm.2.2.2.2]
      exact hPremEvidence P5 (by simp)
    rw [hProgramTerm]
    exact facts_bvConcatPullup3Term M hM op
      xs ws y z u nxm nyu nyum nu num hXsT hWsT hPrem1Bool hBodyTy
      hP1True hP2True hP3True hP4True hP5True
  · rw [hProgramTerm]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_bvConcatPullup3Term op xs ws y z u nxm nyu nyum nu num
        hXsT hWsT hPrem1Bool hBodyTy)

def BvConcatPullupOp.pullup3Rule : BvConcatPullupOp → CRule
  | .band => CRule.bv_and_concat_pullup3
  | .bor => CRule.bv_or_concat_pullup3
  | .bxor => CRule.bv_xor_concat_pullup3

theorem cmd_step_bvConcatPullup3_properties
    (M : SmtModel) (hM : model_wf M)
    (op : BvConcatPullupOp)
    (s : CState) (args : CArgList) (premises : CIndexList) :
    cmdTranslationOk (CCmd.step op.pullup3Rule args premises) ->
    AllHaveBoolType (premiseTermList s premises) ->
    __eo_typeof
        (__eo_cmd_step_proven s op.pullup3Rule args premises) = Term.Bool ->
    StepRuleProperties M (premiseTermList s premises)
      (__eo_cmd_step_proven s op.pullup3Rule args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s op.pullup3Rule args premises ≠
      Term.Stuck := term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact False.elim (hProg (by cases op <;> rfl))
  | cons xs args =>
    cases args with
    | nil => exact False.elim (hProg (by cases op <;> rfl))
    | cons ws args =>
      cases args with
      | nil => exact False.elim (hProg (by cases op <;> rfl))
      | cons y args =>
        cases args with
        | nil => exact False.elim (hProg (by cases op <;> rfl))
        | cons z args =>
          cases args with
          | nil => exact False.elim (hProg (by cases op <;> rfl))
          | cons u args =>
            cases args with
            | nil => exact False.elim (hProg (by cases op <;> rfl))
            | cons nxm args =>
              cases args with
              | nil => exact False.elim (hProg (by cases op <;> rfl))
              | cons nyu args =>
                cases args with
                | nil => exact False.elim (hProg (by cases op <;> rfl))
                | cons nyum args =>
                  cases args with
                  | nil => exact False.elim (hProg (by cases op <;> rfl))
                  | cons nu args =>
                    cases args with
                    | nil => exact False.elim (hProg (by cases op <;> rfl))
                    | cons num args =>
                      cases args with
                      | cons _ _ =>
                        exact False.elim (hProg (by cases op <;> rfl))
                      | nil =>
                        cases premises with
                        | nil =>
                          exact False.elim (hProg (by cases op <;> rfl))
                        | cons n1 premises =>
                          cases premises with
                          | nil =>
                            exact False.elim (hProg (by cases op <;> rfl))
                          | cons n2 premises =>
                            cases premises with
                            | nil =>
                              exact False.elim (hProg (by cases op <;> rfl))
                            | cons n3 premises =>
                              cases premises with
                              | nil =>
                                exact False.elim (hProg (by cases op <;> rfl))
                              | cons n4 premises =>
                                cases premises with
                                | nil =>
                                  exact False.elim
                                    (hProg (by cases op <;> rfl))
                                | cons n5 premises =>
                                  cases premises with
                                  | cons _ _ =>
                                    exact False.elim
                                      (hProg (by cases op <;> rfl))
                                  | nil =>
                                    let P1 := __eo_state_proven_nth s n1
                                    let P2 := __eo_state_proven_nth s n2
                                    let P3 := __eo_state_proven_nth s n3
                                    let P4 := __eo_state_proven_nth s n4
                                    let P5 := __eo_state_proven_nth s n5
                                    have hCommandEq :
                                        __eo_cmd_step_proven s op.pullup3Rule
                                          (CArgList.cons xs (CArgList.cons ws
                                            (CArgList.cons y (CArgList.cons z
                                              (CArgList.cons u
                                                (CArgList.cons nxm
                                                  (CArgList.cons nyu
                                                    (CArgList.cons nyum
                                                      (CArgList.cons nu
                                                        (CArgList.cons num
                                                          CArgList.nil))))))))))
                                          (CIndexList.cons n1
                                            (CIndexList.cons n2
                                              (CIndexList.cons n3
                                                (CIndexList.cons n4
                                                  (CIndexList.cons n5
                                                    CIndexList.nil))))) =
                                          bvConcatPullup3Program op xs ws y z u
                                            nxm nyu nyum nu num P1 P2 P3 P4 P5 := by
                                      cases op <;> rfl
                                    rw [hCommandEq]
                                    have hArgsTrans :
                                        RuleProofs.eo_has_smt_translation xs ∧
                                        RuleProofs.eo_has_smt_translation ws ∧
                                        RuleProofs.eo_has_smt_translation y ∧
                                        RuleProofs.eo_has_smt_translation z ∧
                                        RuleProofs.eo_has_smt_translation u ∧
                                        RuleProofs.eo_has_smt_translation nxm ∧
                                        RuleProofs.eo_has_smt_translation nyu ∧
                                        RuleProofs.eo_has_smt_translation nyum ∧
                                        RuleProofs.eo_has_smt_translation nu ∧
                                        RuleProofs.eo_has_smt_translation num ∧
                                        True := by
                                      cases op <;> simpa
                                        [BvConcatPullupOp.pullup3Rule,
                                          cmdTranslationOk,
                                          cArgListTranslationOk]
                                        using hCmdTrans
                                    have hP1Bool := hPremisesBool P1 (by
                                      simp [premiseTermList, P1, P2, P3, P4, P5])
                                    have hP2Bool := hPremisesBool P2 (by
                                      simp [premiseTermList, P1, P2, P3, P4, P5])
                                    have hP3Bool := hPremisesBool P3 (by
                                      simp [premiseTermList, P1, P2, P3, P4, P5])
                                    have hP4Bool := hPremisesBool P4 (by
                                      simp [premiseTermList, P1, P2, P3, P4, P5])
                                    have hP5Bool := hPremisesBool P5 (by
                                      simp [premiseTermList, P1, P2, P3, P4, P5])
                                    have hResultTyLocal : __eo_typeof
                                        (bvConcatPullup3Program op xs ws y z u
                                          nxm nyu nyum nu num P1 P2 P3 P4 P5) =
                                        Term.Bool := by
                                      rw [← hCommandEq]
                                      exact hResultTy
                                    exact bvConcatPullup3ProgramProperties
                                      M hM op xs ws y z u nxm nyu nyum nu num
                                      P1 P2 P3 P4 P5
                                      hArgsTrans.1 hArgsTrans.2.1
                                      hArgsTrans.2.2.1
                                      hArgsTrans.2.2.2.1
                                      hArgsTrans.2.2.2.2.1
                                      hArgsTrans.2.2.2.2.2.1
                                      hArgsTrans.2.2.2.2.2.2.1
                                      hArgsTrans.2.2.2.2.2.2.2.1
                                      hArgsTrans.2.2.2.2.2.2.2.2.1
                                      hArgsTrans.2.2.2.2.2.2.2.2.2.1
                                      hP1Bool hP2Bool hP3Bool hP4Bool hP5Bool
                                      hResultTyLocal

theorem bvConcatPullup1BaseContext
    (op : BvConcatPullupOp) (xs ws y z ys nxm ny nym : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation
      (bvConcatPullup1Term op xs ws y z ys nxm ny nym) ->
    __eo_typeof (bvConcatPullup1Term op xs ws y z ys nxm ny nym) =
      Term.Bool ->
    ∃ w : Nat,
      __eo_is_list op.term xs = Term.Boolean true ∧
      __eo_is_list op.term ws = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat) ys = Term.Boolean true ∧
      PullupListTypeOrNil xs w ∧
      __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullup1ConcatZYs z y ys)) =
        SmtType.BitVec w ∧
      __smtx_typeof
          (__eo_to_smt (bvConcatPullupAggregate op xs ws)) =
        SmtType.BitVec w := by
  intro hXsTrans hBodyTrans hTermTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (bvConcatPullup1Lhs op xs ws y z ys))
    (__eo_typeof (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))
    (by have hsimpa := hTermTy; (try simp [bvConcatPullup1Term] at hsimpa ⊢); exact hsimpa)
  have hLhsNe : bvConcatPullup1Lhs op xs ws y z ys ≠ Term.Stuck := by
    intro h
    rw [h] at hSides
    exact hSides.1 rfl
  let full := bvConcatPullup1ConcatZYs z y ys
  let tail := op.apply full ws
  have hLists := pullup_list_concat_parts_of_ne_stuck op.term xs tail (by
    simpa [bvConcatPullup1Lhs, full, tail] using hLhsNe)
  have hXsList := hLists.1
  have hTailList := hLists.2
  have hWsList : __eo_is_list op.term ws = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op.term full ws hTailList
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof
            (__eo_to_smt (bvConcatPullup1Lhs op xs ws y z ys)))
          (__smtx_typeof
            (__eo_to_smt (bvConcatPullup1Rhs op xs ws y z ys nxm ny nym))) ≠
        SmtType.None := by
    have hsimpa := hBodyTrans
    try simp [RuleProofs.eo_has_smt_translation, bvConcatPullup1Term] at hsimpa ⊢
    exact hsimpa
  have hEqArgs := TranslationProofs.smtx_typeof_eq_non_none hEqNN
  have hLhsSmtNN :
      __smtx_typeof (__eo_to_smt (bvConcatPullup1Lhs op xs ws y z ys)) ≠
        SmtType.None := by
    exact hEqArgs.2
  have hRecNN :
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs tail)) ≠
        SmtType.None := by
    rw [← pullup_list_concat_eq_rec op.term xs tail hXsList hTailList]
    simpa [bvConcatPullup1Lhs, full, tail] using hLhsSmtNN
  have hTailNN := pullup_list_concat_rec_right_smt_non_none op xs tail
    hXsList hRecNN
  have hTailArgs : ∃ w,
      __smtx_typeof (__eo_to_smt full) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt ws) = SmtType.BitVec w := by
    cases op with
    | band =>
        exact bv_binop_args_of_non_none (op := SmtTerm.bvand)
          (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt full)
                (__eo_to_smt ws)) =
              __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt full))
                (__smtx_typeof (__eo_to_smt ws)) by
            rw [__smtx_typeof.eq_def] <;> simp only) hTailNN
    | bor =>
        exact bv_binop_args_of_non_none (op := SmtTerm.bvor)
          (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt full)
                (__eo_to_smt ws)) =
              __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt full))
                (__smtx_typeof (__eo_to_smt ws)) by
            rw [__smtx_typeof.eq_def] <;> simp only) hTailNN
    | bxor =>
        exact bv_binop_args_of_non_none (op := SmtTerm.bvxor)
          (show __smtx_typeof (SmtTerm.bvxor (__eo_to_smt full)
                (__eo_to_smt ws)) =
              __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt full))
                (__smtx_typeof (__eo_to_smt ws)) by
            rw [__smtx_typeof.eq_44]) hTailNN
  rcases hTailArgs with ⟨w, hFullTy, hWsTy⟩
  have hRecTy := pullup_list_concat_rec_result_smt_type op xs tail w
    hXsList (op.binarySmtType full ws w hFullTy hWsTy) hRecNN
  have hXsType := pullup_list_type_or_nil_of_concat_type op xs tail w
    hXsTrans hXsList (op.binarySmtType full ws w hFullTy hWsTy) hRecTy
  have hFullNe := pullup_term_ne_stuck_of_smt_bitvec_type hFullTy
  have hConcatLists := bvConcat_list_concat_lists_of_ne_stuck ys
    (bvConcatPullupConcat z (bvConcatPullupConcat y (Term.Binary 0 0))) (by
      simpa [full, bvConcatPullup1ConcatZYs] using hFullNe)
  have hYsList := hConcatLists.1
  let c := __eo_list_concat op.term xs ws
  have hCList : __eo_is_list op.term c = Term.Boolean true := by
    dsimp [c]
    rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
    exact eo_list_concat_rec_is_list_true_of_lists op.term xs ws
      hXsList hWsList
  have hCTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
    rcases hXsType with hXsTy | hXsNil
    · dsimp [c]
      rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList]
      exact op.listConcatRecSmtType xs ws w hXsList hWsList hXsTy hWsTy
    · have hCeq : c = ws := by
        dsimp [c]
        rw [pullup_list_concat_eq_rec op.term xs ws hXsList hWsList,
          hXsNil ws]
      rw [hCeq]
      exact hWsTy
  have hAggTy := op.listSingletonElimSmtType c w hCList hCTy
  exact ⟨w, hXsList, hWsList, hYsList, hXsType, hWsTy,
    by simpa [full] using hFullTy,
    by simpa [bvConcatPullupAggregate, c] using hAggTy⟩
end
