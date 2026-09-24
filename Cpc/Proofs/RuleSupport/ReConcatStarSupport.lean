module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport
public import Cpc.Proofs.RuleSupport.ReLoopElimSupport
import all Cpc.Proofs.RuleSupport.ReLoopElimSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-! ## Arithmetic helpers (stated over `Int`/`Nat` so `omega` sees the atoms) -/

private theorem one_le_toNat_of_one_le {z : Int} (h : 1 ≤ z) :
    1 ≤ Int.toNat z := by omega

private theorem one_le_toNat_lo {lo hi : Int}
    (hhi : 1 ≤ hi) (hlohi : lo ≤ hi)
    (hzero : Int.toNat (hi + -lo) = 0) : 1 ≤ Int.toNat lo := by omega

/-! ## Bridging `native_str_in_re` and `nativeListInRe` -/

theorem native_str_in_re_eq_nativeListInRe
    (s : native_String) (r : SmtRegLan)
    (hValid : native_string_valid s = true) :
    native_str_in_re s r = nativeListInRe s r := by
  simp [native_str_in_re, hValid]

/-! ## Membership facts for epsilon and star -/

theorem nativeListInRe_epsilon_iff (xs : List native_Char) :
    nativeListInRe xs SmtRegLan.epsilon = true ↔ xs = [] := by
  cases xs with
  | nil => simp [nativeListInRe, native_re_nullable]
  | cons c cs =>
      have hFalse : nativeListInRe (c :: cs) SmtRegLan.epsilon = false := by
        simpa [nativeListInRe, native_re_deriv] using nativeListInRe_empty cs
      simp [hFalse]

theorem native_re_nullable_mk_star (r : SmtRegLan) :
    native_re_nullable (native_re_mk_star r) = true := by
  cases r <;> simp [native_re_mk_star, native_re_mult, native_re_nullable]

theorem nativeListInRe_nil_mk_star (r : SmtRegLan) :
    nativeListInRe [] (native_re_mk_star r) = true := by
  simp [nativeListInRe, native_re_nullable_mk_star]

/-- Append-closure of the language of a raw `star`. -/
theorem nativeListInRe_raw_star_append :
    (xs ys : List native_Char) -> (r : SmtRegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, r, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, r, hLeft, hRight => by
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hLeft
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
        ⟨xs1, xs2, hAppend, hChunk, hTail⟩
      have hLen : xs2.length < (c :: cs).length := by
        have hLenEq := congrArg List.length hAppend
        simp at hLenEq ⊢
        omega
      have hTailAppend :
          nativeListInRe (xs2 ++ ys) (SmtRegLan.star r) = true :=
        nativeListInRe_raw_star_append xs2 ys r hTail hRight
      have hAppend' : xs1 ++ (xs2 ++ ys) = cs ++ ys := by
        rw [← List.append_assoc, hAppend]
      have hConcat' :
          nativeListInRe (cs ++ ys)
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨xs1, xs2 ++ ys, hAppend', hChunk, hTailAppend⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    omega

/-- `native_re_mk_star r` is either `epsilon` or a raw `star`. -/
theorem mk_star_eq_epsilon_or_star (r : SmtRegLan) :
    native_re_mk_star r = SmtRegLan.epsilon ∨
      ∃ r', native_re_mk_star r = SmtRegLan.star r' := by
  cases r <;> simp [native_re_mk_star, native_re_mult]

/-- Append-closure of the language of `mk_star`. -/
theorem nativeListInRe_mk_star_append
    (xs ys : List native_Char) (r : SmtRegLan)
    (hxs : nativeListInRe xs (native_re_mk_star r) = true)
    (hys : nativeListInRe ys (native_re_mk_star r) = true) :
    nativeListInRe (xs ++ ys) (native_re_mk_star r) = true := by
  rcases mk_star_eq_epsilon_or_star r with hEps | ⟨r', hStar⟩
  · rw [hEps] at hxs hys ⊢
    have hxNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 hxs
    have hyNil : ys = [] := (nativeListInRe_epsilon_iff ys).1 hys
    subst hxNil; subst hyNil
    simpa using (nativeListInRe_epsilon_iff ([] : List native_Char)).2 rfl
  · rw [hStar] at hxs hys ⊢
    exact nativeListInRe_raw_star_append xs ys r' hxs hys

/-! ## `nativeReExpRec` over a star base -/

/-- The exponentiation of a nullable language is nullable. -/
theorem nativeReExpRec_nullable
    (k : native_Nat) (r : SmtRegLan)
    (hr : native_re_nullable r = true) :
    native_re_nullable (nativeReExpRec k r) = true := by
  induction k with
  | zero => simp [nativeReExpRec, native_re_nullable]
  | succ k ih =>
      rw [nativeReExpRec]
      rw [native_re_nullable_mk_concat, ih, hr]
      rfl

/-- Any power of `mk_star r` is contained in `mk_star r`. -/
theorem nativeReExpRec_mk_star_subset
    (k : native_Nat) (r : SmtRegLan) (xs : List native_Char)
    (h : nativeListInRe xs (nativeReExpRec k (native_re_mk_star r)) = true) :
    nativeListInRe xs (native_re_mk_star r) = true := by
  induction k generalizing xs with
  | zero =>
      have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 (by
        simpa [nativeReExpRec] using h)
      subst hNil
      exact nativeListInRe_nil_mk_star r
  | succ k ih =>
      have hConcat :
          nativeListInRe xs
            (native_re_mk_concat (nativeReExpRec k (native_re_mk_star r))
              (native_re_mk_star r)) = true := by
        exact h
      rcases
        (nativeListInRe_mk_concat_true_iff_exists_append xs
          (nativeReExpRec k (native_re_mk_star r))
          (native_re_mk_star r)).1 hConcat with
        ⟨xs1, xs2, hAppend, hLeft, hRight⟩
      have hLeft' : nativeListInRe xs1 (native_re_mk_star r) = true :=
        ih xs1 hLeft
      rw [← hAppend]
      exact nativeListInRe_mk_star_append xs1 xs2 r hLeft' hRight

/-- Positive powers of `mk_star r` contain all of `mk_star r`. -/
theorem nativeReExpRec_mk_star_pos
    (k : native_Nat) (r : SmtRegLan) (xs : List native_Char)
    (hk : 1 ≤ k)
    (h : nativeListInRe xs (native_re_mk_star r) = true) :
    nativeListInRe xs (nativeReExpRec k (native_re_mk_star r)) = true := by
  cases k with
  | zero => exact absurd hk (by decide)
  | succ k' =>
  have hNilLeft :
      nativeListInRe [] (nativeReExpRec k' (native_re_mk_star r)) = true := by
    simp [nativeListInRe,
      nativeReExpRec_nullable k' _ (native_re_nullable_mk_star r)]
  have hConcat :
      nativeListInRe xs
        (native_re_mk_concat (nativeReExpRec k' (native_re_mk_star r))
          (native_re_mk_star r)) = true :=
    (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeReExpRec k' (native_re_mk_star r))
      (native_re_mk_star r)).2
      ⟨[], xs, by simp, hNilLeft, h⟩
  exact hConcat

/-! ## `nativeReLoopRec` over a star base -/

/-- Every clause of the loop unrolling is contained in `mk_star r`. -/
theorem nativeReLoopRec_mk_star_subset
    (k : native_Nat) (lo hi : native_Int) (r : SmtRegLan)
    (xs : List native_Char)
    (h : nativeListInRe xs
        (nativeReLoopRec k lo hi (native_re_mk_star r)) = true) :
    nativeListInRe xs (native_re_mk_star r) = true := by
  induction k generalizing hi with
  | zero =>
      exact nativeReExpRec_mk_star_subset (native_int_to_nat lo) r xs
        (by simpa [nativeReLoopRec] using h)
  | succ k ih =>
      have hUnion :
          nativeListInRe xs
            (native_re_mk_union
              (nativeReLoopRec k lo (native_zplus hi (native_zneg 1))
                (native_re_mk_star r))
              (nativeReExpRec (native_int_to_nat hi)
                (native_re_mk_star r))) = true := by
        exact h
      rw [nativeListInRe_mk_union] at hUnion
      simp only [Bool.or_eq_true] at hUnion
      rcases hUnion with hL | hR
      · exact ih (native_zplus hi (native_zneg 1)) hL
      · exact nativeReExpRec_mk_star_subset (native_int_to_nat hi) r xs hR

/-- Extensional equality of the loop unrolling and `mk_star r` for `hi ≥ 1`. -/
theorem nativeReLoopRec_mk_star_ext
    (lo hi : native_Int) (r : SmtRegLan) (xs : List native_Char)
    (hhi : 1 ≤ hi) (hlohi : lo ≤ hi) :
    nativeListInRe xs
        (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
          lo hi (native_re_mk_star r)) =
      nativeListInRe xs (native_re_mk_star r) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact nativeReLoopRec_mk_star_subset _ lo hi r xs h
  · intro h
    have hHiNat : 1 ≤ native_int_to_nat hi :=
      one_le_toNat_of_one_le hhi
    cases hk : native_int_to_nat (native_zplus hi (native_zneg lo)) with
    | zero =>
        -- `k = 0` forces `hi = lo`, hence `int_to_nat lo = int_to_nat hi ≥ 1`
        have hk' : Int.toNat (hi + -lo) = 0 := by
          simpa [native_int_to_nat, native_zplus, native_zneg] using hk
        have hLoNat : 1 ≤ native_int_to_nat lo :=
          one_le_toNat_lo hhi hlohi hk'
        simp only [nativeReLoopRec]
        exact nativeReExpRec_mk_star_pos (native_int_to_nat lo) r xs hLoNat h
    | succ k =>
        have hMem :
            nativeListInRe xs
              (nativeReExpRec (native_int_to_nat hi)
                (native_re_mk_star r)) = true :=
          nativeReExpRec_mk_star_pos (native_int_to_nat hi) r xs hHiNat h
        rw [nativeReLoopRec, nativeListInRe_mk_union]
        simp only [Bool.or_eq_true]
        exact Or.inr hMem

/-! ## Nullable absorption: `Σ* · r₁ · t = Σ* · t` for nullable `r₁`

`Σ* = re.* re.allchar = native_re_all` accepts every *valid* string, and the
`smt_value_rel` on `RegLan` only quantifies over valid strings, so the absorption
holds at the `native_str_in_re` level even though it can fail at the raw
`nativeListInRe` level (a `comp`-style `r₁` can match invalid characters). -/

theorem native_str_in_re_all_concat_nullable_absorb
    (r1 t : SmtRegLan) (hNull : native_re_nullable r1 = true)
    (s : native_String) (hValid : native_string_valid s = true) :
    native_str_in_re s
        (native_re_mk_concat native_re_all (native_re_mk_concat r1 t)) =
      native_str_in_re s (native_re_mk_concat native_re_all t) := by
  rw [native_str_in_re_eq_nativeListInRe s _ hValid,
    native_str_in_re_eq_nativeListInRe s _ hValid]
  have hsValid : s.all native_char_valid = true := by
    simpa [native_string_valid] using hValid
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append s native_re_all
        (native_re_mk_concat r1 t)).1 h with ⟨u, w, hUW, hU, hW⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append w r1 t).1 hW with
      ⟨v, z, hVZ, hV, hZ⟩
    have hsplit : u ++ (v ++ z) = s := by rw [hVZ, hUW]
    have huvValid : (u ++ v).all native_char_valid = true := by
      have := hsValid
      rw [← hsplit, List.all_append, List.all_append] at this
      rw [List.all_append]
      simp only [Bool.and_eq_true] at this ⊢
      exact ⟨this.1, this.2.1⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append s native_re_all t).2
    refine ⟨u ++ v, z, ?_, ?_, hZ⟩
    · rw [List.append_assoc, hVZ, hUW]
    · exact (nativeListInRe_re_all_true_iff (u ++ v)).2 huvValid
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append s native_re_all t).1 h with
      ⟨u, z, hUZ, hU, hZ⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append s native_re_all
      (native_re_mk_concat r1 t)).2
    refine ⟨u, z, hUZ, hU, ?_⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append z r1 t).2
    refine ⟨[], z, by simp, ?_, hZ⟩
    simpa [nativeListInRe] using hNull

/-- Left variant: `r₁ · (Σ* · t) = Σ* · t` for nullable `r₁` (over valid strings). -/
theorem native_str_in_re_nullable_concat_all_absorb
    (r1 t : SmtRegLan) (hNull : native_re_nullable r1 = true)
    (s : native_String) (hValid : native_string_valid s = true) :
    native_str_in_re s
        (native_re_mk_concat r1 (native_re_mk_concat native_re_all t)) =
      native_str_in_re s (native_re_mk_concat native_re_all t) := by
  rw [native_str_in_re_eq_nativeListInRe s _ hValid,
    native_str_in_re_eq_nativeListInRe s _ hValid]
  have hsValid : s.all native_char_valid = true := by
    simpa [native_string_valid] using hValid
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append s r1
        (native_re_mk_concat native_re_all t)).1 h with ⟨v, w, hVW, hV, hW⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append w native_re_all t).1 hW with
      ⟨a, b, hAB, hA, hB⟩
    have hsplit : v ++ (a ++ b) = s := by rw [hAB, hVW]
    have hvaValid : (v ++ a).all native_char_valid = true := by
      have := hsValid
      rw [← hsplit, List.all_append, List.all_append] at this
      rw [List.all_append]
      simp only [Bool.and_eq_true] at this ⊢
      exact ⟨this.1, this.2.1⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append s native_re_all t).2
    refine ⟨v ++ a, b, ?_, ?_, hB⟩
    · rw [List.append_assoc, hAB, hVW]
    · exact (nativeListInRe_re_all_true_iff (v ++ a)).2 hvaValid
  · intro h
    apply (nativeListInRe_mk_concat_true_iff_exists_append s r1
      (native_re_mk_concat native_re_all t)).2
    refine ⟨[], s, by simp, ?_, h⟩
    simpa [nativeListInRe] using hNull

/-! ## Bridge to `smt_value_rel` -/

/-- Build a `RegLan` semantic equality from extensional membership equality. -/
theorem smt_value_rel_reglan_of_valid_eq {r s : SmtRegLan}
    (h : ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str r = native_str_in_re str s) :
    RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s) := by
  have hModel : ∀ str : native_String,
      native_string_valid str = true →
        Smtm.native_str_in_re (impl_native_string_to_values str) r =
          Smtm.native_str_in_re (impl_native_string_to_values str) s := by
    intro str hValid
    rw [← native_str_in_re_eq_model, ← native_str_in_re_eq_model]
    exact h str hValid
  change __smtx_model_eval_eq (SmtValue.RegLan r) (SmtValue.RegLan s) =
    SmtValue.Boolean true
  simpa [__smtx_model_eval_eq] using hModel

/-- Final extensional equality of `re.loop n m (r*)` and `r*`, packaged for the rule. -/
theorem re_loop_star_smt_value_rel
    (lo hi : native_Int) (rv : SmtRegLan)
    (hhi : 1 ≤ hi) (hlohi : lo ≤ hi) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
          lo hi (native_re_mult rv)))
      (SmtValue.RegLan (native_re_mult rv)) := by
  apply smt_value_rel_reglan_of_valid_eq
  intro str hValid
  rw [native_str_in_re_eq_nativeListInRe str _ hValid,
    native_str_in_re_eq_nativeListInRe str _ hValid]
  exact nativeReLoopRec_mk_star_ext lo hi rv str hhi hlohi

end RuleProofs
