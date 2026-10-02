module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.eo_eval_str_from_int_rhs (n : Term) : Term :=
  let _v0 := __run_evaluate n
  let _v1 := __eo_add (__eo_log (Term.Numeral 10) _v0) (Term.Numeral 1)
  __eo_ite (__eo_is_z _v0)
    (__eo_ite (__eo_is_neg _v0) (Term.String [])
      (__str_from_int_eval_rec
        (__eo_requires (__eo_is_neg _v1) (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) _v1)
            (Term.Numeral 0)))
        _v0 (Term.String [])))
    (__eo_mk_apply (Term.UOp UserOp.str_from_int) _v0)

def EvaluateProofInternal.eo_iota_int_list : native_Nat -> native_Int -> Term
  | 0, _ => Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
      (Term.UOp UserOp.Int)
  | fuel + 1, i =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral i))
        (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1))

def EvaluateProofInternal.eo_zero_int_list : native_Nat -> Term
  | 0 => Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
      (Term.UOp UserOp.Int)
  | fuel + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (EvaluateProofInternal.eo_zero_int_list fuel)

theorem EvaluateProofInternal.eo_zero_int_list_ne_stuck :
    ∀ fuel : native_Nat, EvaluateProofInternal.eo_zero_int_list fuel ≠ Term.Stuck
  | 0 => by
      intro h
      cases h
  | fuel + 1 => by
      intro h
      cases h

theorem EvaluateProofInternal.eo_iota_int_list_ne_stuck :
    ∀ (fuel : native_Nat) (i : native_Int),
      EvaluateProofInternal.eo_iota_int_list fuel i ≠ Term.Stuck
  | 0, _ => by
      intro h
      cases h
  | fuel + 1, _ => by
      intro h
      cases h

theorem EvaluateProofInternal.eo_list_repeat_rec_int_zero :
    ∀ fuel : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) fuel =
        EvaluateProofInternal.eo_zero_int_list fuel
  | 0 => by
      rfl
  | fuel + 1 => by
      rw [show
        __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (fuel + 1) =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (__eo_list_repeat_rec
              (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) fuel) by
        rfl]
      rw [EvaluateProofInternal.eo_list_repeat_rec_int_zero fuel]
      rw [show EvaluateProofInternal.eo_zero_int_list (fuel + 1) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (EvaluateProofInternal.eo_zero_int_list fuel) by
        rfl]
      have hNe := EvaluateProofInternal.eo_zero_int_list_ne_stuck fuel
      cases hList : EvaluateProofInternal.eo_zero_int_list fuel <;>
        simp [__eo_mk_apply, hList] at hNe ⊢

theorem EvaluateProofInternal.eo_iota_zero_int_list :
    ∀ (fuel : native_Nat) (i : native_Int),
      __iota_rec (EvaluateProofInternal.eo_zero_int_list fuel) (Term.Numeral i) =
        EvaluateProofInternal.eo_iota_int_list fuel i
  | 0, _ => by
      rfl
  | fuel + 1, i => by
      rw [show
        __iota_rec (EvaluateProofInternal.eo_zero_int_list (fuel + 1)) (Term.Numeral i) =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral i))
            (__iota_rec (EvaluateProofInternal.eo_zero_int_list fuel)
              (__eo_add (Term.Numeral i) (Term.Numeral 1))) by
        rfl]
      simp [__eo_add, native_zplus]
      rw [EvaluateProofInternal.eo_iota_zero_int_list fuel (i + 1)]
      rw [show EvaluateProofInternal.eo_iota_int_list (fuel + 1) i =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral i))
            (EvaluateProofInternal.eo_iota_int_list fuel (i + 1)) by
        rfl]
      have hNe := EvaluateProofInternal.eo_iota_int_list_ne_stuck fuel (i + 1)
      cases hList : EvaluateProofInternal.eo_iota_int_list fuel (i + 1) <;>
        simp [__eo_mk_apply, hList] at hNe ⊢

theorem EvaluateProofInternal.eo_iota_list_repeat_int_of_nonneg
    {k i : native_Int}
    (hNonneg : ¬ k < 0) :
    __iota_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) (Term.Numeral k))
        (Term.Numeral i) =
      EvaluateProofInternal.eo_iota_int_list (native_int_to_nat k) i := by
  have hNegBool : native_zlt k 0 = false := by
    rw [show native_zlt k 0 = decide (k < 0) by rfl]
    exact decide_eq_false hNonneg
  simp [__eo_list_repeat, native_ite, hNegBool,
    EvaluateProofInternal.eo_list_repeat_rec_int_zero, EvaluateProofInternal.eo_iota_zero_int_list]

theorem EvaluateProofInternal.native_digitChar_toNat_of_lt10 {d : Nat} (hd : d < 10) :
    Char.toNat (Nat.digitChar d) = 48 + d := by
  unfold Nat.digitChar
  by_cases h0 : d = 0
  · simp [h0]
  · by_cases h1 : d = 1
    · simp [h1]
    · by_cases h2 : d = 2
      · simp [h2]
      · by_cases h3 : d = 3
        · simp [h3]
        · by_cases h4 : d = 4
          · simp [h4]
          · by_cases h5 : d = 5
            · simp [h5]
            · by_cases h6 : d = 6
              · simp [h6]
              · by_cases h7 : d = 7
                · simp [h7]
                · by_cases h8 : d = 8
                  · simp [h8]
                  · by_cases h9 : d = 9
                    · simp [h9]
                    · have hGe : 10 ≤ d := by omega
                      exact False.elim ((Nat.not_lt_of_ge hGe) hd)

theorem EvaluateProofInternal.eo_str_from_int_digit_term_nat (n : Nat) :
    __eo_to_str
        (__eo_add (Term.Numeral 48)
          (__eo_zmod (Term.Numeral (Int.ofNat n)) (Term.Numeral 10))) =
      Term.String [Char.toNat (Nat.digitChar (n % 10))] := by
  let r : Int := (Int.ofNat n) % 10
  have hRNonneg : 0 ≤ r := by
    exact Int.emod_nonneg _ (by decide : (10 : Int) ≠ 0)
  have hRLt : r < 10 := by
    exact Int.emod_lt_of_pos _ (by decide : 0 < (10 : Int))
  have hCodeNonneg : 0 ≤ (48 : Int) + r := by omega
  have hCodeLt : (48 : Int) + r < 196608 := by omega
  have hCodeToNat :
      Int.toNat ((48 : Int) + r) = 48 + n % 10 := by
    rw [Int.toNat_add (by decide : 0 ≤ (48 : Int)) hRNonneg]
    change Int.toNat (48 : Int) + Int.toNat ((Int.ofNat n) % 10) =
      48 + n % 10
    have hModToNat :
        Int.toNat ((Int.ofNat n) % (10 : Int)) = n % 10 := by
      simpa using
        (Int.toNat_emod (x := Int.ofNat n) (y := (10 : Int))
          (Int.zero_le_ofNat n) (by decide : 0 ≤ (10 : Int)))
    rw [hModToNat]
    simp
  have hToNatLt : Int.toNat ((48 : Int) + r) < 196608 := by
    rw [hCodeToNat]
    have hModLt : n % 10 < 10 := Nat.mod_lt n (by decide)
    omega
  have hCodeValid :
      native_char_valid (Int.toNat ((48 : Int) + r)) = true := by
    rw [show native_char_valid (Int.toNat ((48 : Int) + r)) =
      decide (Int.toNat ((48 : Int) + r) < 196608) by rfl]
    exact decide_eq_true hToNatLt
  have hDigit :
      Int.toNat ((48 : Int) + r) =
        Char.toNat (Nat.digitChar (n % 10)) := by
    rw [EvaluateProofInternal.native_digitChar_toNat_of_lt10 (Nat.mod_lt n (by decide))]
    exact hCodeToNat
  have hCodeNonnegRaw : 0 ≤ (48 : Int) + (Int.ofNat n % 10) := by
    simpa [r] using hCodeNonneg
  have hCodeLtRaw : (48 : Int) + (Int.ofNat n % 10) < 196608 := by
    simpa [r] using hCodeLt
  have hCodeValidRaw :
      native_char_valid (Int.toNat ((48 : Int) + (Int.ofNat n % 10))) =
        true := by
    simpa [r] using hCodeValid
  have hDigitRaw :
      Int.toNat ((48 : Int) + (Int.ofNat n % 10)) =
        Char.toNat (Nat.digitChar (n % 10)) := by
    simpa [r] using hDigit
  -- `native_zleq`/`native_zlt` unfold to `decide (_ < 196608)`, which simp then
  -- tries to evaluate by unary `Nat.rec` and blows the recursion limit.  Leave
  -- them folded; the `rw [ite_eq_left ..]` steps below discharge the guards.
  simp [__eo_zmod, __eo_add, __eo_to_str, native_ite, native_zeq,
    native_zplus, native_mod_total, native_and, native_str_from_code]
  -- both guards are folded `Bool` conjunctions `native_and _ _ = true`, not
  -- `And`s, so an anonymous constructor mis-elaborates; discharge them with the
  -- component facts instead (which also keeps the `196608` literal from being
  -- evaluated unarily)
  rw [ite_eq_left (by
    simp [native_and, native_zleq, native_zlt]
    exact ⟨hCodeNonnegRaw, hCodeLtRaw⟩)]
  rw [ite_eq_left (by
    try simp [native_and, native_zleq]
    exact ⟨hCodeNonnegRaw, hCodeValidRaw⟩)]
  change
    Term.String [Int.toNat ((48 : Int) + (Int.ofNat n % (10 : Int)))] =
      Term.String [Char.toNat (Nat.digitChar (n % 10))]
  rw [hDigitRaw]

theorem EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits :
    ∀ (fuel : native_Nat) (i : native_Int) (n : Nat) (acc : native_String),
      0 < n ->
      (Nat.toDigits 10 n).length ≤ fuel ->
        __str_from_int_eval_rec (EvaluateProofInternal.eo_iota_int_list fuel i)
          (Term.Numeral (Int.ofNat n)) (Term.String acc) =
        Term.String ((Nat.toDigits 10 n).map Char.toNat ++ acc)
  | 0, _i, n, _acc, _hPos, hLen => by
      have hDigitsPos : 0 < (Nat.toDigits 10 n).length :=
        Nat.length_toDigits_pos
      omega
  | fuel + 1, i, n, acc, hPos, hLen => by
      cases n with
      | zero =>
          omega
      | succ n =>
          change
            __str_from_int_eval_rec
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral i))
                (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1)))
              (Term.Numeral (Int.ofNat (n + 1))) (Term.String acc) =
            Term.String
              (List.map Char.toNat (Nat.toDigits 10 (n + 1)) ++ acc)
          rw [__str_from_int_eval_rec.eq_5]
          · have hDivTerm :
                __eo_zdiv (Term.Numeral (Int.ofNat (n + 1)))
                    (Term.Numeral 10) =
                  Term.Numeral (Int.ofNat ((n + 1) / 10)) := by
                simp [__eo_zdiv, native_ite, native_zeq,
                  native_div_total]
            have hDigitConcat :
                __eo_concat
                    (__eo_to_str
                      (__eo_add (Term.Numeral 48)
                        (__eo_zmod (Term.Numeral (Int.ofNat (n + 1)))
                          (Term.Numeral 10))))
                    (Term.String acc) =
                  Term.String
                    ([Char.toNat (Nat.digitChar ((n + 1) % 10))] ++ acc) := by
              rw [EvaluateProofInternal.eo_str_from_int_digit_term_nat (n + 1)]
              rfl
            rw [hDivTerm, hDigitConcat]
            by_cases hDiv : (n + 1) / 10 = 0
            · rw [hDiv]
              have hLt : n + 1 < 10 := by
                have hDiv' := hDiv
                rw [Nat.div_eq_zero_iff] at hDiv'
                rcases hDiv' with hTen | hLt
                · cases hTen
                · exact hLt
              have hDigits :
                  Nat.toDigits 10 (n + 1) =
                    [Nat.digitChar ((n + 1) % 10)] := by
                rw [Nat.toDigits_eq_ite (by decide : 1 < 10)]
                rw [ite_eq_left hLt]
                rw [Nat.mod_eq_of_lt hLt]
              rw [hDigits]
              change
                __str_from_int_eval_rec
                    (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1))
                    (Term.Numeral 0)
                    (Term.String
                      (Char.toNat (Nat.digitChar ((n + 1) % 10)) :: acc)) =
                  Term.String
                    (Char.toNat (Nat.digitChar ((n + 1) % 10)) :: acc)
              rw [__str_from_int_eval_rec.eq_4]
              · simp [__eo_eq, __eo_ite, native_ite, native_teq]
              · exact EvaluateProofInternal.eo_iota_int_list_ne_stuck fuel (native_zplus i 1)
              · intro h
                cases h
            · have hTailPos : 0 < (n + 1) / 10 :=
                Nat.pos_iff_ne_zero.mpr hDiv
              have hNotLt : ¬ n + 1 < 10 := by
                intro hLt
                exact hDiv (Nat.div_eq_of_lt hLt)
              have hDigits :
                  Nat.toDigits 10 (n + 1) =
                    Nat.toDigits 10 ((n + 1) / 10) ++
                      [Nat.digitChar ((n + 1) % 10)] := by
                rw [Nat.toDigits_eq_ite (by decide : 1 < 10)]
                rw [ite_eq_right hNotLt]
              have hTailLen :
                  (Nat.toDigits 10 ((n + 1) / 10)).length ≤ fuel := by
                rw [hDigits] at hLen
                simp at hLen
                omega
              have ih :=
                EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits fuel
                  (native_zplus i 1) ((n + 1) / 10)
                  ([Char.toNat (Nat.digitChar ((n + 1) % 10))] ++ acc)
                  hTailPos hTailLen
              rw [ih]
              rw [hDigits]
              simp [List.map_append, List.append_assoc]
          · intro h
            cases h
          · intro h
            injection h with hInt
            exact (Int.ne_of_gt (Int.ofNat_lt.mpr (Nat.succ_pos n))) hInt
          · intro h
            cases h

theorem EvaluateProofInternal.native_str_from_int_pos_toDigits
    {n : native_Int} (hPos : 0 < n) :
    native_str_from_int n =
      (Nat.toDigits 10 (Int.toNat n)).map Char.toNat := by
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hNotNeg : ¬ n < 0 := Int.not_lt_of_ge hNonneg
  unfold native_str_from_int
  rw [ite_eq_right hNotNeg]
  unfold native_string_lit
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  rw [← hCast]
  change (toString (Int.ofNat (Int.toNat n))).toList.map Char.toNat =
    (Nat.toDigits 10 (Int.toNat n)).map Char.toNat
  rw [show toString (Int.ofNat (Int.toNat n)) = toString (Int.toNat n) by
    rfl]
  rw [Nat.toString_eq_ofList_toDigits (n := Int.toNat n)]
  rw [String.toList_ofList]

theorem EvaluateProofInternal.native_int_log_rec10_pow_bound :
    ∀ fuel remaining : Nat,
      remaining ≤ fuel ->
      0 < remaining ->
        remaining < 10 ^ (impl_native_int_log_rec 10 fuel remaining + 1)
  | 0, remaining, hLe, _hPos => by
      omega
  | fuel + 1, remaining, hLe, hPos => by
      rw [impl_native_int_log_rec]
      by_cases hLt : remaining < 10
      · rw [ite_eq_left hLt]
        simpa using hLt
      · rw [ite_eq_right hLt]
        let q := remaining / 10
        let r := remaining % 10
        have hTenLe : 10 ≤ remaining := Nat.le_of_not_gt hLt
        have hqPos : 0 < q := by
          dsimp [q]
          exact Nat.div_pos_iff.mpr (by omega)
        have hqLtRemaining : q < remaining := by
          dsimp [q]
          exact Nat.div_lt_self hPos (by decide : 1 < 10)
        have hqLeFuel : q ≤ fuel := by
          omega
        have ih := EvaluateProofInternal.native_int_log_rec10_pow_bound fuel q hqLeFuel hqPos
        have hqSucc :
            q + 1 ≤ 10 ^ (impl_native_int_log_rec 10 fuel q + 1) :=
          Nat.succ_le_of_lt ih
        have hRemEq : remaining = 10 * q + r := by
          dsimp [q, r]
          simpa [Nat.mul_comm] using (Nat.div_add_mod remaining 10).symm
        have hrLt : r < 10 := by
          dsimp [r]
          exact Nat.mod_lt remaining (by decide)
        change remaining < 10 ^ (1 + impl_native_int_log_rec 10 fuel q + 1)
        rw [hRemEq]
        calc
          10 * q + r < 10 * (q + 1) := by omega
          _ ≤ 10 * 10 ^ (impl_native_int_log_rec 10 fuel q + 1) := by
            exact Nat.mul_le_mul_left 10 hqSucc
          _ = 10 ^ (impl_native_int_log_rec 10 fuel q + 1) * 10 := by
            rw [Nat.mul_comm]
          _ = 10 ^ (impl_native_int_log_rec 10 fuel q + 1 + 1) := by
            exact (Nat.pow_succ 10 (impl_native_int_log_rec 10 fuel q + 1)).symm
          _ = 10 ^ (1 + impl_native_int_log_rec 10 fuel q + 1) := by
            rw [show impl_native_int_log_rec 10 fuel q + 1 + 1 =
              1 + impl_native_int_log_rec 10 fuel q + 1 by
                simp [Nat.add_comm]]

theorem EvaluateProofInternal.native_int_log10_digit_len_bound
    {n : native_Int} (hPos : 0 < n) :
    (Nat.toDigits 10 (Int.toNat n)).length ≤
      native_int_to_nat (native_zplus (native_int_log 10 n) 1) := by
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  have hmPos : 0 < Int.toNat n := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < Int.ofNat (Int.toNat n)
    rw [hCast]
    exact hPos
  have hNotLe : ¬ n ≤ 0 := Int.not_le_of_gt hPos
  have hFuel :
      native_int_to_nat (native_zplus (native_int_log 10 n) 1) =
        impl_native_int_log_rec 10 (Int.toNat n) (Int.toNat n) + 1 := by
    unfold native_int_to_nat native_zplus native_int_log
    simp [hNotLe]
  rw [hFuel]
  rw [Nat.length_toDigits_le_iff (b := 10)
    (n := Int.toNat n)
    (k := impl_native_int_log_rec 10 (Int.toNat n) (Int.toNat n) + 1)
    (by decide : 1 < 10)
    (Nat.succ_pos _)]
  exact EvaluateProofInternal.native_int_log_rec10_pow_bound (Int.toNat n) (Int.toNat n)
    (Nat.le_refl _) hmPos

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_neg
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hNeg : n < 0) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  have hNegBool : native_zlt n 0 = true := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_true hNeg
  have hNative : native_str_from_int n = [] := by
    unfold native_str_from_int
    rw [ite_eq_left hNeg]
    simp [native_string_lit]
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
    native_ite, native_teq, native_and, native_not, hNegBool, hNative]

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_zero
    {x : Term}
    (hRun : __run_evaluate x = Term.Numeral 0) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int 0) := by
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  native_decide

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_pos
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hPos : 0 < n) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  have hReduced :
      EvaluateProofInternal.eo_eval_str_from_int_rhs x =
        __str_from_int_eval_rec
          (EvaluateProofInternal.eo_iota_int_list
            (native_int_to_nat (native_zplus (native_int_log 10 n) 1)) 0)
          (Term.Numeral n) (Term.String []) := by
    have hNegBool : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt_of_ge (Int.le_of_lt hPos))
    have hLogNonneg : 0 ≤ native_int_log 10 n := by
      unfold native_int_log
      by_cases hCond :
          (decide (Int.toNat 10 ≤ 1) || Int.toNat n == 0) = true
      · rw [ite_eq_left hCond]
        decide
      · rw [ite_eq_right hCond]
        exact Int.natCast_nonneg _
    have hFuelNonneg :
        ¬ native_zplus (native_int_log 10 n) 1 < 0 := by
      exact Int.not_lt_of_ge
        (by
          unfold native_zplus
          exact Int.add_nonneg hLogNonneg (by decide))
    have hFuelNegBool :
        native_zlt (native_zplus (native_int_log 10 n) 1) 0 = false := by
      rw [show native_zlt (native_zplus (native_int_log 10 n) 1) 0 =
        decide (native_zplus (native_int_log 10 n) 1 < 0) by rfl]
      exact decide_eq_false hFuelNonneg
    dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
    rw [hRun]
    simp only [__eo_log, __eo_add]
    rw [EvaluateProofInternal.eo_iota_list_repeat_int_of_nonneg (k :=
      native_zplus (native_int_log 10 n) 1) (i := 0) hFuelNonneg]
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_requires, native_ite, native_teq, native_and, native_not,
      hNegBool, hFuelNegBool]
  rw [hReduced]
  rw [EvaluateProofInternal.native_str_from_int_pos_toDigits hPos]
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  have hmPos : 0 < Int.toNat n := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < Int.ofNat (Int.toNat n)
    rw [hCast]
    exact hPos
  have hLen := EvaluateProofInternal.native_int_log10_digit_len_bound hPos
  have hTermCast :
      Term.Numeral (Int.ofNat (Int.toNat n)) = Term.Numeral n := by
    rw [hCast]
  rw [← hTermCast]
  simpa using
    EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits
      (native_int_to_nat (native_zplus (native_int_log 10 n) 1))
      0 (Int.toNat n) [] hmPos hLen

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  by_cases hNeg : n < 0
  · exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_neg hRun hNeg
  · by_cases hZero : n = 0
    · subst n
      exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_zero hRun
    · have hNonneg : 0 ≤ n := Int.le_of_not_gt hNeg
      have hPos : 0 < n := by
        by_cases hPos : 0 < n
        · exact hPos
        · have hLeZero : n ≤ 0 := Int.le_of_not_gt hPos
          have hEq : n = 0 := Int.le_antisymm hLeZero hNonneg
          exact False.elim (hZero hEq)
      exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_pos hRun hPos

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_non_numeral
    {x t : Term}
    (hRun : __run_evaluate x = t)
    (hNotNumeral : ∀ n : native_Int, t ≠ Term.Numeral n)
    (hTNe : t ≠ Term.Stuck) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x =
      Term.Apply (Term.UOp UserOp.str_from_int) t := by
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  cases t <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
      native_ite, native_teq, native_and, native_not] at hNotNumeral hTNe ⊢

