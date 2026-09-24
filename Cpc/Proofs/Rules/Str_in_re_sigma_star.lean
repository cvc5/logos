module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem native_string_lit_empty :
    native_string_lit "" = ([] : native_String) := by
  simp [native_string_lit]

private def nativeSigmaPrefix : Nat -> SmtRegLan
  | 0 => SmtRegLan.epsilon
  | 1 => native_re_allchar
  | n + 2 => SmtRegLan.concat native_re_allchar (nativeSigmaPrefix (n + 1))

private theorem nativeSigmaPrefix_succ_ne_empty (n : Nat) :
    nativeSigmaPrefix (n + 1) ≠ SmtRegLan.empty := by
  cases n <;> simp [nativeSigmaPrefix, native_re_allchar]

private theorem nativeSigmaPrefix_succ_ne_epsilon (n : Nat) :
    nativeSigmaPrefix (n + 1) ≠ SmtRegLan.epsilon := by
  cases n <;> simp [nativeSigmaPrefix, native_re_allchar]

private theorem native_re_mk_concat_allchar_sigmaPrefix_succ (n : Nat) :
    native_re_mk_concat native_re_allchar (nativeSigmaPrefix (n + 1)) =
      SmtRegLan.concat native_re_allchar (nativeSigmaPrefix (n + 1)) := by
  cases n <;>
    simp [native_re_mk_concat, native_re_concat, nativeSigmaPrefix,
      native_re_allchar]

private theorem nativeListInRe_sigmaPrefix_true_iff :
    (n : Nat) -> (xs : List native_Char) ->
      nativeListInRe xs (nativeSigmaPrefix n) = true <->
        xs.length = n ∧ native_string_valid xs = true
  | 0, xs => by
      cases xs with
      | nil =>
          simp [nativeSigmaPrefix, nativeListInRe, native_re_nullable,
            native_string_valid]
      | cons _ cs =>
          simpa [nativeSigmaPrefix, nativeListInRe, native_re_nullable,
            native_re_deriv, native_string_valid] using nativeListInRe_empty cs
  | n + 1, xs => by
      cases n with
      | zero =>
          constructor
          · intro h
            have hParts :
                xs.length = 1 ∧ xs.all native_char_valid = true :=
              (nativeListInRe_allchar_true_iff xs).1
                (by simpa [nativeSigmaPrefix] using h)
            exact ⟨hParts.1, by simpa [native_string_valid] using hParts.2⟩
          · intro hParts
            rcases hParts with ⟨hLen, hValid⟩
            have hAll : xs.all native_char_valid = true := by
              simpa [native_string_valid] using hValid
            have hAllchar : nativeListInRe xs native_re_allchar = true :=
              (nativeListInRe_allchar_true_iff xs).2 ⟨hLen, hAll⟩
            simpa [nativeSigmaPrefix] using hAllchar
      | succ n =>
          constructor
          · intro h
            have hMk := native_re_mk_concat_allchar_sigmaPrefix_succ n
            have hConcat :
                nativeListInRe xs
                    (native_re_mk_concat native_re_allchar
                      (nativeSigmaPrefix (n + 1))) =
                  true := by
              simpa [nativeSigmaPrefix, hMk] using h
            rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
                native_re_allchar (nativeSigmaPrefix (n + 1))).1 hConcat with
              ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
            have hLeftParts :
                xs₁.length = 1 ∧ xs₁.all native_char_valid = true :=
              (nativeListInRe_allchar_true_iff xs₁).1 hLeft
            have hRightParts :
                xs₂.length = n + 1 ∧ native_string_valid xs₂ = true :=
              (nativeListInRe_sigmaPrefix_true_iff (n + 1) xs₂).1 hRight
            have hLenEq := congrArg List.length hAppend
            have hValid : native_string_valid xs = true := by
              have hRightAll : xs₂.all native_char_valid = true := by
                simpa [native_string_valid] using hRightParts.2
              rw [← hAppend]
              simp [native_string_valid, List.all_append, hLeftParts.2, hRightAll]
            simp [hLeftParts.1, hRightParts.1] at hLenEq
            exact ⟨by omega, hValid⟩
          · intro hParts
            rcases hParts with ⟨hLen, hValid⟩
            let xs₁ := xs.take 1
            let xs₂ := xs.drop 1
            have hLeftLen : xs₁.length = 1 := by
              simp [xs₁]
              omega
            have hRightLen : xs₂.length = n + 1 := by
              simp [xs₂]
              omega
            have hAppend : xs₁ ++ xs₂ = xs := by
              simpa [xs₁, xs₂] using (List.take_append_drop 1 xs)
            have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
              simpa [native_string_valid, hAppend] using hValid
            rw [List.all_append] at hValidAppend
            have hValidParts :
                xs₁.all native_char_valid = true ∧
                  xs₂.all native_char_valid = true := by
              simpa [Bool.and_eq_true] using hValidAppend
            have hLeft : nativeListInRe xs₁ native_re_allchar = true :=
              (nativeListInRe_allchar_true_iff xs₁).2
                ⟨hLeftLen, hValidParts.1⟩
            have hRight :
                nativeListInRe xs₂ (nativeSigmaPrefix (n + 1)) = true :=
              (nativeListInRe_sigmaPrefix_true_iff (n + 1) xs₂).2
                ⟨hRightLen, by simpa [native_string_valid] using hValidParts.2⟩
            have hConcat :
                nativeListInRe xs
                    (native_re_mk_concat native_re_allchar
                      (nativeSigmaPrefix (n + 1))) =
                  true :=
              (nativeListInRe_mk_concat_true_iff_exists_append xs
                native_re_allchar (nativeSigmaPrefix (n + 1))).2
                ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
            have hMk := native_re_mk_concat_allchar_sigmaPrefix_succ n
            simpa [nativeSigmaPrefix, hMk] using hConcat

private theorem native_re_mult_sigmaPrefix_eq_star
    (n : Nat) (hn : n ≠ 0) :
    native_re_mult (nativeSigmaPrefix n) =
      SmtRegLan.star (nativeSigmaPrefix n) := by
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ n =>
      cases n <;> simp [native_re_mult, nativeSigmaPrefix,
        native_re_allchar]

private theorem nativeListInRe_star_append_intro (r : SmtRegLan) :
    (xs ys : List native_Char) ->
      nativeListInRe xs r = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, hLeft, hRight => by
      change
        nativeListInRe (cs ++ ys)
            (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
          true
      exact (nativeListInRe_mk_concat_true_iff_exists_append (cs ++ ys)
          (native_re_deriv c r) (SmtRegLan.star r)).2
        ⟨cs, ys, rfl, by simpa [nativeListInRe] using hLeft, hRight⟩

private theorem nativeListInRe_sigmaPrefixStar_true_iff_dvd
    (n : Nat) (hn : n ≠ 0) :
    (xs : List native_Char) ->
    nativeListInRe xs (native_re_mult (nativeSigmaPrefix n)) = true <->
      n ∣ xs.length ∧ native_string_valid xs = true
  | [] => by
      have hStar := native_re_mult_sigmaPrefix_eq_star n hn
      constructor
      · intro _h
        exact ⟨⟨0, by simp⟩, by simp [native_string_valid]⟩
      · intro _h
        rw [hStar]
        simp [nativeListInRe, native_re_nullable]
  | c :: cs => by
      have hStar := native_re_mult_sigmaPrefix_eq_star n hn
      constructor
      · intro h
        have hRaw :
            nativeListInRe (c :: cs)
                (SmtRegLan.star (nativeSigmaPrefix n)) =
              true := by
          simpa [hStar] using h
        change
          nativeListInRe cs
              (native_re_mk_concat
                (native_re_deriv c (nativeSigmaPrefix n))
                (SmtRegLan.star (nativeSigmaPrefix n))) =
            true at hRaw
        rcases (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c (nativeSigmaPrefix n))
            (SmtRegLan.star (nativeSigmaPrefix n))).1 hRaw with
          ⟨left, right, hAppend, hLeft, hRight⟩
        have hPrefix :
            nativeListInRe (c :: left) (nativeSigmaPrefix n) = true := by
          simpa [nativeListInRe] using hLeft
        have hPrefixParts :
            (c :: left).length = n ∧
              native_string_valid (c :: left) = true :=
          (nativeListInRe_sigmaPrefix_true_iff n (c :: left)).1 hPrefix
        have hRightStar :
            nativeListInRe right (native_re_mult (nativeSigmaPrefix n)) =
              true := by
          simpa [hStar] using hRight
        have hRightLt : right.length < (c :: cs).length := by
          have hAppendLen := congrArg List.length hAppend
          simp at hAppendLen hPrefixParts ⊢
          omega
        have hRightParts :
            n ∣ right.length ∧ native_string_valid right = true :=
          (nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn right).1 hRightStar
        constructor
        · rcases hRightParts.1 with ⟨q, hq⟩
          have hDecomp : c :: cs = (c :: left) ++ right := by
            simp [hAppend]
          have hLenTotal : (c :: cs).length = n + right.length := by
            have hAppendLen := congrArg List.length hAppend
            have hLeftLen : left.length + 1 = n := by
              simpa using hPrefixParts.1
            simp at hAppendLen ⊢
            omega
          refine ⟨q + 1, ?_⟩
          calc
            (c :: cs).length = n + right.length := hLenTotal
            _ = n + n * q := by rw [hq]
            _ = n * (q + 1) := by
              rw [Nat.mul_succ]
              omega
        · have hDecomp : c :: cs = (c :: left) ++ right := by
            simp [hAppend]
          have hPrefixAll :
              (c :: left).all native_char_valid = true := by
            simpa [native_string_valid] using hPrefixParts.2
          have hRightAll : right.all native_char_valid = true := by
            simpa [native_string_valid] using hRightParts.2
          have hAll : ((c :: left) ++ right).all native_char_valid = true := by
            rw [List.all_append]
            simp [hPrefixAll, hRightAll]
          rw [hDecomp]
          simpa [native_string_valid] using hAll
      · intro hParts
        rcases hParts with ⟨hDvd, hValid⟩
        rcases hDvd with ⟨q, hq⟩
        cases q with
        | zero =>
            have hZero : (c :: cs).length = 0 := by
              simpa using hq
            simp at hZero
        | succ q =>
            let xs₁ := (c :: cs).take n
            let xs₂ := (c :: cs).drop n
            have hnPos : 0 < n := Nat.pos_of_ne_zero hn
            have hNLe : n ≤ (c :: cs).length := by
              rw [hq, Nat.mul_succ]
              omega
            have hLeftLen : xs₁.length = n := by
              have hMin : min n (c :: cs).length = n := Nat.min_eq_left hNLe
              simpa [xs₁] using hMin
            have hRightLen : xs₂.length = n * q := by
              have hDrop : xs₂.length = (c :: cs).length - n := by
                simpa [xs₂] using (List.length_drop n (c :: cs))
              calc
                xs₂.length = (c :: cs).length - n := hDrop
                _ = n * (q + 1) - n := by rw [hq]
                _ = n * q := by
                  rw [Nat.mul_succ]
                  omega
            have hAppend : xs₁ ++ xs₂ = c :: cs := by
              simpa [xs₁, xs₂] using (List.take_append_drop n (c :: cs))
            have hValidAppend :
                (xs₁ ++ xs₂).all native_char_valid = true := by
              simpa [native_string_valid, hAppend] using hValid
            rw [List.all_append] at hValidAppend
            have hValidParts :
                xs₁.all native_char_valid = true ∧
                  xs₂.all native_char_valid = true := by
              simpa [Bool.and_eq_true] using hValidAppend
            have hLeft :
                nativeListInRe xs₁ (nativeSigmaPrefix n) = true :=
              (nativeListInRe_sigmaPrefix_true_iff n xs₁).2
                ⟨hLeftLen,
                  by simpa [native_string_valid] using hValidParts.1⟩
            have hRightLt : xs₂.length < (c :: cs).length := by
              rw [hRightLen, hq, Nat.mul_succ]
              omega
            have hRightStar :
                nativeListInRe xs₂
                    (native_re_mult (nativeSigmaPrefix n)) =
                  true :=
              (nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn xs₂).2
                ⟨⟨q, hRightLen⟩,
                  by simpa [native_string_valid] using hValidParts.2⟩
            have hRightRaw :
                nativeListInRe xs₂
                    (SmtRegLan.star (nativeSigmaPrefix n)) =
                  true := by
              simpa [hStar] using hRightStar
            have hCombinedRaw :
                nativeListInRe (xs₁ ++ xs₂)
                    (SmtRegLan.star (nativeSigmaPrefix n)) =
                  true :=
              nativeListInRe_star_append_intro (nativeSigmaPrefix n)
                xs₁ xs₂ hLeft hRightRaw
            have hCombined :
                nativeListInRe (xs₁ ++ xs₂)
                    (native_re_mult (nativeSigmaPrefix n)) =
                  true := by
              rw [hStar]
              exact hCombinedRaw
            simpa [hAppend] using hCombined
termination_by xs => xs.length
decreasing_by
  all_goals
    omega

private theorem nativeListInRe_sigmaPrefixStar_eq_int_mod
    (n : Nat) (hn : n ≠ 0) (xs : List native_Char)
    (hValid : native_string_valid xs = true) :
    nativeListInRe xs (native_re_mult (nativeSigmaPrefix n)) =
      decide (((xs.length : Int) % (Int.ofNat n)) = 0) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_iff]
    have hDvdNat : n ∣ xs.length :=
      ((nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn xs).1 h).1
    have hDvdInt : (Int.ofNat n) ∣ (Int.ofNat xs.length) := by
      rcases hDvdNat with ⟨q, hq⟩
      refine ⟨Int.ofNat q, ?_⟩
      rw [hq]
      simp
    exact Int.emod_eq_zero_of_dvd hDvdInt
  · intro h
    have hMod : ((xs.length : Int) % (Int.ofNat n)) = 0 :=
      of_decide_eq_true h
    have hDvdInt : (Int.ofNat n) ∣ (Int.ofNat xs.length) :=
      Int.dvd_of_emod_eq_zero hMod
    have hDvdNat : n ∣ xs.length := by
      rw [<- Int.ofNat_dvd]
      exact hDvdInt
    exact (nativeListInRe_sigmaPrefixStar_true_iff_dvd n hn xs).2
      ⟨hDvdNat, hValid⟩

private theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simp [native_unpack_string]

private theorem str_in_re_sigma_star_rec_empty_ne_zero
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
        (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      n ≠ 0 := by
  intro hSide hn
  apply hSide
  subst n
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      simp [__str_mk_str_in_re_sigma_star_rec, __eo_requires, __eo_eq,
        native_teq, native_ite,
        native_string_lit_empty]

private theorem str_in_re_sigma_star_rec_empty_eq
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) (hn : n ≠ 0) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
        (Term.Numeral (Int.ofNat n)) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.mod)
              (Term.Apply (Term.UOp UserOp.str_len) s))
            (Term.Numeral (Int.ofNat n))))
        (Term.Numeral 0) := by
  have hnInt : (Int.ofNat n) ≠ 0 := by
    intro hZero
    exact hn (Int.ofNat_eq_zero.mp hZero)
  have hZeroNe : (0 : Int) ≠ Int.ofNat n := by
    intro hZero
    exact hn (Int.ofNat_eq_zero.mp hZero.symm)
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      (simp [__str_mk_str_in_re_sigma_star_rec, __eo_requires, __eo_eq,
        native_teq, native_ite, native_not, SmtEval.native_not,
        native_string_lit_empty]
       exact hZeroNe)

private theorem str_in_re_sigma_star_rec_str_to_re_nonempty_eq_stuck
    (s : Term) (str : native_String) (n : Nat)
    (hStr : str ≠ native_string_lit "") :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String str))
        (Term.Numeral (Int.ofNat n)) =
      Term.Stuck := by
  have hStrNil : str ≠ ([] : native_String) := by
    simpa [native_string_lit_empty] using hStr
  cases s <;> unfold __str_mk_str_in_re_sigma_star_rec <;>
    simp [hStrNil]

private theorem str_in_re_sigma_star_rec_allchar_eq
    (s r : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_star_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_allchar)) r)
        (Term.Numeral (Int.ofNat n)) =
      __str_mk_str_in_re_sigma_star_rec s r
        (Term.Numeral (Int.ofNat (n + 1))) := by
  simp [__str_mk_str_in_re_sigma_star_rec, __eo_add, native_zplus, Int.natCast_add]

private theorem smtx_model_eval_str_in_re_sigma_star_rec
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char)
    (hSSValid : native_string_valid (native_unpack_string ss) = true)
    (r : Term) (rv : SmtRegLan) (n : Nat) :
      __str_mk_str_in_re_sigma_star_rec s r
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      exists m : Nat,
        rv = nativeSigmaPrefix m /\
          n + m ≠ 0 /\
          __smtx_model_eval M
              (__eo_to_smt
                (__str_mk_str_in_re_sigma_star_rec s r
                  (Term.Numeral (Int.ofNat n)))) =
            SmtValue.Boolean
              (decide ((((native_unpack_string ss).length : Int) %
                (Int.ofNat (n + m))) = 0))
:= by
  intro hSide hREval
  cases r with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases x with
              | String str =>
                  by_cases hStr : str = native_string_lit ""
                  · subst str
                    have hRv : rv = SmtRegLan.epsilon := by
                      change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String (native_string_lit ""))) =
                          SmtValue.RegLan rv at hREval
                      rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_4] at hREval
                      have hsimpa := hREval.symm
                      try simp [__smtx_model_eval_str_to_re, native_str_to_re, native_pack_string] at hsimpa ⊢
                      exact hsimpa
                    subst rv
                    have hn : n ≠ 0 :=
                      str_in_re_sigma_star_rec_empty_ne_zero s n hSNe hSide
                    refine ⟨0, by simp [nativeSigmaPrefix], by simpa using hn, ?_⟩
                    rw [str_in_re_sigma_star_rec_empty_eq s n hSNe hn]
                    change
                      __smtx_model_eval M
                          (SmtTerm.eq
                            (SmtTerm.mod (SmtTerm.str_len (__eo_to_smt s))
                              (SmtTerm.Numeral (Int.ofNat n)))
                            (SmtTerm.Numeral 0)) =
                        SmtValue.Boolean
                          (decide ((((native_unpack_string ss).length : Int) %
                            (Int.ofNat (n + 0))) = 0))
                    rw [smtx_eval_eq_term_eq, __smtx_model_eval.eq_27,
                      smtx_eval_str_len_term_eq, __smtx_model_eval.eq_2,
                      __smtx_model_eval.eq_2, hSEval]
                    have hnInt : (Int.ofNat n) ≠ 0 := by
                      intro hZero
                      exact hn (Int.ofNat_eq_zero.mp hZero)
                    simp [__smtx_model_eval_eq, __smtx_model_eval_mod_total,
                      __smtx_model_eval_str_len, __smtx_model_eval_ite,
                      native_veq, native_mod_total,
                      native_seq_len, native_unpack_string_length_eq,
                      hn]
                  · exfalso
                    apply hSide
                    exact str_in_re_sigma_star_rec_str_to_re_nonempty_eq_stuck
                      s str n hStr
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_star_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_star_rec]
      | Apply f1 y =>
          cases f1 with
          | UOp op1 =>
              cases op1 with
              | re_concat =>
                  cases y with
                  | UOp yop =>
                      cases yop with
                      | re_allchar =>
                          change __smtx_model_eval M
                              (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt x)) =
                            SmtValue.RegLan rv at hREval
                          rw [__smtx_model_eval.eq_114, __smtx_model_eval.eq_104] at hREval
                          cases hTailEval : __smtx_model_eval M (__eo_to_smt x) with
                          | RegLan rvTail =>
                              have hRv : rv = native_re_concat native_re_allchar rvTail := by
                                simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                                exact hREval.symm
                              subst rv
                              have hSideTail :
                                  __str_mk_str_in_re_sigma_star_rec s x
                                      (Term.Numeral (Int.ofNat (n + 1))) ≠
                                    Term.Stuck := by
                                rw [<- str_in_re_sigma_star_rec_allchar_eq s x n hSNe]
                                exact hSide
                              rcases smtx_model_eval_str_in_re_sigma_star_rec
                                  M s ss hSNe hSEval hSsTy hSSValid x rvTail (n + 1)
                                  hSideTail hTailEval with
                                ⟨m, hTailRv, hTotalNe, hEval⟩
                              refine ⟨m + 1, ?_, ?_, ?_⟩
                              · subst rvTail
                                cases m with
                                | zero =>
                                    simp [native_re_concat, nativeSigmaPrefix,
                                      native_re_allchar]
                                | succ m =>
                                    have hNeEmpty := nativeSigmaPrefix_succ_ne_empty m
                                    have hNeEps := nativeSigmaPrefix_succ_ne_epsilon m
                                    simp [native_re_concat, nativeSigmaPrefix,
                                      native_re_allchar]
                              · omega
                              · rw [str_in_re_sigma_star_rec_allchar_eq s x n hSNe]
                                have hTotal :
                                    n + (m + 1) = n + 1 + m := by
                                  omega
                                simpa [hTotal] using hEval
                          | _ =>
                              simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                      | _ =>
                          exfalso
                          apply hSide
                          simpa [__str_mk_str_in_re_sigma_star_rec]
                  | _ =>
                      exfalso
                      apply hSide
                      simpa [__str_mk_str_in_re_sigma_star_rec]
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_star_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_star_rec]
      | _ =>
          exfalso
          apply hSide
          simpa [__str_mk_str_in_re_sigma_star_rec]
  | _ =>
      exfalso
      apply hSide
      simpa [__str_mk_str_in_re_sigma_star_rec]
termination_by r

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  have hxNe : y ≠ Term.Stuck := by
    intro hy
    subst y
    simp at hxOk
  exact hxNe hx

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) /\
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x /\
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_in_re_args_smt_types_of_has_translation
    (s r : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char /\
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) ≠
      SmtType.None
    exact hTrans
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re) (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

private theorem smtx_model_eval_str_in_re_eq_sigma_star_side
    (M : SmtModel) (s r side : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char)
    (hSSValid : native_string_valid (native_unpack_string ss) = true)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      side = __str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0))
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply (Term.UOp UserOp.re_mult) r))) =
      __smtx_model_eval M (__eo_to_smt side) := by
  subst side
  rcases smtx_model_eval_str_in_re_sigma_star_rec M s ss hSNe hSEval hSsTy
      hSSValid r rv 0 hSideNe hREval with
    ⟨m, hRv, hMNe, hSideEval⟩
  have hSideEval' :
      __smtx_model_eval M
          (__eo_to_smt (__str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0))) =
        SmtValue.Boolean
          (decide ((((native_unpack_string ss).length : Int) %
            (Int.ofNat (0 + m))) = 0)) := by
    simpa using hSideEval
  rw [hSideEval']
  change
    __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (SmtTerm.re_mult (__eo_to_smt r))) =
      SmtValue.Boolean
        (decide ((((native_unpack_string ss).length : Int) %
          (Int.ofNat (0 + m))) = 0))
  rw [__smtx_model_eval.eq_119, __smtx_model_eval.eq_108]
  rw [hSEval, hREval]
  subst rv
  have hm : m ≠ 0 := by
    simpa using hMNe
  simp only [__smtx_model_eval_re_mult, __smtx_model_eval_str_in_re]
  rw [model_str_in_re_unpack_eq_string_of_value_type ss
    (native_re_mult (nativeSigmaPrefix m)) hSsTy]
  simp [native_str_in_re, hSSValid]
  simpa [nativeListInRe] using
    nativeListInRe_sigmaPrefixStar_eq_int_mod m hm (native_unpack_string ss)
      hSSValid

private theorem str_in_re_sigma_star_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b))
    (hProgNe :
      __eo_prog_str_in_re_sigma_star
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_sigma_star
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply (Term.UOp UserOp.re_mult) r))) b)) := by
  let reStar := Term.Apply (Term.UOp UserOp.re_mult) r
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) reStar
  let side := __str_mk_str_in_re_sigma_star_rec s r (Term.Numeral 0)
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hReqEq : side = b := eo_requires_eq_of_ne_stuck side b body hProgNe
  have hReqResult : __eo_requires side b body = body :=
    eo_requires_result_eq_of_ne_stuck side b body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hProgNe
  subst b
  change StepRuleProperties M [] (__eo_requires side side body)
  rw [hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [reStar, strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn side hEqTrans with
    ⟨hStrInTrans, _hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s reStar (by
      simpa [strIn] using hStrInTrans) with
    ⟨hSTy, hStarTy⟩
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    have hRNN : term_has_non_none_type (__eo_to_smt r) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt r) ≠ SmtType.None
      change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hStarTy
      rw [typeof_re_mult_eq] at hStarTy
      by_cases hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
      · rw [hRTy]
        simp
      · simp [hRTy, native_ite, native_Teq] at hStarTy
    have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
      change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan at hStarTy
      rw [typeof_re_mult_eq] at hStarTy
      by_cases hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan
      · exact hRTy
      · simp [hRTy, native_ite, native_Teq] at hStarTy
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) hRNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSSValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simp only [hSEval] at hSEvalTy
    exact hSEvalTy
  have hSNe : s ≠ Term.Stuck := by
    intro hs
    apply hSideNe
    subst s
    simp [side, __str_mk_str_in_re_sigma_star_rec]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt strIn) =
        __smtx_model_eval M (__eo_to_smt side) := by
    exact smtx_model_eval_str_in_re_eq_sigma_star_side M s r side ss rv hSNe hSEval
      hSsTy hSSValid hREval rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt side))

end RuleProofs

public theorem cmd_step_str_in_re_sigma_star_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_sigma_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp reStar =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              cases reStar with
                                              | Apply starOp r =>
                                                  cases starOp with
                                                  | UOp starOpName =>
                                                      cases starOpName with
                                                      | re_mult =>
                                                          have hProps :=
                                                            RuleProofs.str_in_re_sigma_star_valid_properties
                                                              M hM str r b (by
                                                                simpa using hA1Trans) (by
                                                                change
                                                                  __eo_prog_str_in_re_sigma_star
                                                                    (Term.Apply
                                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                                        (Term.Apply
                                                                          (Term.Apply
                                                                            (Term.UOp UserOp.str_in_re) str)
                                                                          (Term.Apply
                                                                            (Term.UOp UserOp.re_mult) r))) b) ≠
                                                                    Term.Stuck at hProg
                                                                exact hProg)
                                                          change StepRuleProperties M []
                                                            (__eo_prog_str_in_re_sigma_star
                                                              (Term.Apply
                                                                (Term.Apply (Term.UOp UserOp.eq)
                                                                  (Term.Apply
                                                                    (Term.Apply
                                                                      (Term.UOp UserOp.str_in_re) str)
                                                                    (Term.Apply
                                                                      (Term.UOp UserOp.re_mult) r))) b))
                                                          simpa [premiseTermList] using hProps
                                                      | _ =>
                                                          change Term.Stuck ≠ Term.Stuck at hProg
                                                          exact False.elim (hProg rfl)
                                                  | _ =>
                                                      change Term.Stuck ≠ Term.Stuck at hProg
                                                      exact False.elim (hProg rfl)
                                              | _ =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
