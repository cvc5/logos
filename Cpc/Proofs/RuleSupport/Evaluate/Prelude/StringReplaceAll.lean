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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReplaceAllChain
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringReplaceAllChain
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringIndexof

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.native_str_replace_all_eval_aux
    (fuel : Nat) (pat repl : native_String) :
    native_String -> native_String
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := native_str_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                xs.take n ++ repl ++
                  EvaluateProofInternal.native_str_replace_all_eval_aux fuel pat repl
                    (xs.drop (n + pat.length))

def EvaluateProofInternal.native_str_replace_all_eval_result
    (s pat repl : native_String) : native_String :=
  EvaluateProofInternal.native_str_replace_all_eval_aux (s.length + 1) pat repl s

theorem EvaluateProofInternal.native_str_replace_all_eval_result_nil
    (s repl : native_String) :
    EvaluateProofInternal.native_str_replace_all_eval_result s [] repl = s := by
  unfold EvaluateProofInternal.native_str_replace_all_eval_result
  cases s <;>
    simp [EvaluateProofInternal.native_str_replace_all_eval_aux]

theorem EvaluateProofInternal.native_str_replace_all_eval_aux_prefix_cons
    (fuel : Nat) (s repl : native_String) (p : native_Char)
    (ps : native_String)
    (hPrefix : native_string_prefix_eq (p :: ps) s = true) :
    EvaluateProofInternal.native_str_replace_all_eval_aux (fuel + 1) (p :: ps) repl s =
      repl ++
        EvaluateProofInternal.native_str_replace_all_eval_aux fuel (p :: ps) repl
          (s.drop (ps.length + 1)) := by
  have hIdx : native_str_indexof s (p :: ps) 0 = 0 :=
    EvaluateProofInternal.native_str_indexof_zero_of_prefix s (p :: ps) hPrefix
  simp [EvaluateProofInternal.native_str_replace_all_eval_aux, hIdx]

theorem EvaluateProofInternal.native_str_replace_all_eval_aux_eq_chain_of_fuel
    (pat repl : native_String) :
    ∀ (fuel : Nat) (s : native_String),
      s.length + 1 ≤ fuel ->
      pat ≠ [] ->
      EvaluateProofInternal.native_str_replace_all_eval_aux fuel pat repl s =
        EvaluateProofInternal.native_str_replace_all_chain pat repl 0 s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro s hFuel hPat
      cases fuel with
      | zero =>
          omega
      | succ fuel' =>
          cases pat with
          | nil =>
              contradiction
          | cons p ps =>
              cases s with
              | nil =>
                  have hIdx :
                      native_str_indexof [] (p :: ps) 0 = -1 := by
                    simp [native_str_indexof, native_str_len]
                  simp [EvaluateProofInternal.native_str_replace_all_eval_aux,
                    EvaluateProofInternal.native_str_replace_all_chain, hIdx]
              | cons c cs =>
                  have hCsFuel : cs.length + 1 ≤ fuel' := by
                    simp at hFuel
                    omega
                  by_cases hPref :
                      native_string_prefix_eq (p :: ps) (c :: cs) = true
                  · rw [EvaluateProofInternal.native_str_replace_all_eval_aux_prefix_cons fuel'
                      (c :: cs) repl p ps hPref]
                    have hDropLen :
                        ((c :: cs).drop (ps.length + 1)).length ≤
                          cs.length := by
                      simp [List.length_drop]
                    have hDropFuel :
                        ((c :: cs).drop (ps.length + 1)).length + 1 ≤
                          fuel' := by
                      omega
                    rw [ih fuel' (by omega)
                      ((c :: cs).drop (ps.length + 1)) hDropFuel
                      (by simp)]
                    simp [EvaluateProofInternal.native_str_replace_all_chain, hPref,
                      EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop]
                  · have hPrefFalse :
                        native_string_prefix_eq (p :: ps) (c :: cs) =
                          false := by
                      cases hp :
                          native_string_prefix_eq (p :: ps) (c :: cs) <;>
                        simp [hp] at hPref ⊢
                    have hConsIdx :=
                      EvaluateProofInternal.native_str_indexof_cons_not_prefix c p cs ps
                        hPrefFalse
                    by_cases hTailNeg :
                        native_str_indexof cs (p :: ps) 0 < 0
                    · have hTailEq :
                          native_str_indexof cs (p :: ps) 0 = -1 :=
                        EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg cs (p :: ps)
                          hTailNeg
                      have hParentNeg :
                          native_str_indexof (c :: cs) (p :: ps) 0 < 0 := by
                        rw [hConsIdx, hTailEq]
                        decide
                      have hTailEvalSelf :
                          EvaluateProofInternal.native_str_replace_all_eval_aux fuel' (p :: ps)
                              repl cs =
                            cs := by
                        cases fuel' with
                        | zero =>
                            omega
                        | succ fuel'' =>
                            simp [EvaluateProofInternal.native_str_replace_all_eval_aux,
                              hTailNeg]
                      have hTailChain :
                          EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs =
                            cs := by
                        rw [← ih fuel' (by omega) cs hCsFuel (by simp)]
                        exact hTailEvalSelf
                      simp [EvaluateProofInternal.native_str_replace_all_eval_aux, hParentNeg,
                        EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse,
                        hTailChain]
                    · have hTailNonneg :
                          0 ≤ native_str_indexof cs (p :: ps) 0 :=
                        Int.le_of_not_gt hTailNeg
                      let r := native_str_indexof cs (p :: ps) 0
                      let n := Int.toNat r
                      have hRcast : Int.ofNat n = r :=
                        Int.toNat_of_nonneg hTailNonneg
                      have hTailFit :
                          n + (p :: ps).length ≤ cs.length := by
                        simpa [r, n] using
                          EvaluateProofInternal.native_str_indexof_zero_nonneg_toNat_add_pat_le_len
                            cs (p :: ps) hTailNonneg
                      have hTailNe : r ≠ -1 := by
                        intro h
                        have hBad : r < 0 := by
                          rw [h]
                          decide
                        exact hTailNeg (by simpa [r] using hBad)
                      have hParentIdx :
                          native_str_indexof (c :: cs) (p :: ps) 0 =
                            r + 1 := by
                        rw [hConsIdx]
                        simp [r, hTailNe]
                      have hParentNotNeg :
                          ¬ native_str_indexof (c :: cs) (p :: ps) 0 < 0 := by
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        intro hlt
                        have hR1Nonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        exact (Int.not_lt_of_ge hR1Nonneg)
                          (by simpa [hParentIdx] using hlt)
                      have hParentToNat :
                          Int.toNat
                              (native_str_indexof (c :: cs) (p :: ps) 0) =
                            n + 1 := by
                        rw [hParentIdx]
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        have hNonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        apply Int.ofNat.inj
                        calc
                          Int.ofNat (Int.toNat (r + 1)) = r + 1 :=
                            Int.toNat_of_nonneg hNonneg
                          _ = Int.ofNat (n + 1) := by
                            rw [← hRcast]
                            simp
                      cases fuel' with
                      | zero =>
                          omega
                      | succ fuel'' =>
                          have hPatLenPos : 0 < (p :: ps).length := by
                            simp
                          have hSuffixLen :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                cs.length := by
                            simp [List.length_drop]
                            omega
                          have hSuffixFuelParent :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' + 1 := by
                            omega
                          have hSuffixFuelTail :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' := by
                            simp at hCsFuel
                            omega
                          have hParentSuffix :
                              EvaluateProofInternal.native_str_replace_all_eval_aux (fuel'' + 1)
                                  (p :: ps) repl
                                  (cs.drop (n + (p :: ps).length)) =
                                EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                  (cs.drop (n + (p :: ps).length)) :=
                            ih (fuel'' + 1) (by omega)
                              (cs.drop (n + (p :: ps).length))
                              hSuffixFuelParent (by simp)
                          have hTailSuffix :
                              EvaluateProofInternal.native_str_replace_all_eval_aux fuel''
                                  (p :: ps) repl
                                  (cs.drop (n + (p :: ps).length)) =
                                EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                  (cs.drop (n + (p :: ps).length)) :=
                            ih fuel'' (by omega)
                              (cs.drop (n + (p :: ps).length))
                              hSuffixFuelTail (by simp)
                          have hTailChain :
                              EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs =
                                cs.take n ++ repl ++
                                  EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                    (cs.drop (n + (p :: ps).length)) := by
                            rw [← ih (fuel'' + 1) (by omega) cs hCsFuel
                              (by simp)]
                            simp [EvaluateProofInternal.native_str_replace_all_eval_aux, r, n,
                              hTailNeg]
                            simpa [r, n] using hTailSuffix
                          have hR1NotNeg : ¬ r + 1 < 0 := by
                            have hrNonneg : 0 ≤ r := by
                              rw [← hRcast]
                              exact Int.natCast_nonneg n
                            exact Int.not_lt_of_ge
                              (Int.add_nonneg hrNonneg (by decide))
                          have hToNatR1 : Int.toNat (r + 1) = n + 1 := by
                            simpa [hParentIdx] using hParentToNat
                          have hParentDrop :
                              (c :: cs).drop
                                  (n + 1 + (p :: ps).length) =
                                cs.drop (n + (p :: ps).length) := by
                            rw [show n + 1 + (p :: ps).length =
                                (n + (p :: ps).length) + 1 by omega]
                            simp
                          change
                            (let idx :=
                              native_str_indexof (c :: cs) (p :: ps) 0
                             if idx < 0 then
                               c :: cs
                             else
                               (c :: cs).take (Int.toNat idx) ++ repl ++
                                 EvaluateProofInternal.native_str_replace_all_eval_aux
                                   (fuel'' + 1) (p :: ps) repl
                                   ((c :: cs).drop
                                     (Int.toNat idx + (p :: ps).length))) =
                              EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                (c :: cs)
                          rw [hParentIdx]
                          rw [ite_eq_right hR1NotNeg]
                          rw [hToNatR1]
                          rw [hParentDrop]
                          rw [hParentSuffix]
                          simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse,
                            hTailChain, List.append_assoc]

theorem EvaluateProofInternal.native_str_replace_all_eval_result_cons_eq_chain
    (s repl : native_String) (p : native_Char) (ps : native_String) :
    EvaluateProofInternal.native_str_replace_all_eval_result s (p :: ps) repl =
      EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 s := by
  unfold EvaluateProofInternal.native_str_replace_all_eval_result
  exact EvaluateProofInternal.native_str_replace_all_eval_aux_eq_chain_of_fuel (p :: ps) repl
    (s.length + 1) s (by omega) (by simp)

theorem EvaluateProofInternal.native_re_replace_all_nonempty_list_aux_map_char
    (p : native_Char) (ps repl : native_String) :
    ∀ (fuel : Nat) (s : native_String),
      s.length < fuel →
      impl_native_re_replace_all_nonempty_list_aux fuel
          (native_str_to_re ((p :: ps).map SmtValue.Char))
          (repl.map SmtValue.Char) (s.map SmtValue.Char) =
        (EvaluateProofInternal.native_str_replace_all_chain
          (p :: ps) repl 0 s).map SmtValue.Char := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hFuel
      omega
  | succ fuel ih =>
      intro s hFuel
      cases s with
      | nil =>
          simp [impl_native_re_replace_all_nonempty_list_aux,
            native_re_positive_prefix_match_len?,
            EvaluateProofInternal.native_str_replace_all_chain]
      | cons c cs =>
          simp only [List.map_cons]
          rw [impl_native_re_replace_all_nonempty_list_aux.eq_3]
          rw [StrReplaceAllSupport.positive_prefix_str_to_re_cons]
          rw [show
              native_seq_prefix_eq
                  (SmtValue.Char p :: ps.map SmtValue.Char)
                  (SmtValue.Char c :: cs.map SmtValue.Char) =
                native_string_prefix_eq (p :: ps) (c :: cs) by
            simpa only [List.map_cons] using
              EvaluateProofInternal.native_seq_prefix_eq_map_char
                (p :: ps) (c :: cs)]
          by_cases hPrefix :
              native_string_prefix_eq (p :: ps) (c :: cs) = true
          · rw [ite_eq_left hPrefix]
            simp only [List.length_cons, List.length_map]
            have hPatLe : (p :: ps).length ≤ (c :: cs).length :=
              EvaluateProofInternal.native_string_prefix_eq_length_le
                (p :: ps) (c :: cs) hPrefix
            have hDropFuel :
                ((c :: cs).drop (ps.length + 1)).length < fuel := by
              rw [List.length_drop]
              simp only [List.length_cons] at hFuel hPatLe ⊢
              omega
            rw [show
                (SmtValue.Char c :: cs.map SmtValue.Char).drop (ps.length + 1) =
                  ((c :: cs).drop (ps.length + 1)).map SmtValue.Char by
              simp [List.map_drop]]
            have hRec := ih ((c :: cs).drop (ps.length + 1)) hDropFuel
            simp only [List.map_cons] at hRec
            rw [hRec]
            simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefix,
              EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop,
              List.map_append]
          · rw [ite_eq_right hPrefix]
            simp only [List.length_cons, List.length_map]
            have hCsFuel : cs.length < fuel := by
              simp only [List.length_cons] at hFuel
              omega
            have hRec := ih cs hCsFuel
            simp only [List.map_cons] at hRec
            rw [hRec]
            simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefix]

theorem EvaluateProofInternal.native_seq_replace_all_pack_string
    (s pat repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_replace_all
          (native_unpack_seq (native_pack_string s))
          (native_unpack_seq (native_pack_string pat))
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string
        (EvaluateProofInternal.native_str_replace_all_eval_result s pat repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string pat) =
      pat.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  cases pat with
  | nil =>
      simp only [List.map_nil]
      rw [StrReplaceAllSupport.replace_all_nil_pat]
      rw [EvaluateProofInternal.native_str_replace_all_eval_result_nil]
      simp [Smtm.native_pack_string]
  | cons p ps =>
      unfold native_seq_replace_all native_str_replace_re_all
        impl_native_re_replace_all_nonempty_list
      change native_pack_seq SmtType.Char
          (impl_native_re_replace_all_nonempty_list_aux
            ((s.map SmtValue.Char).length + 1)
            (native_str_to_re ((p :: ps).map SmtValue.Char))
            (repl.map SmtValue.Char) (s.map SmtValue.Char)) = _
      rw [show (s.map SmtValue.Char).length + 1 = s.length + 1 by simp]
      rw [EvaluateProofInternal.native_re_replace_all_nonempty_list_aux_map_char
        p ps repl (s.length + 1) s (by omega)]
      rw [EvaluateProofInternal.native_str_replace_all_eval_result_cons_eq_chain]
      simp [Smtm.native_pack_string]

theorem EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string
    (s pat repl : native_String) :
    __smtx_model_eval_str_replace_all
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string pat))
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq
        (native_pack_string
          (EvaluateProofInternal.native_str_replace_all_eval_result s pat repl)) := by
  simp only [__smtx_model_eval_str_replace_all]
  rw [show __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char by
    simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
  rw [EvaluateProofInternal.native_seq_replace_all_pack_string]

theorem EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string_nil
    (s repl : native_String) :
    __smtx_model_eval_str_replace_all
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string []))
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq (native_pack_string s) := by
  rw [EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string]
  rw [EvaluateProofInternal.native_str_replace_all_eval_result_nil]

