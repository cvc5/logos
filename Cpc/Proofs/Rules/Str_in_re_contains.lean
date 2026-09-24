module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrInReContainsProof

private abbrev sigmaStar : Term :=
  Term.Apply Term.re_mult Term.re_allchar

private abbrev containsRegex (s : Term) : Term :=
  Term.Apply (Term.Apply Term.re_concat sigmaStar)
    (Term.Apply
      (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s))
      (Term.Apply (Term.Apply Term.re_concat sigmaStar)
        (Term.Apply Term.str_to_re (Term.String []))))

private abbrev lhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_in_re t) (containsRegex s)

private abbrev rhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains t) s

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

private theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  cases A with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
                cases B with
                | UOp opb =>
                    cases opb <;> simp [__eo_typeof_str_in_re] at h ⊢
                | _ => simp [__eo_typeof_str_in_re] at h
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  have hsimpa := hTyRaw
  try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
  exact hsimpa

private theorem smtx_typeof_re_allchar :
    __smtx_typeof SmtTerm.re_allchar = SmtType.RegLan := by
  simp [__smtx_typeof]

private theorem smtx_typeof_sigma_star :
    __smtx_typeof (__eo_to_smt sigmaStar) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_mult SmtTerm.re_allchar) = SmtType.RegLan
  rw [typeof_re_mult_eq]
  simp [smtx_typeof_re_allchar, native_ite, native_Teq]

private theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re s)) =
      SmtType.RegLan := by
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSSmtTy, native_ite, native_Teq]

private theorem smtx_typeof_empty_str_to_re :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re (Term.String []))) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) = SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [__smtx_typeof.eq_4, native_string_valid, native_ite, native_Teq]

private theorem smtx_typeof_contains_regex
    (s : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt (containsRegex s)) = SmtType.RegLan := by
  have hStarTy := smtx_typeof_sigma_star
  have hPatTy := smtx_typeof_str_to_re_of_seq_char s hSTrans hSTy
  have hEpsTy := smtx_typeof_empty_str_to_re
  have hTailTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat sigmaStar)
              (Term.Apply Term.str_to_re (Term.String [])))) =
        SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_concat (__eo_to_smt sigmaStar)
          (__eo_to_smt (Term.Apply Term.str_to_re (Term.String [])))) =
      SmtType.RegLan
    -- rewrite the component types before `simp` normalises
    -- `__eo_to_smt (Apply ..)` past their left-hand sides
    rw [typeof_re_concat_eq, hStarTy, hEpsTy]
    simp [native_ite, native_Teq]
  have hRestTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s))
              (Term.Apply (Term.Apply Term.re_concat sigmaStar)
                (Term.Apply Term.str_to_re (Term.String []))))) =
        SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_concat (__eo_to_smt (Term.Apply Term.str_to_re s))
          (__eo_to_smt
            (Term.Apply (Term.Apply Term.re_concat sigmaStar)
              (Term.Apply Term.str_to_re (Term.String []))))) =
      SmtType.RegLan
    rw [typeof_re_concat_eq, hPatTy, hTailTy]
    simp [native_ite, native_Teq]
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt sigmaStar)
        (__eo_to_smt
          (Term.Apply
            (Term.Apply Term.re_concat (Term.Apply Term.str_to_re s))
            (Term.Apply (Term.Apply Term.re_concat sigmaStar)
              (Term.Apply Term.str_to_re (Term.String [])))))) =
    SmtType.RegLan
  rw [typeof_re_concat_eq, hStarTy, hRestTy]
  simp [native_ite, native_Teq]

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [impl_native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

private theorem unpack_seq_eq_map_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_unpack_seq ss = (native_unpack_string ss).map SmtValue.Char := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  unfold native_unpack_string
  simp only [List.map_map]
  exact hMap.symm

private theorem nativeListInRe_char_self
    (c : native_Char) (hc : native_char_valid c = true) :
    RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [RuleProofs.nativeListInRe, native_re_deriv, native_re_nullable, hc]

private theorem nativeListInRe_re_of_list_self :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        RuleProofs.nativeListInRe pat (impl_native_re_of_list pat) = true
  | [], _ => by
      simp [impl_native_re_of_list, RuleProofs.nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases RuleProofs.native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : RuleProofs.nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self c hc
      have hTail : RuleProofs.nativeListInRe cs (impl_native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self cs hcs
      have hConcat :
          RuleProofs.nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (impl_native_re_of_list cs)) = true :=
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (c :: cs) (SmtRegLan.char c) (impl_native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [impl_native_re_of_list] using hConcat

private theorem native_str_in_re_str_to_re_self
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    RuleProofs.native_str_in_re pat (native_str_to_re pat) = true := by
  simpa [RuleProofs.native_str_in_re, hValid, native_str_to_re,
    RuleProofs.nativeListInRe] using
    nativeListInRe_re_of_list_self pat hValid

private theorem native_seq_prefix_eq_append_local (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

private theorem native_seq_indexof_rec_append_ne_neg_local
    (pat after : List SmtValue) :
    ∀ (before : List SmtValue) (i fuel : Nat),
      before.length < fuel →
      native_seq_indexof_rec (before ++ pat ++ after) pat i fuel ≠ -1 := by
  intro before
  induction before with
  | nil =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append_local pat after)]
          simp
  | cons b bs ih =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          have hbs : bs.length < f := by
            simp only [List.length_cons] at hFuel
            omega
          unfold native_seq_indexof_rec
          by_cases hPre :
              native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]
            simp
          · rw [if_neg hPre]
            have hxs :
                (b :: bs) ++ pat ++ after = b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

private theorem native_seq_contains_of_decomp_local
    (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  exact StrContainsReplCharSupport.native_seq_contains_of_decomp
    before pat after

private theorem native_seq_contains_decomp_exists_local
    (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

private theorem native_seq_contains_iff_decomp_local (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔ ∃ before after, xs = before ++ pat ++ after := by
  exact StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat

private theorem native_seq_contains_map_char_iff
    (xs pat : native_String) :
    native_seq_contains (xs.map SmtValue.Char) (pat.map SmtValue.Char) = true ↔
      ∃ before after, xs = before ++ pat ++ after := by
  constructor
  · intro h
    rcases (native_seq_contains_iff_decomp_local
      (xs.map SmtValue.Char) (pat.map SmtValue.Char)).1 h with
      ⟨before, after, hEq⟩
    refine ⟨before.map impl_native_ssm_char_of_value,
      after.map impl_native_ssm_char_of_value, ?_⟩
    have hMap := congrArg (List.map impl_native_ssm_char_of_value) hEq
    simpa [List.map_append, List.map_map, Function.comp_def,
      impl_native_ssm_char_of_value, List.append_assoc] using hMap
  · rintro ⟨before, after, rfl⟩
    simpa [List.map_append, List.append_assoc] using
      native_seq_contains_of_decomp_local
        (before.map SmtValue.Char) (pat.map SmtValue.Char)
        (after.map SmtValue.Char)

private theorem native_str_in_re_contains_regex_eq
    (xs pat : native_String)
    (hXsValid : native_string_valid xs = true)
    (hPatValid : native_string_valid pat = true) :
    RuleProofs.native_str_in_re xs
        (native_re_concat native_re_all
          (native_re_concat (native_str_to_re pat)
            (native_re_concat native_re_all (native_str_to_re [])))) =
      native_seq_contains (xs.map SmtValue.Char) (pat.map SmtValue.Char) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    have hList :
        RuleProofs.nativeListInRe xs
            (native_re_concat native_re_all
              (native_re_concat (native_str_to_re pat)
                (native_re_concat native_re_all (native_str_to_re [])))) = true := by
      simpa [RuleProofs.native_str_in_re, hXsValid] using hMem
    have hOuter :
        RuleProofs.nativeListInRe xs
            (native_re_mk_concat native_re_all
              (native_re_concat (native_str_to_re pat)
                (native_re_concat native_re_all (native_str_to_re [])))) = true := by
      have hsimpa := hList
      try simp [native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs
        native_re_all
        (native_re_concat (native_str_to_re pat)
          (native_re_concat native_re_all (native_str_to_re [])))).1 hOuter with
      ⟨pre, rest, hXs, _hPreMem, hRestMem⟩
    have hXsSplitValid : native_string_valid (pre ++ rest) = true := by
      simpa [hXs] using hXsValid
    have hRestValid : native_string_valid rest = true :=
      RuleProofs.native_string_valid_append_right pre rest hXsSplitValid
    have hRestConcat :
        RuleProofs.nativeListInRe rest
            (native_re_mk_concat (native_str_to_re pat)
              (native_re_concat native_re_all (native_str_to_re []))) = true := by
      have hsimpa := hRestMem
      try simp [native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append rest
        (native_str_to_re pat)
        (native_re_concat native_re_all (native_str_to_re []))).1
        hRestConcat with
      ⟨mid, tail, hRest, hMidMem, hTailMem⟩
    have hRestSplitValid : native_string_valid (mid ++ tail) = true := by
      simpa [hRest] using hRestValid
    have hMidValid : native_string_valid mid = true :=
      RuleProofs.native_string_valid_append_left mid tail hRestSplitValid
    have hTailValid : native_string_valid tail = true :=
      RuleProofs.native_string_valid_append_right mid tail hRestSplitValid
    have hMidStrMem :
        RuleProofs.native_str_in_re mid (native_str_to_re pat) = true := by
      simpa [RuleProofs.native_str_in_re, hMidValid, native_str_to_re] using
        hMidMem
    have hMidEq : mid = pat :=
      RuleProofs.native_str_in_re_str_to_re_eq hMidValid hMidStrMem
    have hTailConcat :
        RuleProofs.nativeListInRe tail
            (native_re_mk_concat native_re_all (native_str_to_re [])) = true := by
      have hsimpa := hTailMem
      try simp [native_re_concat] at hsimpa ⊢
      exact hsimpa
    rcases (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append tail
        native_re_all (native_str_to_re [])).1 hTailConcat with
      ⟨post, eps, hTail, _hPostMem, hEpsMem⟩
    have hTailSplitValid : native_string_valid (post ++ eps) = true := by
      simpa [hTail] using hTailValid
    have hEpsValid : native_string_valid eps = true :=
      RuleProofs.native_string_valid_append_right post eps hTailSplitValid
    have hEpsStrMem :
        RuleProofs.native_str_in_re eps (native_str_to_re []) = true := by
      simpa [RuleProofs.native_str_in_re, hEpsValid, native_str_to_re] using
        hEpsMem
    have hEpsEq : eps = [] :=
      RuleProofs.native_str_in_re_str_to_re_eq hEpsValid hEpsStrMem
    rw [native_seq_contains_map_char_iff]
    refine ⟨pre, post, ?_⟩
    rw [← hXs, ← hRest, ← hTail, hMidEq, hEpsEq]
    simp [List.append_assoc]
  · intro hContains
    rw [native_seq_contains_map_char_iff] at hContains
    rcases hContains with ⟨pre, post, hXs⟩
    have hAllValid : native_string_valid (pre ++ pat ++ post) = true := by
      simpa [hXs] using hXsValid
    have hPreValid : native_string_valid pre = true :=
      RuleProofs.native_string_valid_append_left pre (pat ++ post) (by
        simpa [List.append_assoc] using hAllValid)
    have hPatPostValid : native_string_valid (pat ++ post) = true :=
      RuleProofs.native_string_valid_append_right pre (pat ++ post) (by
        simpa [List.append_assoc] using hAllValid)
    have hPostValid : native_string_valid post = true :=
      RuleProofs.native_string_valid_append_right pat post hPatPostValid
    have hPreMem : RuleProofs.native_str_in_re pre native_re_all = true :=
      RuleProofs.native_str_in_re_re_all pre hPreValid
    have hPatMem :
        RuleProofs.native_str_in_re pat (native_str_to_re pat) = true :=
      native_str_in_re_str_to_re_self pat hPatValid
    have hPostMem : RuleProofs.native_str_in_re post native_re_all = true :=
      RuleProofs.native_str_in_re_re_all post hPostValid
    have hEmptyMem :
        RuleProofs.native_str_in_re ([] : native_String) (native_str_to_re []) =
          true :=
      native_str_in_re_str_to_re_self [] (by simp [native_string_valid])
    have hPostEpsMem :
        RuleProofs.native_str_in_re (post ++ ([] : native_String))
          (native_re_concat native_re_all (native_str_to_re [])) = true :=
      RuleProofs.native_str_in_re_re_concat_intro post []
        native_re_all (native_str_to_re []) hPostMem hEmptyMem
    have hPatTailMem :
        RuleProofs.native_str_in_re (pat ++ (post ++ ([] : native_String)))
          (native_re_concat (native_str_to_re pat)
            (native_re_concat native_re_all (native_str_to_re []))) = true :=
      RuleProofs.native_str_in_re_re_concat_intro pat (post ++ [])
        (native_str_to_re pat)
        (native_re_concat native_re_all (native_str_to_re []))
        hPatMem hPostEpsMem
    have hFull :
        RuleProofs.native_str_in_re
          (pre ++ (pat ++ (post ++ ([] : native_String))))
          (native_re_concat native_re_all
            (native_re_concat (native_str_to_re pat)
              (native_re_concat native_re_all (native_str_to_re [])))) = true :=
      RuleProofs.native_str_in_re_re_concat_intro pre (pat ++ (post ++ []))
        native_re_all
        (native_re_concat (native_str_to_re pat)
          (native_re_concat native_re_all (native_str_to_re [])))
        hPreMem hPatTailMem
    simpa [hXs, List.append_assoc] using hFull

private theorem typed___eo_prog_str_in_re_contains_impl
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_in_re_contains t s) := by
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hRegexTy := smtx_typeof_contains_regex s hSTrans hSTy
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs t s)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt t) (__eo_to_smt (containsRegex s))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq, hTSmtTy, hRegexTy]
    simp [native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs t s)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hTSmtTy, hSSmtTy, __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs t s)) (rhs t s)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs t s) (rhs t s)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hTNotStuck : t ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hTTy
  have hSNotStuck : s ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hSTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hSTy
  have hProg :
      __eo_prog_str_in_re_contains t s =
        Term.Apply (Term.Apply Term.eq (lhs t s)) (rhs t s) := by
    cases hT : t <;>
      first | exact False.elim (hTNotStuck hT) | all_goals
        cases hS : s <;>
          first | exact False.elim (hSNotStuck hS) | rfl
  rw [hProg]
  exact hBoolEq

private theorem smtx_model_eval_contains_regex
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    __smtx_model_eval M (__eo_to_smt (containsRegex s)) =
      SmtValue.RegLan
        (native_re_concat native_re_all
          (native_re_concat (native_str_to_re (native_unpack_string ss))
            (native_re_concat native_re_all (native_str_to_re [])))) := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (SmtTerm.re_mult SmtTerm.re_allchar)
        (SmtTerm.re_concat (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_concat (SmtTerm.re_mult SmtTerm.re_allchar)
            (SmtTerm.str_to_re (SmtTerm.String []))))) =
    SmtValue.RegLan
      (native_re_concat native_re_all
        (native_re_concat (native_str_to_re (native_unpack_string ss))
          (native_re_concat native_re_all (native_str_to_re []))))
  simp [__smtx_model_eval, hSEval, __smtx_model_eval_re_mult,
    __smtx_model_eval_re_concat, __smtx_model_eval_str_to_re,
    native_re_mult, native_re_allchar, native_re_all, native_re_mk_star,
    native_pack_string, native_pack_seq, native_unpack_string, native_unpack_seq]
  rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy]
  simp [impl_native_string_to_values, impl_native_ssm_char_of_value, Function.comp_def]

private theorem facts___eo_prog_str_in_re_contains_impl
    (M : SmtModel) (hM : model_wf M) (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_str_in_re_contains t s) true := by
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hStTy : __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char := by
    simpa [hTEval, __smtx_typeof_value] using hTEvalTy
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hSEval, __smtx_typeof_value] using hSEvalTy
  have hStValid : native_string_valid (native_unpack_string st) = true :=
    native_unpack_string_valid_of_typeof_seq_char hStTy
  have hSsValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSsTy
  have hStUnpack :
      native_unpack_seq st =
        (native_unpack_string st).map SmtValue.Char :=
    unpack_seq_eq_map_unpack_string_of_typeof_seq_char st hStTy
  have hSsUnpack :
      native_unpack_seq ss =
        (native_unpack_string ss).map SmtValue.Char :=
    unpack_seq_eq_map_unpack_string_of_typeof_seq_char ss hSsTy
  have hRegexEval := smtx_model_eval_contains_regex M s ss hSEval hSsTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs t s)) (rhs t s)) := by
    have hTyped :=
      typed___eo_prog_str_in_re_contains_impl t s hTTrans hSTrans hTTy hSTy
    have hTNotStuck : t ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hTTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hTTy
    have hSNotStuck : s ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hSTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hSTy
    have hProg :
        __eo_prog_str_in_re_contains t s =
          Term.Apply (Term.Apply Term.eq (lhs t s)) (rhs t s) := by
      cases hT : t <;>
        first | exact False.elim (hTNotStuck hT) | all_goals
          cases hS : s <;>
            first | exact False.elim (hSNotStuck hS) | rfl
    rwa [hProg] at hTyped
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs t s)) =
        __smtx_model_eval M (__eo_to_smt (rhs t s)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt t) (__eo_to_smt (containsRegex s))) =
      __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s))
    simp [__smtx_model_eval]
    change __smtx_model_eval_str_in_re
        (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt (containsRegex s))) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt s))
    rw [hTEval, hSEval, hRegexEval]
    change
      SmtValue.Boolean
          (Smtm.native_str_in_re (native_unpack_seq st)
            (native_re_concat native_re_all
              (native_re_concat (native_str_to_re (native_unpack_string ss))
                (native_re_concat native_re_all (native_str_to_re []))))) =
        SmtValue.Boolean
          (native_seq_contains (native_unpack_seq st) (native_unpack_seq ss))
    rw [RuleProofs.model_str_in_re_unpack_eq_string st _ hStTy]
    rw [hStUnpack, hSsUnpack]
    rw [native_str_in_re_contains_regex_eq
      (native_unpack_string st) (native_unpack_string ss) hStValid hSsValid]
  have hTNotStuck : t ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hTTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hTTy
  have hSNotStuck : s ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hSTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hSTy
  have hProg :
      __eo_prog_str_in_re_contains t s =
        Term.Apply (Term.Apply Term.eq (lhs t s)) (rhs t s) := by
    cases hT : t <;>
      first | exact False.elim (hTNotStuck hT) | all_goals
        cases hS : s <;>
          first | exact False.elim (hSNotStuck hS) | rfl
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs t s) (rhs t s) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt (rhs t s)))

end StrInReContainsProof

public theorem cmd_step_str_in_re_contains_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_contains args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_contains args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_contains args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_in_re_contains
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply
                          (Term.Apply Term.eq
                            (StrInReContainsProof.lhs a1 a2))
                          (StrInReContainsProof.rhs a1 a2) := by
                    cases hA1 : a1 <;>
                      first | exact False.elim (hA1NotStuck hA1) | all_goals
                        cases hA2 : a2 <;>
                          first | exact False.elim (hA2NotStuck hA2) | rfl
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq
                      (__eo_typeof (StrInReContainsProof.lhs a1 a2))
                      (__eo_typeof (StrInReContainsProof.rhs a1 a2)) = Term.Bool
                    at hResultTy
                  have hOperands :=
                    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof (StrInReContainsProof.lhs a1 a2))
                      (__eo_typeof (StrInReContainsProof.rhs a1 a2))
                      hResultTy
                  have hLhsNotStuck :
                      __eo_typeof (StrInReContainsProof.lhs a1 a2) ≠
                        Term.Stuck :=
                    hOperands.1
                  have hRhsNotStuck :
                      __eo_typeof (StrInReContainsProof.rhs a1 a2) ≠
                        Term.Stuck :=
                    hOperands.2
                  have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof
                          (StrInReContainsProof.containsRegex a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    exact (StrInReContainsProof.eo_typeof_str_in_re_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof (StrInReContainsProof.containsRegex a2))
                      hLhsNotStuck).1
                  have hContainsArgs :
                      ∃ U, __eo_typeof a1 = Term.Apply Term.Seq U ∧
                        __eo_typeof a2 = Term.Apply Term.Seq U := by
                    change __eo_typeof_str_contains (__eo_typeof a1)
                        (__eo_typeof a2) ≠ Term.Stuck at hRhsNotStuck
                    exact StrInReContainsProof.eo_typeof_str_contains_args_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof a2) hRhsNotStuck
                  rcases hContainsArgs with ⟨U, hA1SeqU, hA2SeqU⟩
                  have hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                    have hSeqEq :
                        Term.Apply Term.Seq U = Term.Apply Term.Seq Term.Char := by
                      rw [← hA1SeqU, hA1Ty]
                    cases hSeqEq
                    exact hA2SeqU
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_in_re_contains a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (StrInReContainsProof.typed___eo_prog_str_in_re_contains_impl
                        a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact StrInReContainsProof.facts___eo_prog_str_in_re_contains_impl
                      M hM a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M []
                    (__eo_prog_str_in_re_contains a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
