module

public import Cpc.Proofs.TypePreservation.Common
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

namespace Smtm

/-- Inductive predicate describing the SMT terms covered by the type-preservation proof. -/
inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : native_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : native_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : native_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | string (s : native_String) : supported_preservation_term (SmtTerm.String s)
  | binary (w n : native_Int) : supported_preservation_term (SmtTerm.Binary w n)
  | purify {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm._at_purify t)
  | var (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.UConst s T)
  | re_allchar : supported_preservation_term SmtTerm.re_allchar
  | re_none : supported_preservation_term SmtTerm.re_none
  | re_all : supported_preservation_term SmtTerm.re_all
  | seq_empty (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.seq_empty T)
  | set_empty (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.set_empty T)
  | seq_unit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.seq_unit t)
  | set_singleton {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.set_singleton t)
  | seq_nth {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (hT :
        type_inhabited (__smtx_typeof (SmtTerm.seq_nth t1 t2)))
      (hElemRec :
        ∀ {T : SmtType},
          __smtx_typeof t1 = SmtType.Seq T ->
            __smtx_type_wf_rec T = true) :
      supported_preservation_term (SmtTerm.seq_nth t1 t2)
  | set_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.set_union t1 t2)
  | set_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.set_inter t1 t2)
  | set_minus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.set_minus t1 t2)
  | set_member {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.set_member t1 t2)
  | set_subset {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.set_subset t1 t2)
  | select {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.select t1 t2)
  | store {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.store t1 t2 t3)
  | map_diff {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (hDefault :
        ∀ {A : SmtType},
          __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
            __smtx_typeof_value (__smtx_type_default A) = A ∧
              value_canonical (__smtx_type_default A)) :
      supported_preservation_term
        (SmtTerm.map_diff t1 t2)
  | seq_diff {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term
        (SmtTerm.seq_diff t1 t2)
  | ite {c t1 t2 : SmtTerm}
      (htc : term_has_non_none_type c)
      (hsc : supported_preservation_term c)
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term
        (SmtTerm.ite c t1 t2)
  | exists (s : native_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.exists s T body)
  | forall (s : native_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.forall s T body)
  | choice (s : native_String) (T : SmtType) (body : SmtTerm)
      (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
      supported_preservation_term (SmtTerm.choice s T body)
  | bind (s : native_String) (T : SmtType) (x1 x2 : SmtTerm)
      (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2))
      (hs1 : supported_preservation_term x1)
      (hs2 : supported_preservation_term x2) :
      supported_preservation_term (SmtTerm.bind s T x1 x2)
  | not {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.not t)
  | or {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.or t1 t2)
  | and {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.and t1 t2)
  | imp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.imp t1 t2)
  | eq (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.eq t1 t2)
  | xor (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.xor t1 t2)
  | plus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.plus t1 t2)
  | arith_neg {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.neg t1 t2)
  | mult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.mult t1 t2)
  | lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.lt t1 t2)
  | leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.leq t1 t2)
  | gt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.gt t1 t2)
  | geq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.geq t1 t2)
  | to_real {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.to_real t)
  | to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.to_int t)
  | is_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.is_int t)
  | abs {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.abs t)
  | uneg {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.uneg t)
  | div {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.div t1 t2)
  | mod {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.mod t1 t2)
  | divisible {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.divisible t1 t2)
  | int_pow2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.int_pow2 t)
  | int_log2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.int_log2 t)
  | div_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.div_total t1 t2)
  | mod_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.mod_total t1 t2)
  | qdiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.qdiv t1 t2)
  | qdiv_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.qdiv_total t1 t2)
  | str_len {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_len t)
  | str_to_lower {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_to_lower t)
  | str_to_upper {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_to_upper t)
  | str_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_concat t1 t2)
  | str_substr {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_substr t1 t2 t3)
  | str_contains {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_contains t1 t2)
  | str_indexof {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_indexof t1 t2 t3)
  | str_at {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_at t1 t2)
  | str_replace {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_replace t1 t2 t3)
  | str_rev {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_rev t)
  | str_update {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_update t1 t2 t3)
  | str_replace_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_replace_all t1 t2 t3)
  | str_replace_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_replace_re t1 t2 t3)
  | str_replace_re_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_replace_re_all t1 t2 t3)
  | str_indexof_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_indexof_re t1 t2 t3)
  | _at_strings_occur_index {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm._at_strings_occur_index t1 t2 t3)
  | _at_strings_occur_index_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm._at_strings_occur_index_re t1 t2 t3)
  | str_indexof_re_split {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.str_indexof_re_split t1 t2 t3)
  | str_to_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_to_code t)
  | str_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_to_int t)
  | str_from_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_from_code t)
  | str_from_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_from_int t)
  | str_to_re {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_to_re t)
  | re_mult {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.re_mult t)
  | re_plus {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.re_plus t)
  | re_exp (n : native_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.re_exp (SmtTerm.Numeral n) t)
  | re_opt {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.re_opt t)
  | re_comp {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.re_comp t)
  | re_range {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.re_range t1 t2)
  | re_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.re_concat t1 t2)
  | re_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.re_inter t1 t2)
  | re_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.re_union t1 t2)
  | re_diff {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.re_diff t1 t2)
  | re_loop (n1 n2 : native_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)
  | str_in_re {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_in_re t1 t2)
  | str_lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_lt t1 t2)
  | str_leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_leq t1 t2)
  | str_prefixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_prefixof t1 t2)
  | str_suffixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.str_suffixof t1 t2)
  | str_is_digit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.str_is_digit t)
  | bv_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.concat t1 t2)
  | extract {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.extract t1 t2 t3)
  | bvnot {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.bvnot t)
  | bvand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvand t1 t2)
  | bvor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvor t1 t2)
  | bvnand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvnand t1 t2)
  | bvnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvnor t1 t2)
  | bvxor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvxor t1 t2)
  | bvxnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvxnor t1 t2)
  | bvcomp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvcomp t1 t2)
  | bvneg {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.bvneg t)
  | bvadd {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvadd t1 t2)
  | bvmul {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvmul t1 t2)
  | bvudiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvudiv t1 t2)
  | bvurem {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvurem t1 t2)
  | bvsub {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsub t1 t2)
  | bvult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvult t1 t2)
  | bvule {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvule t1 t2)
  | bvugt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvugt t1 t2)
  | bvuge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvuge t1 t2)
  | bvslt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvslt t1 t2)
  | bvsle {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsle t1 t2)
  | bvsgt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsgt t1 t2)
  | bvsge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsge t1 t2)
  | bvshl {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvshl t1 t2)
  | bvlshr {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvlshr t1 t2)
  | repeat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.repeat t1 t2)
  | bvsdiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsdiv t1 t2)
  | bvsrem {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsrem t1 t2)
  | bvsmod {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsmod t1 t2)
  | bvashr {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvashr t1 t2)
  | rotate_left {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.rotate_left t1 t2)
  | rotate_right {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.rotate_right t1 t2)
  | bvuaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvuaddo t1 t2)
  | bvnego {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.bvnego t)
  | bvsaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsaddo t1 t2)
  | bvumulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvumulo t1 t2)
  | bvsmulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsmulo t1 t2)
  | bvusubo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvusubo t1 t2)
  | bvssubo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvssubo t1 t2)
  | bvsdivo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.bvsdivo t1 t2)
  | zero_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.zero_extend t1 t2)
  | sign_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.sign_extend t1 t2)
  | int_to_bv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.int_to_bv t1 t2)
  | ubv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.ubv_to_int t)
  | sbv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.sbv_to_int t)
  | dt_cons (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
      supported_preservation_term (SmtTerm.DtCons s d i)
  | dt_sel {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat} {x : SmtTerm}
      (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
      (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
      (hWrongMapWF :
        __smtx_type_wf
          (SmtType.Map SmtType.Int
            (SmtType.Map SmtType.Int
              (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)
  | dt_tester (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) (x : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtTester s d i) x)
  | apply {f x : SmtTerm}
      (hTy : generic_apply_type f x)
      (hEval : generic_apply_eval f x)
      (htf : term_has_non_none_type f)
      (hsf : supported_preservation_term f)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply f x)

/-- Extracts inhabitation of the declared variable type from a non-`None` typing judgment. -/
theorem var_type_inhabited_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    type_inhabited T := by
  have hGuard : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  exact smtx_typeof_guard_wf_inhabited_of_non_none T T hGuard

/-- Extracts inhabitation of the declared uninterpreted-constant type from a non-`None` typing judgment. -/
theorem uconst_type_inhabited_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    type_inhabited T := by
  have hGuard : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  exact smtx_typeof_guard_wf_inhabited_of_non_none T T hGuard

/-- Extracts inhabitation of the element type of `seq_empty` from a non-`None` typing judgment. -/
theorem seq_empty_type_inhabited_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    type_inhabited T := by
  have hGuard : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hSeqWF :
      __smtx_type_wf (SmtType.Seq T) = true :=
    smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuard
  exact type_inhabited_of_type_wf T (seq_type_wf_component_of_wf hSeqWF)

/-- Extracts inhabitation of the element type of `set_empty` from a non-`None` typing judgment. -/
theorem set_empty_type_inhabited_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    type_inhabited T := by
  have hGuard : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hSetWF :
      __smtx_type_wf (SmtType.Set T) = true :=
    smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuard
  exact type_inhabited_of_type_wf T (set_type_wf_component_of_wf hSetWF)

/-- Builds support for variables directly from a non-`None` typing judgment. -/
theorem supported_var_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    supported_preservation_term (SmtTerm.Var s T) :=
  supported_preservation_term.var s T (var_type_inhabited_of_non_none ht)

/-- Builds support for uninterpreted constants directly from a non-`None` typing judgment. -/
theorem supported_uconst_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    supported_preservation_term (SmtTerm.UConst s T) :=
  supported_preservation_term.uconst s T (uconst_type_inhabited_of_non_none ht)

/-- Builds support for `seq_empty` directly from a non-`None` typing judgment. -/
theorem supported_seq_empty_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    supported_preservation_term (SmtTerm.seq_empty T) :=
  supported_preservation_term.seq_empty T (seq_empty_type_inhabited_of_non_none ht)

/-- Builds support for `set_empty` directly from a non-`None` typing judgment. -/
theorem supported_set_empty_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    supported_preservation_term (SmtTerm.set_empty T) :=
  supported_preservation_term.set_empty T (set_empty_type_inhabited_of_non_none ht)

/-- Builds support for `choice` directly from a non-`None` typing judgment. -/
theorem supported_choice_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    supported_preservation_term (SmtTerm.choice s T body) :=
  supported_preservation_term.choice s T body ht

/-- Builds support for `bind` directly from a non-`None` typing judgment. -/
theorem supported_bind_of_non_none
    {s : native_String}
    {T : SmtType}
    {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2))
    (hs1 : supported_preservation_term x1)
    (hs2 : supported_preservation_term x2) :
    supported_preservation_term (SmtTerm.bind s T x1 x2) :=
  supported_preservation_term.bind s T x1 x2 ht hs1 hs2

/-- Computes generic application typing for application heads that are not datatype selectors or testers. -/
theorem generic_apply_type_of_non_datatype_head
    {f x : SmtTerm}
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;>
    first
    | exact absurd rfl (hSel _ _ _ _)
    | exact absurd rfl (hTester _ _ _)
    | simp [__smtx_typeof]

/-- Computes generic application evaluation for application heads that are not datatype selectors or testers. -/
theorem generic_apply_eval_of_non_datatype_head
    {f x : SmtTerm}
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_eval f x := by
  unfold generic_apply_eval
  intro M
  cases f <;>
    first
    | exact absurd rfl (hSel _ _ _ _)
    | exact absurd rfl (hTester _ _ _)
    | simp [__smtx_model_eval]

/-- Builds support for generic applications whose heads are not datatype selectors or testers. -/
theorem supported_apply_of_non_datatype_head
    {f x : SmtTerm}
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (htf : term_has_non_none_type f)
    (hsf : supported_preservation_term f)
    (htx : term_has_non_none_type x)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) :=
  supported_preservation_term.apply
    (generic_apply_type_of_non_datatype_head hSel hTester)
    (generic_apply_eval_of_non_datatype_head hSel hTester)
    htf hsf htx hsx

end Smtm
