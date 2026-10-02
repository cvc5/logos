module

public import Cpc.Logos
import all Cpc.Logos
public import Cpc.Proofs.ModelEval
import all Cpc.Proofs.ModelEval

public section

open Smtm in
/-- `native_Teq` is reflexive; lets `simp` discharge the reflexive residual left
when `native_inhabited_type` is unfolded on a concrete type. -/
@[simp] theorem native_Teq_self (x : SmtType) : native_Teq x x = true := by
  simp [native_Teq]

open Eo

namespace Term

/- Proof-only compatibility aliases for pre-`UserOp` `Term.<op>` references. -/
abbrev Int := Term.UOp UserOp.Int
abbrev Real := Term.UOp UserOp.Real
abbrev BitVec := Term.UOp UserOp.BitVec
abbrev Char := Term.UOp UserOp.Char
abbrev Seq := Term.UOp UserOp.Seq
abbrev _at__at_Pair := Term.UOp UserOp._at__at_Pair
abbrev _at__at_pair := Term.UOp UserOp._at__at_pair
abbrev _at__at_TypedList := Term.UOp UserOp._at__at_TypedList
abbrev _at__at_TypedList_nil := Term.UOp UserOp._at__at_TypedList_nil
abbrev _at__at_TypedList_cons := Term.UOp UserOp._at__at_TypedList_cons
abbrev ite := Term.UOp UserOp.ite
abbrev not := Term.UOp UserOp.not
abbrev or := Term.UOp UserOp.or
abbrev and := Term.UOp UserOp.and
abbrev imp := Term.UOp UserOp.imp
abbrev xor := Term.UOp UserOp.xor
abbrev eq := Term.UOp UserOp.eq
abbrev distinct := Term.UOp UserOp.distinct
abbrev plus := Term.UOp UserOp.plus
abbrev neg := Term.UOp UserOp.neg
abbrev mult := Term.UOp UserOp.mult
abbrev lt := Term.UOp UserOp.lt
abbrev leq := Term.UOp UserOp.leq
abbrev gt := Term.UOp UserOp.gt
abbrev geq := Term.UOp UserOp.geq
abbrev to_real := Term.UOp UserOp.to_real
abbrev to_int := Term.UOp UserOp.to_int
abbrev is_int := Term.UOp UserOp.is_int
abbrev abs := Term.UOp UserOp.abs
abbrev __eoo_neg_2 := Term.UOp UserOp.__eoo_neg_2
abbrev div := Term.UOp UserOp.div
abbrev mod := Term.UOp UserOp.mod
abbrev divisible := Term.UOp UserOp.divisible
abbrev int_pow2 := Term.UOp UserOp.int_pow2
abbrev int_log2 := Term.UOp UserOp.int_log2
abbrev int_ispow2 := Term.UOp UserOp.int_ispow2
abbrev div_total := Term.UOp UserOp.div_total
abbrev mod_total := Term.UOp UserOp.mod_total
abbrev _at_int_div_by_zero := Term.UOp UserOp._at_int_div_by_zero
abbrev _at_mod_by_zero := Term.UOp UserOp._at_mod_by_zero
abbrev Array := Term.UOp UserOp.Array
abbrev select := Term.UOp UserOp.select
abbrev store := Term.UOp UserOp.store
abbrev _at_bvsize := Term.UOp UserOp._at_bvsize
abbrev concat := Term.UOp UserOp.concat
abbrev extract := Term.UOp2 UserOp2.extract
abbrev «repeat» := Term.UOp1 UserOp1.repeat
abbrev bvnot := Term.UOp UserOp.bvnot
abbrev bvand := Term.UOp UserOp.bvand
abbrev bvor := Term.UOp UserOp.bvor
abbrev bvnand := Term.UOp UserOp.bvnand
abbrev bvnor := Term.UOp UserOp.bvnor
abbrev bvxor := Term.UOp UserOp.bvxor
abbrev bvxnor := Term.UOp UserOp.bvxnor
abbrev bvcomp := Term.UOp UserOp.bvcomp
abbrev bvneg := Term.UOp UserOp.bvneg
abbrev bvadd := Term.UOp UserOp.bvadd
abbrev bvmul := Term.UOp UserOp.bvmul
abbrev bvudiv := Term.UOp UserOp.bvudiv
abbrev bvurem := Term.UOp UserOp.bvurem
abbrev bvsub := Term.UOp UserOp.bvsub
abbrev bvsdiv := Term.UOp UserOp.bvsdiv
abbrev bvsrem := Term.UOp UserOp.bvsrem
abbrev bvsmod := Term.UOp UserOp.bvsmod
abbrev bvult := Term.UOp UserOp.bvult
abbrev bvule := Term.UOp UserOp.bvule
abbrev bvugt := Term.UOp UserOp.bvugt
abbrev bvuge := Term.UOp UserOp.bvuge
abbrev bvslt := Term.UOp UserOp.bvslt
abbrev bvsle := Term.UOp UserOp.bvsle
abbrev bvsgt := Term.UOp UserOp.bvsgt
abbrev bvsge := Term.UOp UserOp.bvsge
abbrev bvshl := Term.UOp UserOp.bvshl
abbrev bvlshr := Term.UOp UserOp.bvlshr
abbrev bvashr := Term.UOp UserOp.bvashr
abbrev zero_extend := Term.UOp1 UserOp1.zero_extend
abbrev sign_extend := Term.UOp1 UserOp1.sign_extend
abbrev rotate_left := Term.UOp1 UserOp1.rotate_left
abbrev rotate_right := Term.UOp1 UserOp1.rotate_right
abbrev bvite := Term.UOp UserOp.bvite
abbrev bvuaddo := Term.UOp UserOp.bvuaddo
abbrev bvnego := Term.UOp UserOp.bvnego
abbrev bvsaddo := Term.UOp UserOp.bvsaddo
abbrev bvumulo := Term.UOp UserOp.bvumulo
abbrev bvsmulo := Term.UOp UserOp.bvsmulo
abbrev bvusubo := Term.UOp UserOp.bvusubo
abbrev bvssubo := Term.UOp UserOp.bvssubo
abbrev bvsdivo := Term.UOp UserOp.bvsdivo
abbrev bvultbv := Term.UOp UserOp.bvultbv
abbrev bvsltbv := Term.UOp UserOp.bvsltbv
abbrev bvredand := Term.UOp UserOp.bvredand
abbrev bvredor := Term.UOp UserOp.bvredor
abbrev _at_bit := Term.UOp1 UserOp1._at_bit
abbrev _at_from_bools := Term.UOp UserOp._at_from_bools
abbrev _at_purify (x : Term) := Term.Apply (Term.UOp UserOp._at_purify) x
abbrev _at_array_deq_diff (x y : Term) :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y
abbrev RegLan := Term.UOp UserOp.RegLan
abbrev str_len := Term.UOp UserOp.str_len
abbrev str_concat := Term.UOp UserOp.str_concat
abbrev str_substr := Term.UOp UserOp.str_substr
abbrev str_contains := Term.UOp UserOp.str_contains
abbrev str_replace := Term.UOp UserOp.str_replace
abbrev str_indexof := Term.UOp UserOp.str_indexof
abbrev str_at := Term.UOp UserOp.str_at
abbrev str_prefixof := Term.UOp UserOp.str_prefixof
abbrev str_suffixof := Term.UOp UserOp.str_suffixof
abbrev str_rev := Term.UOp UserOp.str_rev
abbrev str_update := Term.UOp UserOp.str_update
abbrev str_to_lower := Term.UOp UserOp.str_to_lower
abbrev str_to_upper := Term.UOp UserOp.str_to_upper
abbrev str_to_code := Term.UOp UserOp.str_to_code
abbrev str_from_code := Term.UOp UserOp.str_from_code
abbrev str_is_digit := Term.UOp UserOp.str_is_digit
abbrev str_to_int := Term.UOp UserOp.str_to_int
abbrev str_from_int := Term.UOp UserOp.str_from_int
abbrev str_lt := Term.UOp UserOp.str_lt
abbrev str_leq := Term.UOp UserOp.str_leq
abbrev str_replace_all := Term.UOp UserOp.str_replace_all
abbrev str_replace_re := Term.UOp UserOp.str_replace_re
abbrev str_replace_re_all := Term.UOp UserOp.str_replace_re_all
abbrev str_indexof_re := Term.UOp UserOp.str_indexof_re
abbrev re_allchar := Term.UOp UserOp.re_allchar
abbrev re_none := Term.UOp UserOp.re_none
abbrev re_all := Term.UOp UserOp.re_all
abbrev str_to_re := Term.UOp UserOp.str_to_re
abbrev re_mult := Term.UOp UserOp.re_mult
abbrev re_plus := Term.UOp UserOp.re_plus
abbrev re_exp := Term.UOp1 UserOp1.re_exp
abbrev re_opt := Term.UOp UserOp.re_opt
abbrev re_comp := Term.UOp UserOp.re_comp
abbrev re_range := Term.UOp UserOp.re_range
abbrev re_concat := Term.UOp UserOp.re_concat
abbrev re_inter := Term.UOp UserOp.re_inter
abbrev re_union := Term.UOp UserOp.re_union
abbrev re_diff := Term.UOp UserOp.re_diff
abbrev re_loop := Term.UOp2 UserOp2.re_loop
abbrev str_in_re := Term.UOp UserOp.str_in_re
abbrev seq_empty := Term.UOp1 UserOp1.seq_empty
abbrev seq_unit := Term.UOp UserOp.seq_unit
abbrev seq_nth := Term.UOp UserOp.seq_nth
abbrev _at_re_unfold_pos_component (t r i : Term) : Term :=
  Term.UOp3 UserOp3._at_re_unfold_pos_component t r i
abbrev _at_strings_deq_diff (x y : Term) :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y
abbrev _at_strings_stoi_result (x : Term) :=
  Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x
abbrev _at_strings_stoi_non_digit (x : Term) :=
  Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x
abbrev _at_strings_itos_result (x : Term) :=
  Term.Apply (Term.UOp UserOp._at_strings_itos_result) x
abbrev _at_strings_num_occur := Term.UOp UserOp._at_strings_num_occur
abbrev _at_strings_num_occur_re (x y : Term) :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) x) y
abbrev _at_strings_occur_index := Term.UOp UserOp._at_strings_occur_index
abbrev _at_strings_occur_index_re (x y : Term) :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) x) y
abbrev _at_witness_string_length := Term.UOp3 UserOp3._at_witness_string_length
abbrev _at_strings_replace_all_result (x y z : Term) :=
  Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) x) y) z
abbrev _at_strings_replace_re_all_result (x y z : Term) :=
  Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) x) y) z
abbrev is := Term.UOp1 UserOp1.is
abbrev update := Term.UOp1 UserOp1.update
abbrev UnitTuple := Term.UOp UserOp.UnitTuple
abbrev Tuple := Term.UOp UserOp.Tuple
abbrev tuple_unit := Term.UOp UserOp.tuple_unit
abbrev tuple := Term.UOp UserOp.tuple
abbrev tuple_select := Term.UOp1 UserOp1.tuple_select
abbrev tuple_update := Term.UOp1 UserOp1.tuple_update
abbrev Set := Term.UOp UserOp.Set
abbrev set_empty := Term.UOp1 UserOp1.set_empty
abbrev set_singleton := Term.UOp UserOp.set_singleton
abbrev set_union := Term.UOp UserOp.set_union
abbrev set_inter := Term.UOp UserOp.set_inter
abbrev set_minus := Term.UOp UserOp.set_minus
abbrev set_member := Term.UOp UserOp.set_member
abbrev set_subset := Term.UOp UserOp.set_subset
abbrev set_choose := Term.UOp UserOp.set_choose
abbrev set_is_empty := Term.UOp UserOp.set_is_empty
abbrev set_is_singleton := Term.UOp UserOp.set_is_singleton
abbrev set_insert := Term.UOp UserOp.set_insert
abbrev qdiv := Term.UOp UserOp.qdiv
abbrev qdiv_total := Term.UOp UserOp.qdiv_total
abbrev _at_div_by_zero := Term.UOp UserOp._at_div_by_zero
abbrev _at_sets_deq_diff (x y : Term) :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y
abbrev _at__at_Monomial := Term.UOp UserOp._at__at_Monomial
abbrev _at__at_mon := Term.UOp UserOp._at__at_mon
abbrev _at__at_Polynomial := Term.UOp UserOp._at__at_Polynomial
abbrev _at__at_poly_zero := Term.UOp UserOp._at__at_poly_zero
abbrev _at__at_poly := Term.UOp UserOp._at__at_poly
abbrev «forall» := Term.UOp UserOp.forall
abbrev «exists» := Term.UOp UserOp.exists
abbrev _at_quantifiers_skolemize := Term.UOp2 UserOp2._at_quantifiers_skolemize
abbrev int_to_bv := Term.UOp1 UserOp1.int_to_bv
abbrev ubv_to_int := Term.UOp UserOp.ubv_to_int
abbrev sbv_to_int := Term.UOp UserOp.sbv_to_int
abbrev _at__at_aci_sorted := Term.UOp UserOp._at__at_aci_sorted
abbrev _at_const := Term.UOp2 UserOp2._at_const

attribute [match_pattern]
  Term.Int
  Term.Real
  Term.BitVec
  Term.Char
  Term.Seq
  Term._at__at_Pair
  Term._at__at_pair
  Term._at__at_TypedList
  Term._at__at_TypedList_nil
  Term._at__at_TypedList_cons
  Term.ite
  Term.not
  Term.or
  Term.and
  Term.imp
  Term.xor
  Term.eq
  Term.distinct
  Term.plus
  Term.neg
  Term.mult
  Term.lt
  Term.leq
  Term.gt
  Term.geq
  Term.to_real
  Term.to_int
  Term.is_int
  Term.abs
  Term.__eoo_neg_2
  Term.div
  Term.mod
  Term.divisible
  Term.int_pow2
  Term.int_log2
  Term.int_ispow2
  Term.div_total
  Term.mod_total
  Term._at_int_div_by_zero
  Term._at_mod_by_zero
  Term.Array
  Term.select
  Term.store
  Term._at_bvsize
  Term.concat
  Term.extract
  Term.«repeat»
  Term.bvnot
  Term.bvand
  Term.bvor
  Term.bvnand
  Term.bvnor
  Term.bvxor
  Term.bvxnor
  Term.bvcomp
  Term.bvneg
  Term.bvadd
  Term.bvmul
  Term.bvudiv
  Term.bvurem
  Term.bvsub
  Term.bvsdiv
  Term.bvsrem
  Term.bvsmod
  Term.bvult
  Term.bvule
  Term.bvugt
  Term.bvuge
  Term.bvslt
  Term.bvsle
  Term.bvsgt
  Term.bvsge
  Term.bvshl
  Term.bvlshr
  Term.bvashr
  Term.zero_extend
  Term.sign_extend
  Term.rotate_left
  Term.rotate_right
  Term.bvite
  Term.bvuaddo
  Term.bvnego
  Term.bvsaddo
  Term.bvumulo
  Term.bvsmulo
  Term.bvusubo
  Term.bvssubo
  Term.bvsdivo
  Term.bvultbv
  Term.bvsltbv
  Term.bvredand
  Term.bvredor
  Term._at_bit
  Term._at_from_bools
  Term._at_purify
  Term._at_array_deq_diff
  Term.RegLan
  Term.str_len
  Term.str_concat
  Term.str_substr
  Term.str_contains
  Term.str_replace
  Term.str_indexof
  Term.str_at
  Term.str_prefixof
  Term.str_suffixof
  Term.str_rev
  Term.str_update
  Term.str_to_lower
  Term.str_to_upper
  Term.str_to_code
  Term.str_from_code
  Term.str_is_digit
  Term.str_to_int
  Term.str_from_int
  Term.str_lt
  Term.str_leq
  Term.str_replace_all
  Term.str_replace_re
  Term.str_replace_re_all
  Term.str_indexof_re
  Term.re_allchar
  Term.re_none
  Term.re_all
  Term.str_to_re
  Term.re_mult
  Term.re_plus
  Term.re_exp
  Term.re_opt
  Term.re_comp
  Term.re_range
  Term.re_concat
  Term.re_inter
  Term.re_union
  Term.re_diff
  Term.re_loop
  Term.str_in_re
  Term.seq_empty
  Term.seq_unit
  Term.seq_nth
  Term._at_re_unfold_pos_component
  Term._at_strings_deq_diff
  Term._at_strings_stoi_result
  Term._at_strings_stoi_non_digit
  Term._at_strings_itos_result
  Term._at_strings_num_occur
  Term._at_strings_num_occur_re
  Term._at_strings_occur_index
  Term._at_strings_occur_index_re
  Term._at_witness_string_length
  Term._at_strings_replace_all_result
  Term._at_strings_replace_re_all_result
  Term.is
  Term.update
  Term.UnitTuple
  Term.Tuple
  Term.tuple_unit
  Term.tuple
  Term.tuple_select
  Term.tuple_update
  Term.Set
  Term.set_empty
  Term.set_singleton
  Term.set_union
  Term.set_inter
  Term.set_minus
  Term.set_member
  Term.set_subset
  Term.set_choose
  Term.set_is_empty
  Term.set_is_singleton
  Term.set_insert
  Term.qdiv
  Term.qdiv_total
  Term._at_div_by_zero
  Term._at_sets_deq_diff
  Term._at__at_Monomial
  Term._at__at_mon
  Term._at__at_Polynomial
  Term._at__at_poly_zero
  Term._at__at_poly
  Term.«forall»
  Term.«exists»
  Term._at_quantifiers_skolemize
  Term.int_to_bv
  Term.ubv_to_int
  Term.sbv_to_int
  Term._at__at_aci_sorted
  Term._at_const

end Term
