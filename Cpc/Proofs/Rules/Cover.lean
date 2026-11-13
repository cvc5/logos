module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoveringsSupport
import all Cpc.Proofs.RuleSupport.CoveringsSupport

open Eo
open SmtEval
open Smtm
open CoveringsProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

local notation "MINF" => Term.UOp UserOp._at__at_cov_minus_inf
local notation "PINF" => Term.UOp UserOp._at__at_cov_plus_inf

/-- The interval `(@list l r)` consed onto the intervals `ps`. -/
private abbrev ivCons (l r ps : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons
    (Term.Apply (Term.Apply Term.__eo_List_cons l)
      (Term.Apply (Term.Apply Term.__eo_List_cons r) Term.__eo_List_nil))) ps

/-- `(l, r)` is one of the intervals `ps`. -/
private inductive PieceIn : Term -> Term -> Term -> Prop where
  | head (l r ps : Term) : PieceIn l r (ivCons l r ps)
  | tail (l r l' r' ps : Term) : PieceIn l r ps -> PieceIn l r (ivCons l' r' ps)

/-! ### The disjunction `$mk_cover_rec` builds -/

private def orChain : List Term -> Term
  | [] => Term.Boolean false
  | f :: fs => Term.Apply (Term.Apply (Term.UOp UserOp.or) f) (orChain fs)

private theorem orChain_is_list (fs : List Term) :
    __eo_is_list (Term.UOp UserOp.or) (orChain fs) = Term.Boolean true := by
  induction fs with
  | nil => simp [orChain, __eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
      __eo_is_list_nil, native_ite, native_teq, native_not]
  | cons f fs ih =>
      have hne : orChain fs ≠ Term.Stuck := by cases fs <;> simp [orChain]
      simp only [__eo_is_list, __eo_is_ok] at ih ⊢
      simp [orChain, __eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not] at ih ⊢
      exact ih

/-- `$mk_cover_rec x ps` is `true`, or the disjunction of the pieces of `ps`. -/
private theorem rec_cases (x : Term) :
    ∀ ps, __mk_cover_rec x ps ≠ Term.Stuck ->
      __mk_cover_rec x ps = Term.Boolean true ∨
      ∃ fs, __mk_cover_rec x ps = orChain fs ∧
        (∀ f ∈ fs, ∃ l r, PieceIn l r ps ∧ f = __mk_cover_piece x l r) ∧
        (∀ l r, PieceIn l r ps -> __mk_cover_piece x l r ∈ fs) ∧
        (∀ f ∈ fs, f ≠ Term.Boolean true) := by
  intro ps
  induction hn : sizeOf ps using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  intro h
  have hx : x ≠ Term.Stuck := by rintro rfl; simp [__mk_cover_rec] at h
  rw [__mk_cover_rec.eq_def] at h ⊢
  split at h
  · exact absurd rfl hx
  · exact Or.inr ⟨[], rfl, by simp, (fun l r hp => by cases hp), by simp⟩
  · rename_i _ _ l r ps' _
    simp only at h ⊢
    by_cases hf : __mk_cover_piece x l r = Term.Boolean true
    · left; simp [hf, __eo_ite, __eo_is_eq, native_ite, native_teq, native_and, native_not]
    · have hf' : __eo_is_eq (__mk_cover_piece x l r) (Term.Boolean true) = Term.Boolean false := by
        simp [__eo_is_eq, native_teq, native_and, native_not, Ne.symm hf]
      rw [hf'] at h ⊢
      simp only [__eo_ite, native_ite, native_teq] at h ⊢
      simp only [decide_true, ↓reduceIte] at h ⊢
      by_cases hr : __mk_cover_rec x ps' = Term.Boolean true
      · left; simp [hr, __eo_is_eq, native_teq, native_and, native_not]
      · have hr' : __eo_is_eq (__mk_cover_rec x ps') (Term.Boolean true) = Term.Boolean false := by
          simp [__eo_is_eq, native_teq, native_and, native_not, Ne.symm hr]
        rw [hr'] at h ⊢
        simp only [decide_true, ↓reduceIte] at h ⊢
        have hrS : __mk_cover_rec x ps' ≠ Term.Stuck := by
          intro hs; rw [hs] at h
          simp [__eo_cons, __eo_is_list, __eo_requires, native_ite, native_teq] at h
        rcases ih _ (by subst hn; simp <;> omega) ps' rfl hrS with hT | ⟨fs, hfs, h1, h2, h3⟩
        · exact absurd hT hr
        · right
          refine ⟨__mk_cover_piece x l r :: fs, ?_, ?_, ?_, ?_⟩
          · rw [hfs]
            simp [orChain, __eo_cons, orChain_is_list, __eo_requires, native_ite, native_teq,
              native_not]
          · intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact ⟨l, r, PieceIn.head l r ps', rfl⟩
            · obtain ⟨l', r', hp, rfl⟩ := h1 f hf
              exact ⟨l', r', PieceIn.tail _ _ _ _ _ hp, rfl⟩
          · intro l' r' hp
            cases hp with
            | head => exact List.mem_cons_self
            | tail _ _ _ hp => exact List.mem_cons_of_mem _ (h2 _ _ hp)
          · intro f hf'
            rcases List.mem_cons.mp hf' with rfl | hf'
            · exact hf
            · exact h3 f hf'
  · exact absurd rfl h

private theorem orChain_typeof (fs : List Term) (h : __eo_typeof (orChain fs) = Term.Bool) :
    ∀ f ∈ fs, __eo_typeof f = Term.Bool := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      have h' : __eo_typeof_or (__eo_typeof f) (__eo_typeof (orChain fs)) = Term.Bool := h
      obtain ⟨h1, h2⟩ := RuleProofs.eo_typeof_or_bool_args _ _ h'
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h1
      · exact ih h2 g hg

private theorem or_bool (A B : Term) (hA : RuleProofs.eo_has_bool_type A)
    (hB : RuleProofs.eo_has_bool_type B) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) =
    SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) from rfl, typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem orChain_bool (fs : List Term) (h : ∀ f ∈ fs, RuleProofs.eo_has_bool_type f) :
    RuleProofs.eo_has_bool_type (orChain fs) := by
  induction fs with
  | nil =>
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (orChain []) = SmtTerm.Boolean false from rfl]
      simp [__smtx_typeof]
  | cons f fs ih =>
      exact or_bool _ _ (h f List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

private theorem eval_bool (M : SmtModel) (hM : model_wf M) (t : Term)
    (hB : RuleProofs.eo_has_bool_type t) : ∃ b, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  rcases interprets_true_or_false M hM t hB with h | h <;>
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at h <;> cases h <;> exact ⟨_, by assumption⟩

private theorem orChain_true (M : SmtModel) (hM : model_wf M) (fs : List Term)
    (hb : ∀ f ∈ fs, RuleProofs.eo_has_bool_type f) (h : ∃ f ∈ fs, eo_interprets M f true) :
    eo_interprets M (orChain fs) true := by
  have hB := orChain_bool fs hb
  refine RuleProofs.eo_interprets_of_bool_eval M _ true hB ?_
  induction fs with
  | nil => simp at h
  | cons f fs ih =>
      have hfB := hb f List.mem_cons_self
      have hrB := orChain_bool fs fun g hg => hb g (List.mem_cons_of_mem _ hg)
      obtain ⟨b1, hb1⟩ := eval_bool M hM f hfB
      obtain ⟨b2, hb2⟩ := eval_bool M hM _ hrB
      rw [show __eo_to_smt (orChain (f :: fs)) =
        SmtTerm.or (__eo_to_smt f) (__eo_to_smt (orChain fs)) from rfl, __smtx_model_eval, hb1, hb2]
      obtain ⟨g, hg, hgT⟩ := h
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hgT
        cases hgT with
        | intro_true _ hE => rw [hb1] at hE; cases hE; simp [__smtx_model_eval_or, native_or]
      · have := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg)) ⟨g, hg, hgT⟩ hrB
        rw [hb2] at this; cases this; simp [__smtx_model_eval_or, native_or]

private theorem singleton_elim_orChain (fs : List Term) :
    (∀ f, fs = [f] -> __eo_list_singleton_elim (Term.UOp UserOp.or) (orChain fs) = f) ∧
    ((∀ f, fs ≠ [f]) -> __eo_list_singleton_elim (Term.UOp UserOp.or) (orChain fs) = orChain fs) := by
  have hL := orChain_is_list fs
  have hE : __eo_list_singleton_elim (Term.UOp UserOp.or) (orChain fs) =
      __eo_list_singleton_elim_2 (orChain fs) := by
    simp only [__eo_list_singleton_elim, hL, __eo_requires, native_ite, native_teq, native_not]
    simp
  rw [hE]
  refine ⟨?_, ?_⟩
  · rintro f rfl
    simp [__eo_list_singleton_elim_2, orChain, __eo_ite, __eo_is_list_nil, native_ite, native_teq]
  · intro hne
    rcases fs with _ | ⟨f, _ | ⟨g, gs⟩⟩
    · simp [__eo_list_singleton_elim_2, orChain]
    · exact absurd rfl (hne f)
    · simp [__eo_list_singleton_elim_2, orChain, __eo_ite, __eo_is_list_nil, native_ite, native_teq]

/-! ### Comparing arithmetic endpoints -/

private theorem ran_real_of_covArith {c a b d : Term}
    (h : CovArith (Term.UOp4 UserOp4._at_ran c a b d)) :
    __smtx_typeof (__eo_to_smt (Term.UOp4 UserOp4._at_ran c a b d)) = SmtType.Real := by
  rcases TranslationProofs.eo_to_smt_ran_head_cases c a b d with hE | ⟨F, hE⟩ <;>
    rcases h with h | h <;> rw [hE] at h ⊢
  · simp at h
  · simp at h
  · rcases TranslationProofs.typeof_choice_real_cases (native_string_lit "@x") F with h' | h' <;>
      rw [h'] at h <;> cases h
  · exact h

private theorem covDen_numeral (M : SmtModel) (n : Int) : covDen M (Term.Numeral n) = n := by
  simp [covDen, arith_poly_norm_atom_denote_real_of_numeral, native_int_to_real]

/-- A numeric literal. -/
private def LitTerm (e : Term) : Prop :=
  (∃ n, e = Term.Numeral n) ∨ (∃ q, e = Term.Rational q) ∨ (∃ w n, e = Term.Binary w n)

private def IsRan (e : Term) : Prop := ∃ c a b d, e = Term.UOp4 UserOp4._at_ran c a b d

private theorem eo_gt_bool_shapes {x y : Term} {b : Bool} (h : __eo_gt x y = Term.Boolean b) :
    LitTerm x ∧ LitTerm y := by
  unfold __eo_gt at h
  split at h
  · exact ⟨Or.inl ⟨_, rfl⟩, Or.inl ⟨_, rfl⟩⟩
  · exact ⟨Or.inr (Or.inl ⟨_, rfl⟩), Or.inr (Or.inl ⟨_, rfl⟩)⟩
  · exact ⟨Or.inr (Or.inr ⟨_, _, rfl⟩), Or.inr (Or.inr ⟨_, _, rfl⟩)⟩
  · cases h

private theorem eo_not_bool {x : Term} (h : __eo_not x = Term.Boolean true) :
    x = Term.Boolean false := by
  cases x <;> simp_all [__eo_not, native_not]

/-- What `$cov_lt` succeeds on: literals and real algebraic numbers. -/
private theorem cov_lt_shapes {a b : Term} (h : __cov_lt a b = Term.Boolean true) :
    (IsRan a ∨ LitTerm a) ∧ (IsRan b ∨ LitTerm b) := by
  unfold __cov_lt at h
  split at h
  · simp at h
  · simp at h
  · exact ⟨Or.inl ⟨_, _, _, _, rfl⟩, Or.inl ⟨_, _, _, _, rfl⟩⟩
  · obtain ⟨_, hn⟩ := eo_and_true_inv h
    exact ⟨Or.inl ⟨_, _, _, _, rfl⟩, Or.inr (eo_gt_bool_shapes (eo_not_bool hn)).2⟩
  · obtain ⟨_, hn⟩ := eo_and_true_inv h
    exact ⟨Or.inr (eo_gt_bool_shapes (eo_not_bool hn)).1, Or.inl ⟨_, _, _, _, rfl⟩⟩
  · have := eo_gt_bool_shapes h
    exact ⟨Or.inr this.2, Or.inr this.1⟩

private theorem typeof_numeral (n : Int) :
    __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
  rw [__eo_to_smt.eq_def]; simp [__smtx_typeof]

private theorem typeof_rational (q : Rat) :
    __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Real := by
  rw [__eo_to_smt.eq_def]; simp [__smtx_typeof]

private theorem not_covArith_binary (w n : Int) : ¬ CovArith (Term.Binary w n) := by
  intro h
  rw [CovArith, __eo_to_smt.eq_def] at h
  simp only at h
  rw [__smtx_typeof.eq_def] at h
  simp only at h
  unfold native_ite at h
  split at h <;> simp at h

/-- `$cov_lt` compares, by value, endpoints of the arithmetic sort `T`. -/
private theorem cov_lt_sound_arith (M : SmtModel) (hM : model_wf M) {a b : Term} {T : SmtType}
    (ha : __smtx_typeof (__eo_to_smt a) = T) (hb : __smtx_typeof (__eo_to_smt b) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real)
    (h : __cov_lt a b = Term.Boolean true) : covDen M a < covDen M b := by
  obtain ⟨hsa, hsb⟩ := cov_lt_shapes h
  have hAa : CovArith a := by rw [CovArith, ha]; exact hT
  have hAb : CovArith b := by rw [CovArith, hb]; exact hT
  have fin : ∀ e, __smtx_typeof (__eo_to_smt e) = SmtType.Real -> (IsRan e ∨ LitTerm e) ->
      FinEnd e := by
    intro e he hs
    rcases hs with ⟨c, x, y, d, rfl⟩ | ⟨n, rfl⟩ | ⟨q, rfl⟩ | ⟨w, n, rfl⟩
    · exact Or.inr ⟨c, x, y, d, rfl, he⟩
    · rw [typeof_numeral] at he; cases he
    · exact Or.inl ⟨q, rfl⟩
    · exact absurd (Or.inr he) (not_covArith_binary w n)
  rcases hT with rfl | rfl
  · -- integers: both are numerals
    have num : ∀ e, __smtx_typeof (__eo_to_smt e) = SmtType.Int -> (IsRan e ∨ LitTerm e) ->
        ∃ n, e = Term.Numeral n := by
      intro e he hs
      rcases hs with ⟨c, x, y, d, rfl⟩ | ⟨n, rfl⟩ | ⟨q, rfl⟩ | ⟨w, n, rfl⟩
      · rw [ran_real_of_covArith (Or.inl he)] at he; cases he
      · exact ⟨n, rfl⟩
      · rw [typeof_rational] at he; cases he
      · exact absurd (Or.inl he) (not_covArith_binary w n)
    obtain ⟨n, rfl⟩ := num a ha hsa
    obtain ⟨m, rfl⟩ := num b hb hsb
    simp [__cov_lt, __eo_gt, native_zlt] at h
    rw [covDen_numeral, covDen_numeral]
    exact_mod_cast h
  · exact cov_lt_sound M hM (fin a ha hsa) (fin b hb hsb) h

/-! ### The pieces of a covering -/

private theorem typeof_minf : __smtx_typeof (__eo_to_smt MINF) = SmtType.None := by
  rw [show __eo_to_smt MINF = SmtTerm.None by rw [__eo_to_smt.eq_def]]; simp

private theorem typeof_pinf : __smtx_typeof (__eo_to_smt PINF) = SmtType.None := by
  rw [show __eo_to_smt PINF = SmtTerm.None by rw [__eo_to_smt.eq_def]]; simp

/-- A typed piece that is not `true`, of a covering of `x`. -/
private def PieceGood (x l r : Term) : Prop :=
  __mk_cover_piece x l r ≠ Term.Stuck ∧ RuleProofs.eo_has_bool_type (__mk_cover_piece x l r) ∧
    __mk_cover_piece x l r ≠ Term.Boolean true

private theorem rel_args_same (rel : CovRel) (hrel : rel = CovRel.lt ∨ rel = CovRel.gt)
    (x e : Term) (h : RuleProofs.eo_has_bool_type (rel.atom x e)) :
    __smtx_typeof (__eo_to_smt e) = __smtx_typeof (__eo_to_smt x) ∧ CovArith x := by
  have hab :
      (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧ __smtx_typeof (__eo_to_smt e) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧ __smtx_typeof (__eo_to_smt e) = SmtType.Real) := by
    rcases hrel with rfl | rfl
    · exact rel_operands_arith_type_of_lt_has_bool_type x e h
    · exact rel_operands_arith_type_of_gt_has_bool_type x e h
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h2.trans h1.symm, Or.inl h1⟩
  · exact ⟨h2.trans h1.symm, Or.inr h1⟩

/-- The finite endpoints of a good piece have the sort of `x`. -/
private theorem piece_endpoints (x l r : Term) (T : SmtType)
    (hx : __smtx_typeof (__eo_to_smt x) = T) (hT : T = SmtType.Int ∨ T = SmtType.Real)
    (hG : PieceGood x l r) :
    (l ≠ MINF -> l ≠ PINF ∧ __smtx_typeof (__eo_to_smt l) = T) ∧
    (r ≠ PINF -> r ≠ MINF ∧ __smtx_typeof (__eo_to_smt r) = T) := by
  obtain ⟨hP, hB, hNT⟩ := hG
  have hTn : T ≠ SmtType.None := by rcases hT with rfl | rfl <;> simp
  obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l r hP
  rcases hc with ⟨rfl, rfl, hE⟩ | ⟨rfl, hr, hE⟩ | ⟨hl, rfl, hE⟩ | ⟨hl, hr, hlp, hrm, ⟨rfl, hE⟩ | ⟨_, hE⟩⟩
  · exact absurd hE hNT
  · rw [hE] at hB
    obtain ⟨hre, _⟩ := rel_args_same CovRel.lt (Or.inl rfl) x r hB
    refine ⟨fun h => absurd rfl h, fun _ => ⟨?_, hre.trans hx⟩⟩
    rintro rfl; rw [typeof_minf, hx] at hre; exact hTn hre.symm
  · rw [hE] at hB
    obtain ⟨hle, _⟩ := rel_args_same CovRel.gt (Or.inr rfl) x l hB
    refine ⟨fun _ => ⟨?_, hle.trans hx⟩, fun h => absurd rfl h⟩
    rintro rfl; rw [typeof_pinf, hx] at hle; exact hTn hle.symm
  · rw [hE] at hB
    have h := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x l hB
    exact ⟨fun _ => ⟨hlp, h.1.symm.trans hx⟩, fun _ => ⟨hrm, h.1.symm.trans hx⟩⟩
  · rw [hE] at hB
    have h1 := RuleProofs.eo_has_bool_type_and_left _ _ hB
    have h2 := RuleProofs.eo_has_bool_type_and_left _ _ (RuleProofs.eo_has_bool_type_and_right _ _ hB)
    obtain ⟨hle, _⟩ := rel_args_same CovRel.gt (Or.inr rfl) x l h1
    obtain ⟨hre, _⟩ := rel_args_same CovRel.lt (Or.inl rfl) x r h2
    exact ⟨fun _ => ⟨hlp, hle.trans hx⟩, fun _ => ⟨hrm, hre.trans hx⟩⟩

private theorem rel_true_of_holds (M : SmtModel) (hM : model_wf M) (rel : CovRel) (a b : Term)
    (hb : CovArith b) (hB : RuleProofs.eo_has_bool_type (rel.atom a b))
    (h : rel.holds (covDen M a) (covDen M b)) : eo_interprets M (rel.atom a b) true := by
  obtain ⟨_, hE⟩ := covRel_eval M hM rel a b hb hB
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hB (by rw [hE]; simp [h])

/-- A good piece holds wherever `x` lies in it. -/
private theorem piece_holds (M : SmtModel) (hM : model_wf M) (x l r : Term) (T : SmtType)
    (hx : __smtx_typeof (__eo_to_smt x) = T) (hT : T = SmtType.Int ∨ T = SmtType.Real)
    (hG : PieceGood x l r) :
    (l ≠ r -> InL M l (covDen M x) -> InR M r (covDen M x) ->
      eo_interprets M (__mk_cover_piece x l r) true) ∧
    (l = r -> l ≠ MINF -> covDen M x = covDen M l ->
      eo_interprets M (__mk_cover_piece x l r) true) := by
  obtain ⟨hle, hre⟩ := piece_endpoints x l r T hx hT hG
  have hA : ∀ e, __smtx_typeof (__eo_to_smt e) = T -> CovArith e := by
    intro e he; rw [CovArith, he]; exact hT
  obtain ⟨hP, hB, hNT⟩ := hG
  obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l r hP
  rcases hc with ⟨rfl, rfl, hE⟩ | ⟨rfl, hr, hE⟩ | ⟨hl, rfl, hE⟩ | ⟨hl, hr, hlp, hrm, ⟨rfl, hE⟩ | ⟨hlr, hE⟩⟩
  · exact absurd hE hNT
  · rw [hE] at hB ⊢
    obtain ⟨hrm, hrT⟩ := hre hr
    refine ⟨fun _ _ hIR => ?_, fun h => absurd h.symm hrm⟩
    rcases hIR with h | h
    · exact absurd h hr
    · exact rel_true_of_holds M hM CovRel.lt x r (hA r hrT) hB h
  · rw [hE] at hB ⊢
    obtain ⟨hlp, hlT⟩ := hle hl
    refine ⟨fun _ hIL _ => ?_, fun h => absurd h hlp⟩
    rcases hIL with h | h
    · exact absurd h hl
    · exact rel_true_of_holds M hM CovRel.gt x l (hA l hlT) hB h
  · rw [hE] at hB ⊢
    obtain ⟨_, hlT⟩ := hle hl
    exact ⟨fun h => absurd rfl h, fun _ _ h => rel_true_of_holds M hM CovRel.eq x l (hA l hlT) hB h⟩
  · rw [hE] at hB ⊢
    obtain ⟨_, hlT⟩ := hle hl
    obtain ⟨_, hrT⟩ := hre hr
    refine ⟨fun _ hIL hIR => ?_, fun h => absurd h hlr⟩
    have h1 := RuleProofs.eo_has_bool_type_and_left _ _ hB
    have h23 := RuleProofs.eo_has_bool_type_and_right _ _ hB
    have h2 := RuleProofs.eo_has_bool_type_and_left _ _ h23
    rcases hIL with h | hIL; exact absurd h hl
    rcases hIR with h | hIR; exact absurd h hr
    exact RuleProofs.eo_interprets_and_intro M _ _
      (rel_true_of_holds M hM CovRel.gt x l (hA l hlT) h1 hIL)
      (RuleProofs.eo_interprets_and_intro M _ _
        (rel_true_of_holds M hM CovRel.lt x r (hA r hrT) h2 hIR)
        (RuleProofs.eo_interprets_true M))

/-! ### The sweep -/

/-- Every value below `c` is covered, and `c` itself too when `incl`: so a value still to be
covered is one that is past `c`, or at it when `c` is not yet included. -/
private def AfterC (M : SmtModel) (incl : Bool) (c : Term) (v : Real) : Prop :=
  c = MINF ∨ (c ≠ PINF ∧ (covDen M c < v ∨ (v = covDen M c ∧ incl = false)))

private theorem is_eq_true {a b : Term} (h : __eo_is_eq a b = Term.Boolean true) : a = b := by
  simp [__eo_is_eq, native_and, native_not, native_teq] at h
  exact h.2.2.symm

private theorem is_eq_false {a b : Term} (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (h : __eo_is_eq a b = Term.Boolean false) : a ≠ b := by
  rintro rfl
  simp [__eo_is_eq, native_and, native_not, native_teq, ha] at h

private theorem bound_lt_pinf_left {r : Term} (h : __cov_bound_lt PINF r = Term.Boolean true) :
    False := by
  unfold __cov_bound_lt at h
  split at h <;> simp_all

/-- Attaching the piece `(l, _)` to the sweep at `c` puts every value still to be covered
above `l`. -/
private theorem attach_sound (M : SmtModel) (hM : model_wf M) (incl : Bool) (l c r : Term)
    (T : SmtType) (hT : T = SmtType.Int ∨ T = SmtType.Real)
    (hl : l ≠ MINF -> __smtx_typeof (__eo_to_smt l) = T)
    (hc : c = MINF ∨ c = PINF ∨ __smtx_typeof (__eo_to_smt c) = T)
    (hatt : __eo_ite (Term.Boolean incl) (__cov_attach_incl l c) (__cov_attach l c) =
      Term.Boolean true)
    (hbl : __cov_bound_lt c r = Term.Boolean true) (v : Real) (hA : AfterC M incl c v) :
    InL M l v := by
  have hcp : c ≠ PINF := by rintro rfl; exact bound_lt_pinf_left hbl
  have hcT : c ≠ MINF -> __smtx_typeof (__eo_to_smt c) = T := by
    intro hcm; rcases hc with h | h | h; exact absurd h hcm; exact absurd h hcp; exact h
  cases incl with
  | false =>
      simp [__eo_ite, native_ite, native_teq] at hatt
      unfold __cov_attach at hatt
      split at hatt
      · simp at hatt
      · simp at hatt
      · exact Or.inl rfl
      · simp at hatt
      · simp at hatt
      · exact absurd rfl hcp
      · rename_i _ _ _ hlm _ _ hcm _
        right
        have hlt := cov_lt_sound_arith M hM (hl hlm) (hcT hcm) hT hatt
        rcases hA with h | ⟨_, h | ⟨h, _⟩⟩
        · exact absurd h hcm
        · linarith
        · linarith
  | true =>
      simp [__eo_ite, native_ite, native_teq] at hatt
      unfold __cov_attach_incl at hatt
      split at hatt
      · simp at hatt
      · simp at hatt
      · exact Or.inl rfl
      · simp at hatt
      · rename_i _ _ _ hlm _ _
        right
        rcases eo_ite_true_cases hatt with ⟨hEq, _⟩ | ⟨_, hlt⟩
        · have := is_eq_true hEq
          subst this
          rcases hA with h | ⟨_, h | ⟨_, h⟩⟩
          · exact absurd h (fun h' => hlm h')
          · exact h
          · cases h
        · have hcm : c ≠ MINF := by
            rintro rfl
            rcases (cov_lt_shapes hlt).2 with ⟨_, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
          have hlt' := cov_lt_sound_arith M hM (hl (fun h => hlm h)) (hcT hcm) hT hlt
          rcases hA with h | ⟨_, h | ⟨_, h⟩⟩
          · exact absurd h hcm
          · linarith
          · cases h

private theorem cov_eo_or_false {a b : Term} (h : __eo_or a b = Term.Boolean false) :
    a = Term.Boolean false ∧ b = Term.Boolean false := by
  cases a <;> cases b <;> simp_all [__eo_or, native_or]
  all_goals first
    | (simp [__eo_requires, native_ite, native_teq, native_not] at h; split at h <;> simp_all)
    | skip

private theorem is_eq_false_of_ne {a b : Term} (h : __eo_is_eq a b = Term.Boolean false)
    (ha : a ≠ Term.Stuck) : a ≠ b := by
  rintro rfl; simp [__eo_is_eq, native_and, native_not, native_teq, ha] at h

private theorem sweep_shapes (incl : Bool) (c ps : Term)
    (h : __cov_sweep (Term.Boolean incl) c ps ≠ Term.Stuck) :
    ps = Term.__eo_List_nil ∨ ∃ l r ps', ps = ivCons l r ps' := by
  unfold __cov_sweep at h
  split at h
  · simp at h
  · simp at h
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, _, rfl⟩
  · simp at h

private theorem sweep_nil (incl : Bool) (c : Term) (hc : c ≠ Term.Stuck) :
    __cov_sweep (Term.Boolean incl) c Term.__eo_List_nil =
      __eo_and (__eo_not (Term.Boolean incl)) (__eo_is_eq c PINF) := by
  cases c <;> simp_all [__cov_sweep]

private theorem sweep_cons (incl : Bool) (c l r ps : Term) (hc : c ≠ Term.Stuck) :
    __cov_sweep (Term.Boolean incl) c (ivCons l r ps) =
      __eo_ite (__eo_is_eq l r)
        (__eo_ite (__eo_or (__eo_is_eq l MINF) (__eo_is_eq l PINF)) (Term.Boolean false)
          (__eo_ite (__eo_and (__eo_not (Term.Boolean incl)) (__eo_is_eq l c))
            (__cov_sweep (Term.Boolean true) c ps) (__cov_sweep (Term.Boolean incl) c ps)))
        (__eo_ite (__eo_and (__eo_ite (Term.Boolean incl) (__cov_attach_incl l c) (__cov_attach l c))
            (__cov_bound_lt c r))
          (__cov_sweep (Term.Boolean false) r ps) (__cov_sweep (Term.Boolean incl) c ps)) := by
  rw [__cov_sweep.eq_def]
  cases c <;> simp_all

/-- The sweep of `$cov_sweep`: once it succeeds, a value still to be covered is covered by a
piece it has yet to read. -/
private theorem sweep_sound (M : SmtModel) (hM : model_wf M) (x : Term) (T : SmtType)
    (hx : __smtx_typeof (__eo_to_smt x) = T) (hT : T = SmtType.Int ∨ T = SmtType.Real)
    (ps0 : Term) (hgood : ∀ l r, PieceIn l r ps0 -> PieceGood x l r) :
    ∀ ps (incl : Bool) c, (∀ l r, PieceIn l r ps -> PieceIn l r ps0) ->
      (c = MINF ∨ c = PINF ∨ __smtx_typeof (__eo_to_smt c) = T) ->
      __cov_sweep (Term.Boolean incl) c ps = Term.Boolean true ->
      AfterC M incl c (covDen M x) ->
      ∃ l r, PieceIn l r ps0 ∧ eo_interprets M (__mk_cover_piece x l r) true := by
  intro ps
  induction hn : sizeOf ps using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  intro incl c hsub hc h hA
  have hcS : c ≠ Term.Stuck := by
    rintro rfl
    rcases hc with h' | h' | h'
    · cases h'
    · cases h'
    · rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rw [__eo_to_smt.eq_def]] at h'
      simp at h'; rcases hT with rfl | rfl <;> simp_all
  rcases sweep_shapes incl c ps (by rw [h]; simp) with rfl | ⟨l, r, ps', rfl⟩
  · -- the end of the intervals: the sweep has reached `+∞`
    rw [sweep_nil incl c hcS] at h
    obtain ⟨_, h2⟩ := eo_and_true_inv h
    have := is_eq_true h2
    subst this
    rcases hA with h | ⟨h, _⟩
    · cases h
    · exact absurd rfl h
  · rw [sweep_cons incl c l r ps' hcS] at h
    have hIn : PieceIn l r ps0 := hsub l r (PieceIn.head l r ps')
    have hsub' : ∀ l' r', PieceIn l' r' ps' -> PieceIn l' r' ps0 :=
      fun l' r' hp => hsub l' r' (PieceIn.tail _ _ _ _ _ hp)
    have hsz : sizeOf ps' < n := by subst hn; simp <;> omega
    have hG := hgood l r hIn
    obtain ⟨hle, hre⟩ := piece_endpoints x l r T hx hT hG
    obtain ⟨hpc, hpp⟩ := piece_holds M hM x l r T hx hT hG
    obtain ⟨_, hlS, hrS, _⟩ := mk_cover_piece_cases x l r hG.1
    rcases eo_ite_true_cases h with ⟨hlr, hA1⟩ | ⟨hlr, hB1⟩
    · -- a point
      have hlr := is_eq_true hlr
      subst hlr
      rcases eo_ite_true_cases hA1 with ⟨_, hF⟩ | ⟨hinf, hA2⟩
      · cases hF
      obtain ⟨hm, hp⟩ := cov_eo_or_false hinf
      have hlm := is_eq_false_of_ne hm hlS
      rcases eo_ite_true_cases hA2 with ⟨hnew, hS⟩ | ⟨_, hS⟩
      · obtain ⟨hni, hlc⟩ := eo_and_true_inv hnew
        have hlc := is_eq_true hlc
        subst hlc
        clear hA1 hA2
        have hincl : incl = false := by cases incl <;> simp_all [__eo_not, native_not]
        subst hincl
        rcases hA with h' | ⟨hcp, hlt | ⟨heq, _⟩⟩
        · exact absurd h' hlm
        · exact ih _ hsz ps' rfl true l hsub' hc hS (Or.inr ⟨hcp, Or.inl hlt⟩)
        · exact ⟨l, l, hIn, hpp rfl hlm heq⟩
      · exact ih _ hsz ps' rfl incl c hsub' hc hS hA
    · -- an interval
      have hlr := is_eq_false_of_ne hlr hlS
      rcases eo_ite_true_cases hB1 with ⟨hatt, h⟩ | ⟨_, h⟩
      · obtain ⟨hatt, hbl⟩ := eo_and_true_inv hatt
        have hr' : r = MINF ∨ r = PINF ∨ __smtx_typeof (__eo_to_smt r) = T := by
          by_cases hrp : r = PINF
          · exact Or.inr (Or.inl hrp)
          · exact Or.inr (Or.inr (hre hrp).2)
        by_cases hAr : AfterC M false r (covDen M x)
        · exact ih _ hsz ps' rfl false r hsub' hr' h hAr
        · have hIL := attach_sound M hM incl l c r T hT (fun h => (hle h).2) hc hatt hbl _ hA
          have hIR : InR M r (covDen M x) := by
            simp only [AfterC, not_or, not_and] at hAr
            by_cases hrp : r = PINF
            · exact Or.inl hrp
            · right
              obtain ⟨_, h2⟩ := hAr
              have := h2 hrp
              rcases lt_trichotomy (covDen M x) (covDen M r) with h' | h' | h'
              · exact h'
              · exact ((this.2 h') trivial).elim
              · exact absurd h' this.1
          exact ⟨l, r, hIn, hpc hlr hIL hIR⟩
      · exact ih _ hsz ps' rfl incl c hsub' hc h hA

private theorem sweep_cS {incl : Bool} {c ps : Term}
    (h : __cov_sweep (Term.Boolean incl) c ps = Term.Boolean true) : c ≠ Term.Stuck := by
  rintro rfl; cases ps <;> simp [__cov_sweep] at h

/-- A successful sweep never meets a point at infinity. -/
private theorem sweep_no_inf_point :
    ∀ ps (incl : Bool) c, __cov_sweep (Term.Boolean incl) c ps = Term.Boolean true ->
      ∀ l r, PieceIn l r ps -> ¬ (l = r ∧ (l = MINF ∨ l = PINF)) := by
  intro ps
  induction hn : sizeOf ps using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  intro incl c h l r hp
  have hcS := sweep_cS h
  rcases sweep_shapes incl c ps (by rw [h]; simp) with rfl | ⟨l', r', ps', rfl⟩
  · cases hp
  rw [sweep_cons incl c l' r' ps' hcS] at h
  have hsz : sizeOf ps' < n := by subst hn; simp <;> omega
  have hrec : ∀ (incl' : Bool) c', __cov_sweep (Term.Boolean incl') c' ps' = Term.Boolean true ->
      PieceIn l r ps' -> ¬ (l = r ∧ (l = MINF ∨ l = PINF)) :=
    fun incl' c' h' hp' => ih _ hsz ps' rfl incl' c' h' l r hp'
  rcases eo_ite_true_cases h with ⟨hlr, hA1⟩ | ⟨hlr, hB1⟩
  · rcases eo_ite_true_cases hA1 with ⟨_, hF⟩ | ⟨hinf, hA2⟩
    · cases hF
    cases hp with
    | head =>
        rintro ⟨_, hl⟩
        obtain ⟨hm, hp'⟩ := cov_eo_or_false hinf
        rcases hl with rfl | rfl <;>
          simp [__eo_is_eq, native_and, native_not, native_teq] at hm hp'
    | tail _ _ _ hp =>
        rcases eo_ite_true_cases hA2 with ⟨_, hS⟩ | ⟨_, hS⟩
        · exact hrec _ _ hS hp
        · exact hrec _ _ hS hp
  · cases hp with
    | head =>
        rintro ⟨rfl, hl⟩
        have : l ≠ Term.Stuck := by rcases hl with rfl | rfl <;> simp
        simp [__eo_is_eq, native_and, native_not, native_teq, this] at hlr
    | tail _ _ _ hp =>
        rcases eo_ite_true_cases hB1 with ⟨_, hS⟩ | ⟨_, hS⟩
        · exact hrec _ _ hS hp
        · exact hrec _ _ hS hp

/-- A successful sweep that has not yet reached `+∞` reaches it through a piece. -/
private theorem sweep_reaches :
    ∀ ps (incl : Bool) c, __cov_sweep (Term.Boolean incl) c ps = Term.Boolean true -> c ≠ PINF ->
      ∃ l, PieceIn l PINF ps ∧ l ≠ PINF := by
  intro ps
  induction hn : sizeOf ps using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  intro incl c h hc
  have hcS := sweep_cS h
  rcases sweep_shapes incl c ps (by rw [h]; simp) with rfl | ⟨l, r, ps', rfl⟩
  · rw [sweep_nil incl c hcS] at h
    obtain ⟨_, h2⟩ := eo_and_true_inv h
    exact absurd (is_eq_true h2) hc
  rw [sweep_cons incl c l r ps' hcS] at h
  have hsz : sizeOf ps' < n := by subst hn; simp <;> omega
  have lift : ∀ (incl' : Bool) c', __cov_sweep (Term.Boolean incl') c' ps' = Term.Boolean true ->
      c' ≠ PINF -> ∃ l', PieceIn l' PINF (ivCons l r ps') ∧ l' ≠ PINF := by
    intro incl' c' h' hc'
    obtain ⟨l', hp, hl'⟩ := ih _ hsz ps' rfl incl' c' h' hc'
    exact ⟨l', PieceIn.tail _ _ _ _ _ hp, hl'⟩
  rcases eo_ite_true_cases h with ⟨_, hA1⟩ | ⟨hlr, hB1⟩
  · rcases eo_ite_true_cases hA1 with ⟨_, hF⟩ | ⟨_, hA2⟩
    · cases hF
    rcases eo_ite_true_cases hA2 with ⟨_, hS⟩ | ⟨_, hS⟩
    · exact lift _ _ hS hc
    · exact lift _ _ hS hc
  · rcases eo_ite_true_cases hB1 with ⟨hatt, hS⟩ | ⟨_, hS⟩
    · by_cases hr : r = PINF
      · subst hr
        have hlS : l ≠ Term.Stuck := by
          rintro rfl
          obtain ⟨ha, _⟩ := eo_and_true_inv hatt
          cases incl <;> simp [__eo_ite, native_ite, native_teq, __cov_attach, __cov_attach_incl] at ha
        exact ⟨l, PieceIn.head _ _ _, is_eq_false_of_ne hlr hlS⟩
      · exact lift _ _ hS hr
    · exact lift _ _ hS hc

/-! ### The rule -/

private theorem prog_cover_inv (x ps : Term) (h : __eo_prog_cover x ps ≠ Term.Stuck) :
    x ≠ Term.Stuck ∧
    __cov_sweep (Term.Boolean false) MINF ps = Term.Boolean true ∧
    __eo_prog_cover x ps =
      __eo_ite (__eo_is_eq (__mk_cover_rec x ps) (Term.Boolean true)) (Term.Boolean true)
        (__eo_list_singleton_elim (Term.UOp UserOp.or) (__mk_cover_rec x ps)) := by
  have hx : x ≠ Term.Stuck := by rintro rfl; simp [__eo_prog_cover] at h
  have hps : ps ≠ Term.Stuck := by rintro rfl; cases x <;> simp_all [__eo_prog_cover]
  have hEq : __eo_prog_cover x ps =
      __eo_requires (__cov_sweep (Term.Boolean false) MINF ps) (Term.Boolean true)
        (__eo_ite (__eo_is_eq (__mk_cover_rec x ps) (Term.Boolean true)) (Term.Boolean true)
          (__eo_list_singleton_elim (Term.UOp UserOp.or) (__mk_cover_rec x ps))) := by
    rw [__eo_prog_cover.eq_def]
    cases x <;> cases ps <;> simp_all
  rw [hEq] at h ⊢
  obtain ⟨h1, h2⟩ := eo_requires_eq_body h
  exact ⟨hx, h1, h2⟩

private theorem covIntervals_endpoints {ps : Term} (hps : CovIntervalsOk ps) :
    ∀ l r, PieceIn l r ps -> CovEndpointOk l ∧ CovEndpointOk r := by
  intro l r hp
  revert hps
  induction hp with
  | head _ => intro hps; exact ⟨hps.1, hps.2.1⟩
  | tail _ _ _ _ ih => intro hps; exact ih hps.2.2

private theorem endpoint_trans {e : Term} (h : CovEndpointOk e) (hm : e ≠ MINF) (hp : e ≠ PINF) :
    RuleProofs.eo_has_smt_translation e := by
  unfold CovEndpointOk at h
  split at h
  · exact absurd rfl hm
  · exact absurd rfl hp
  · exact h

/-- The infinity markers of a piece that is not stuck, and not a point at infinity, are on
the side they bound. -/
private theorem piece_inf_sides (x l r : Term) (hP : __mk_cover_piece x l r ≠ Term.Stuck)
    (hpt : ¬ (l = r ∧ (l = MINF ∨ l = PINF))) : l ≠ PINF ∧ r ≠ MINF := by
  obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l r hP
  rcases hc with ⟨rfl, rfl, _⟩ | ⟨rfl, hr, _⟩ | ⟨hl, rfl, _⟩ | ⟨_, _, hlp, hrm, _⟩
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, fun h => hpt ⟨h.symm, Or.inl rfl⟩⟩
  · exact ⟨fun h => hpt ⟨h, Or.inr h⟩, by simp⟩
  · exact ⟨hlp, hrm⟩

/-- The conclusion of `cover` is a Boolean that holds in every model. -/
private theorem cover_sound (M : SmtModel) (hM : model_wf M) (x ps : Term)
    (hxT : RuleProofs.eo_has_smt_translation x) (hps : CovIntervalsOk ps)
    (hTy : __eo_typeof (__eo_prog_cover x ps) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_cover x ps) ∧ eo_interprets M (__eo_prog_cover x ps) true := by
  have hProg := term_ne_stuck_of_typeof_bool hTy
  obtain ⟨hx, hsw, hEq⟩ := prog_cover_inv x ps hProg
  rw [hEq] at hTy hProg ⊢
  by_cases hrt : __mk_cover_rec x ps = Term.Boolean true
  · rw [hrt]
    simp only [__eo_ite, __eo_is_eq, native_and, native_not, native_teq, native_ite]
    simp
    exact ⟨RuleProofs.eo_has_bool_type_true, RuleProofs.eo_interprets_true M⟩
  have hIte : __eo_ite (__eo_is_eq (__mk_cover_rec x ps) (Term.Boolean true)) (Term.Boolean true)
      (__eo_list_singleton_elim (Term.UOp UserOp.or) (__mk_cover_rec x ps)) =
      __eo_list_singleton_elim (Term.UOp UserOp.or) (__mk_cover_rec x ps) := by
    simp [__eo_ite, __eo_is_eq, native_and, native_not, native_teq, native_ite, Ne.symm hrt]
  rw [hIte] at hTy hProg ⊢
  have hrS : __mk_cover_rec x ps ≠ Term.Stuck := by
    intro hs; rw [hs] at hProg
    exact hProg (by simp [__eo_list_singleton_elim, __eo_requires, __eo_is_list, native_ite,
      native_teq])
  rcases rec_cases x ps hrS with h | ⟨fs, hfs, h1, h2, h3⟩
  · exact absurd h hrt
  rw [hfs] at hTy ⊢
  obtain ⟨hS1, hS2⟩ := singleton_elim_orChain fs
  -- every piece has Eunoia type `Bool`
  have hfTy : ∀ f ∈ fs, __eo_typeof f = Term.Bool := by
    by_cases hone : ∃ f, fs = [f]
    · rcases hone with ⟨f, rfl⟩
      rw [hS1 f rfl] at hTy
      intro g hg; rw [List.mem_singleton.mp hg]; exact hTy
    · push Not at hone
      rw [hS2 hone] at hTy
      exact orChain_typeof fs hTy
  -- so every piece is good
  have hgood : ∀ l r, PieceIn l r ps -> PieceGood x l r := by
    intro l r hp
    have hmem := h2 l r hp
    have hpTy := hfTy _ hmem
    have hP := term_ne_stuck_of_typeof_bool hpTy
    obtain ⟨hlp, hrm⟩ := piece_inf_sides x l r hP (sweep_no_inf_point ps false MINF hsw l r hp)
    obtain ⟨hlE, hrE⟩ := covIntervals_endpoints hps l r hp
    exact ⟨hP, piece_bool x l r hP hxT (fun hm => endpoint_trans hlE hm hlp)
      (fun hp' => endpoint_trans hrE hrm hp') hpTy, h3 _ hmem⟩
  -- `x` is arithmetic: the sweep reaches `+∞` through a piece `x > l`
  obtain ⟨l, hpl, hlp⟩ := sweep_reaches ps false MINF hsw (by simp)
  have hGl := hgood l _ hpl
  have hxA : CovArith x := by
    obtain ⟨hP, hB, hNT⟩ := hGl
    obtain ⟨_, _, _, hc⟩ := mk_cover_piece_cases x l PINF hP
    rcases hc with ⟨_, _, hE⟩ | ⟨_, hr, _⟩ | ⟨_, _, hE⟩ | ⟨_, hr, _⟩
    · exact absurd hE hNT
    · exact absurd rfl hr
    · rw [hE] at hB; exact (rel_args_same CovRel.gt (Or.inr rfl) x l hB).2
    · exact absurd rfl hr
  obtain ⟨T, hxTy, hT⟩ : ∃ T, __smtx_typeof (__eo_to_smt x) = T ∧
      (T = SmtType.Int ∨ T = SmtType.Real) := ⟨_, rfl, hxA⟩
  have hfB : ∀ f ∈ fs, RuleProofs.eo_has_bool_type f := by
    intro f hf
    obtain ⟨l', r', hp, rfl⟩ := h1 f hf
    exact (hgood l' r' hp).2.1
  obtain ⟨l', r', hp, hpT⟩ := sweep_sound M hM x T hxTy hT ps hgood ps false MINF
    (fun _ _ h => h) (Or.inl rfl) hsw (Or.inl rfl)
  have hmem := h2 l' r' hp
  by_cases hone : ∃ f, fs = [f]
  · rcases hone with ⟨f, rfl⟩
    rw [hS1 f rfl]
    have : __mk_cover_piece x l' r' = f := List.mem_singleton.mp hmem
    exact ⟨hfB f List.mem_cons_self, this ▸ hpT⟩
  · push Not at hone
    rw [hS2 hone]
    exact ⟨orChain_bool fs hfB, orChain_true M hM fs hfB ⟨_, hmem, hpT⟩⟩

public theorem cmd_step_cover_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cover args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cover args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cover args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.cover args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases args with _ | ⟨x, _ | ⟨ps, _ | ⟨_, _⟩⟩⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  rcases premises with _ | ⟨_, _⟩ <;>
    try (change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl))
  have hT := hCmdTrans
  simp only [cmdTranslationOk, cArgListTranslationOkMask, argTranslationOkMasked] at hT
  have hTy : __eo_typeof (__eo_prog_cover x ps) = Term.Bool := hResultTy
  have hSound := cover_sound M hM x ps hT.1 hT.2.1 hTy
  exact ⟨fun _ => hSound.2, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hSound.1⟩
