module

public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtModel
import all Cpc.SmtModel

@[expose] public section

open Eo
open SmtEval
open Smtm

/--
The conjunction of an input assumption list, as one term.

The checker takes a proof's assumptions as a `CArgList` and pushes them one at a
time, so nothing it runs builds this term.  Soundness is a statement about the
formula those assumptions stand for, and that is this `and`-chain: it is what
`stateAssumes` reads back off the state `__eo_invoke_assume_list` builds from the
list (`stateAssumes_invoke_assume_list`, `Proofs/CheckerState.lean`), and it is
the term `correct___eo_is_refutation` concludes about.

The head of the list is the outermost conjunct because `__eo_invoke_assume_list`
pushes it last, which is where `stateAssumes` then finds it.
-/
def argListAssumes : CArgList -> Term
  | CArgList.nil => Term.Boolean true
  | CArgList.cons A as =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (argListAssumes as)

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eoHasSmtTranslation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that every element of an EO list has an SMT translation. -/
def EoListAllHaveSmtTranslation : Term -> Prop
  | Term.__eo_List_nil => True
  | Term.Apply (Term.Apply Term.__eo_List_cons t) ts =>
      eoHasSmtTranslation t ∧ EoListAllHaveSmtTranslation ts
  | _ => False

/-- Classifies checker rule arguments by the translation side condition they require. -/
inductive ArgTranslationKind where
  | term
  | list
  | type
  /-- A value argument whose translated result type must itself be a full
      well-formed SMT type. This is weaker than `wfElem` for top-level function
      and regex types, but strong enough for EO typed-list annotations. -/
  | wfTerm
  /-- A value argument that the rule's conclusion places into a container element
      position (e.g. `set.singleton`/`seq.unit`). Requires the argument's value type
      to be well-formed *as a container element* (`__smtx_type_wf_component`), which is
      strictly stronger than `term`: it additionally rules out element types such as
      `RegLan` that have a translation but cannot inhabit a `Set`/`Seq`. -/
  | wfElem

/-- Interprets a command-argument mask entry. -/
def argTranslationOkMasked : ArgTranslationKind -> Term -> Prop
  | ArgTranslationKind.term, t => eoHasSmtTranslation t
  | ArgTranslationKind.list, t => EoListAllHaveSmtTranslation t
  | ArgTranslationKind.type, t => __smtx_type_wf (__eo_to_smt_type t) = true
  | ArgTranslationKind.wfTerm, t =>
      eoHasSmtTranslation t ∧ __smtx_type_wf (__smtx_typeof (__eo_to_smt t)) = true
  | ArgTranslationKind.wfElem, t =>
      __smtx_type_wf_component (__smtx_typeof (__eo_to_smt t)) = true

/-- Predicate asserting that every argument in a checker argument list is translation-safe. -/
def cArgListTranslationOk : CArgList -> Prop
  | CArgList.nil => True
  | CArgList.cons a args => eoHasSmtTranslation a ∧ cArgListTranslationOk args

/-- Predicate asserting that a checker argument list matches a translation mask. -/
def cArgListTranslationOkMask : List ArgTranslationKind -> CArgList -> Prop
  | [], CArgList.nil => True
  | kind :: mask, CArgList.cons a args =>
      argTranslationOkMasked kind a ∧ cArgListTranslationOkMask mask args
  | _, _ => False

/-- Predicate asserting that a checker command meets the translation side conditions used by the rule proofs. -/
def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => eoHasSmtTranslation A
  | CCmd.step CRule.chain_resolution args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.list, ArgTranslationKind.list] args
  | CCmd.step CRule.chain_m_resolution args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.instantiate args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.list] args
  | CCmd.step CRule.alpha_equiv args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.distinct_binary_elim args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.wfTerm, ArgTranslationKind.term] args
  | CCmd.step CRule.exists_string_length args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.type, ArgTranslationKind.term,
        ArgTranslationKind.term] args
  | CCmd.step CRule.sets_eq_singleton_emp args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_member_emp args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp1 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp2 args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_self args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.sets_is_empty_elim args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_range args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start_neg args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_substr_start_geq_len args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base_rev args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_contains_char args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_concat_rec args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_base args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_indexof_self args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_char_start_eq_len args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_member_singleton args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.term, ArgTranslationKind.wfElem] args
  | CCmd.step CRule.sets_choose_singleton args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_len_unit args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_rev_unit args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_nth_unit args _ =>
      cArgListTranslationOkMask [ArgTranslationKind.wfElem] args
  | CCmd.step _ args _ => cArgListTranslationOk args
  | _ => True

/--
Every entry of an input assumption list has an SMT translation: the first side
condition of `correct___eo_is_refutation`.

A proof's input assumptions reach the checker as a `CArgList`, the same list type
a rule's arguments come in, so this is `cArgListTranslationOk` under the name the
soundness statement uses for it rather than a second copy of it.
-/
abbrev TranslatableAssumptionList : CArgList -> Prop := cArgListTranslationOk

/-- Inductive predicate asserting that every command in a checker command list satisfies `cmdTranslationOk`. -/
inductive CmdListTranslationOk : CCmdList -> Prop
  | nil : CmdListTranslationOk CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdTranslationOk c ->
      CmdListTranslationOk cs ->
      CmdListTranslationOk (CCmdList.cons c cs)

/-! ## Deciding the side conditions

The executable has to decide the predicates above at run time: `Cpc/Api.lean`
runs `decide (cmdTranslationOk c)` and `decide (eoHasSmtTranslation A)` on the
parser's output, and `Cpc/ApiChecks.lean` turns those into the hypotheses of
`correct___eo_is_refutation`.

The instances are *derived from* the definitions above rather than restating
them, so there is no second copy of the side conditions to keep in sync -- in
particular no second copy of the per-rule masks of `cmdTranslationOk`.  A rule
whose mask is added or changed here is checked that way by the executable as
soon as it is written down.  Deriving them is why this section is `@[expose]`:
a `Decidable` instance is data, and data may not depend on a definition whose
body the module does not export.
-/

/-- Decides `eoHasSmtTranslation`. -/
instance instDecidableEoHasSmtTranslation (t : Term) : Decidable (eoHasSmtTranslation t) := by
  unfold eoHasSmtTranslation; infer_instance

/--
Decides `EoListAllHaveSmtTranslation`.

`EoListAllHaveSmtTranslation` recurses through a `Term` rather than a `List`, and
its last case is a catch-all, so the decision procedure is written out as a
`Bool` function whose branches match it and is tied to the predicate by
`eoListAllHaveSmtTranslationB_iff`, rather than derived branch by branch.
-/
def eoListAllHaveSmtTranslationB : Term -> Bool
  | Term.__eo_List_nil => true
  | Term.Apply (Term.Apply Term.__eo_List_cons t) ts =>
      decide (eoHasSmtTranslation t) && eoListAllHaveSmtTranslationB ts
  | _ => false

theorem eoListAllHaveSmtTranslationB_iff :
    ∀ t : Term, eoListAllHaveSmtTranslationB t = true ↔ EoListAllHaveSmtTranslation t := by
  intro t
  fun_induction eoListAllHaveSmtTranslationB t <;> simp_all [EoListAllHaveSmtTranslation]

instance instDecidableEoListAllHaveSmtTranslation (t : Term) :
    Decidable (EoListAllHaveSmtTranslation t) :=
  decidable_of_iff _ (eoListAllHaveSmtTranslationB_iff t)

/-- Decides `argTranslationOkMasked`, one case per kind. -/
instance instDecidableArgTranslationOkMasked (k : ArgTranslationKind) (t : Term) :
    Decidable (argTranslationOkMasked k t) := by
  unfold argTranslationOkMasked; split <;> infer_instance

/-- Decides `cArgListTranslationOk`. -/
instance instDecidableCArgListTranslationOk :
    (args : CArgList) -> Decidable (cArgListTranslationOk args)
  | CArgList.nil => isTrue trivial
  | CArgList.cons a args =>
      have := instDecidableCArgListTranslationOk args
      inferInstanceAs (Decidable (eoHasSmtTranslation a ∧ cArgListTranslationOk args))

/-- Decides `cArgListTranslationOkMask`; a mask and an argument list of different lengths fail. -/
instance instDecidableCArgListTranslationOkMask :
    (mask : List ArgTranslationKind) -> (args : CArgList) ->
      Decidable (cArgListTranslationOkMask mask args)
  | [], CArgList.nil => isTrue trivial
  | k :: mask, CArgList.cons a args =>
      have := instDecidableCArgListTranslationOkMask mask args
      inferInstanceAs
        (Decidable (argTranslationOkMasked k a ∧ cArgListTranslationOkMask mask args))
  | [], CArgList.cons _ _ => isFalse not_false
  | _ :: _, CArgList.nil => isFalse not_false

/--
Decides `cmdTranslationOk`, one case per case of the definition -- including the
per-rule masks, which are read off `cmdTranslationOk` itself.
-/
instance instDecidableCmdTranslationOk (c : CCmd) : Decidable (cmdTranslationOk c) := by
  unfold cmdTranslationOk; split <;> infer_instance

/-- Decides `CmdListTranslationOk`. -/
instance instDecidableCmdListTranslationOk :
    (cmds : CCmdList) -> Decidable (CmdListTranslationOk cmds)
  | CCmdList.nil => isTrue CmdListTranslationOk.nil
  | CCmdList.cons c cmds =>
      if hc : cmdTranslationOk c then
        match instDecidableCmdListTranslationOk cmds with
        | isTrue hcs => isTrue (CmdListTranslationOk.cons c cmds hc hcs)
        | isFalse hcs => isFalse fun h => hcs (by cases h; assumption)
      else isFalse fun h => hc (by cases h; assumption)
