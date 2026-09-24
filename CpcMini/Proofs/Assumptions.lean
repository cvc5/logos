module

public import CpcMini.Spec
import all CpcMini.Spec
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.SmtModel
import all CpcMini.SmtModel

@[expose] public section

open Eo
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

/-- Predicate asserting that every argument in a checker argument list is translation-safe. -/
def cArgListTranslationOk : CArgList -> Prop
  | CArgList.nil => True
  | CArgList.cons a args => eoHasSmtTranslation a ∧ cArgListTranslationOk args

/-- Predicate asserting that a checker command meets the translation side conditions used by the rule proofs. -/
def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => eoHasSmtTranslation A
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
