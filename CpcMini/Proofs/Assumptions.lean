module

public import CpcMini.Spec
import all CpcMini.Spec
public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.Proofs.ModelEval
import all CpcMini.Proofs.ModelEval
public import CpcMini.Proofs.CalculusAssumptions
import all CpcMini.Proofs.CalculusAssumptions

@[expose] public section

open Eo
open Smtm

/--
The formulas of an input assumption list, in order.

The checker takes a proof's assumptions as a `CArgList` and pushes them one at a
time.  This is what `stateAssumes` reads back off the state
`__eo_invoke_assume_list` builds from the list (`stateAssumes_invoke_assume_list`,
`Proofs/CheckerState.lean`): the head of the list is pushed last, which is where
`stateAssumes` then finds it.

Soundness is stated about `argListAssumes F`, the one formula the calculus says
the list stands for (`Proofs/CalculusAssumptions.lean`); the checker itself only
ever reasons about this list.
-/
def argListTerms : CArgList -> List Term
  | CArgList.nil => []
  | CArgList.cons A as => A :: argListTerms as

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
