module

public import CpcMini.Logos
import all CpcMini.Logos

/-!
# The formula an input assumption list stands for

Supplied by the calculus, not by the checker.  The checker reads a proof's
assumptions as a list of formulas and names no operator of the calculus;
`correct___eo_is_refutation` is stated about the single term `argListAssumes F`
defined here.  What the checker needs to know about it is proved in
`Proofs/RuleSupport/CalculusAssumptions.lean`.

This calculus has `and`, so the term is the conjunction of the list.
-/

@[expose] public section

open Eo

/--
The conjunction of an input assumption list, as one term: for the list
`A1 ... An` it is `(and A1 (and A2 ... (and An true) ... ))`.

Nothing the checker runs builds this term.
-/
def argListAssumes : CArgList -> Term
  | CArgList.nil => Term.Boolean true
  | CArgList.cons A as =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (argListAssumes as)
