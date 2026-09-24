module

public import Cpc.Logos
import all Cpc.Logos
public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Parser
import all Cpc.Parser
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

@[expose] public section

/-!
# What the `logos` executable computes

This module is everything the `logos` executable does with a proof file, from
the file's text to its verdict:

```
logos_check_proof : String -> Except String Verdict
```

`Main.lean` only reads the file, prints the verdict and picks an exit status;
`Cpc/ApiCorrect.lean` states the correctness of the executable about this
function.

The pipeline has two stages.  `Cpc/Parser.lean` turns the text into a `List Term`
of assumptions and a `CCmdList` of commands -- this stage is unverified, so the
correctness theorem is about the assumptions *as parsed*, whatever they are.
`logos_verdict` then runs the three checks below on that output, one for each
component of `correct___eo_is_refutation` (`Cpc/Proofs/Checker.lean`):

```
theorem correct___eo_is_refutation (F : CArgList) (pf : CCmdList) :
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  eo_satisfiability (argListAssumes F) false
```

| component of the theorem        | computed here by                           |
| ------------------------------- | ------------------------------------------ |
| the list `F`                    | `logos_assumption_arglist assums`          |
| `eo_is_refutation F pf`         | `logos_check_refutation assums cmds`       |
| `TranslatableAssumptionList F`  | `logos_check_translatableAssumptionList`   |
| `CmdListTranslationOk pf`       | `logos_check_cmdListTranslationOk`         |

`logos_assumption_term assums` is `argListAssumes` of that list: the formula the
correctness of the executable is ultimately about.

Nothing here is trusted: `Cpc/ApiChecks.lean` proves that each check gives the
component it stands for, and `Cpc/ApiCorrect.lean` assembles those into
`correct___logos_check_proof`.

The two translation side conditions are not re-implemented here.  They are the
predicates of `Cpc/Proofs/Assumptions.lean`, decided by the `Decidable`
instances that file derives from them, so that the executable checks the same
per-rule masks the rule proofs assume, with no second copy to keep in sync.

`Cpc/Native.lean` is the same pipeline for the Lean-native front end
(`MainNative.lean`, and the `#eval` scripts cvc5 emits for it), whose input
names its assumptions and commands directly instead of parsing them.  It runs
the three checks below on what a script names, reusing the definitions here.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The assumptions the parser produced, as the checker's input list -/

/-- One link of the assumption list: `A` in front of the assumptions already read. -/
def logos_assumption_list_step (rest : CArgList) (A : Term) : CArgList :=
  CArgList.cons A rest

/--
The parser's assumptions as the checker takes them: the `F` of
`correct___eo_is_refutation`.

The order is not the obvious one.  `__eo_invoke_assume_list` consumes the list by
pushing its head *last*, so the head ends up on top of the proof stack.  The
parser numbers premises against a stack whose *first* assumption is at the bottom
(`registerStep` and `parsePremise` in `Logos/Parser.lean`), so the list that
matches the parser's numbering holds the assumptions in reverse file order: for
assumptions `A1 ... An` this builds

    [An, A(n-1), ..., A1]

which `__eo_invoke_assume_list` pushes as `A1` first and `An` on top.  Building
the list the other way round cannot silently accept a bad proof -- premise
indices then resolve to the wrong stack entries and the checker rejects -- but
it would make the theorem talk about a different `F`.

Nothing at run time builds this list either: `logos_check_refutation` folds the
guarded push over the parser's list instead, and `invoke_assume_list_eq_fold`
(`Cpc/ApiChecks.lean`) proves the two agree.
-/
def logos_assumption_arglist (assums : List Term) : CArgList :=
  assums.foldl logos_assumption_list_step CArgList.nil

/--
The conjunction of the parser's assumptions: the term the correctness of the
executable is ultimately about.

`correct___eo_is_refutation` concludes `eo_satisfiability (argListAssumes F) false`
for the list `F` it was run on, and this is that term for the list the parser
produced -- for assumptions `A1 ... An`,

    (and An (and A(n-1) ... (and A1 true) ... ))
-/
def logos_assumption_term (assums : List Term) : Term :=
  argListAssumes (logos_assumption_arglist assums)

/--
The checker state a run starts in: nothing assumed, nothing proven.

An alias for `CState.nil`, so that the statements below and the theorems
`Cpc/ApiChecks.lean` proves about them do not have to name a constructor of the
checker's internal state.  `Eo.logos_init_state` (`Cpc/Native.lean`) is the
front-end state a Lean-native script starts from, whose checker state this is.
-/
def logos_checker_init_state : CState := CState.nil

/--
Push one input assumption, applying the well-formedness guard that
`__eo_invoke_assume_list` applies to each element of the input list: the
assumption must be Boolean-typed and closed, or the state goes `Stuck`.

The guard is not cosmetic:
`__eo_typeof A = Term.Bool` for `assume` entries is what `checkerTypeInvariant`
requires (`Cpc/Proofs/CheckerCore.lean`), and closedness is what yields
`StableAssumptionList`, so dropping it puts the run outside the reach of the
soundness proof.
-/
def logos_invoke_input_assume (s : CState) (A : Term) : CState :=
  __eo_push_input_assume_check (__eo_and (__eo_is_bool_type A) (__eo_is_closed A)) A s

/-! ## The three checks

The first is the checker run itself.  The other two are the side conditions
`correct___eo_is_refutation` assumes: the rule proofs only interpret an EO term
through `__eo_to_smt`, so terms with no SMT-LIB counterpart are excluded.  Both
are `decide` applied to the predicate of `Cpc/Proofs/Assumptions.lean` that the
theorem uses, which is what keeps them from drifting away from it.
-/

/--
Logos runs `cmds` from the parser's assumptions and ends in a closed state that
has proven `false`.  `logos_check_refutation_eq_checker` (`Cpc/ApiChecks.lean`)
proves

    logos_check_refutation assums cmds
      = __eo_checker_is_refutation (logos_assumption_arglist assums) cmds

so this returning `true` is exactly `eo_is_refutation (logos_assumption_arglist assums) cmds`.
The fold needs no stack, while `__eo_invoke_assume_list` recurses once per
assumption.
-/
def logos_check_refutation (assums : List Term) (cmds : CCmdList) : Bool :=
  __eo_state_is_refutation
    (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_checker_init_state) cmds)

/--
Every assumption has an SMT-LIB translation.  `translatableAssumptionList_of_check`
(`Cpc/ApiChecks.lean`) turns this into `TranslatableAssumptionList
(logos_assumption_arglist assums)`, the first hypothesis of
`correct___eo_is_refutation`.
-/
def logos_check_translatableAssumptionList (assums : List Term) : Bool :=
  assums.all fun A => decide (eoHasSmtTranslation A)

/--
`CmdListTranslationOk cmds`, the second hypothesis of
`correct___eo_is_refutation`, decided by the instance in
`Cpc/Proofs/Assumptions.lean`.
-/
def logos_check_cmdListTranslationOk (cmds : CCmdList) : Bool :=
  decide (CmdListTranslationOk cmds)

/-! ## The verdict -/

/-- What the executable reports about a proof file. -/
inductive Verdict where
  /-- The proof's assumptions are unsatisfiable, by `correct___logos_check_proof`. -/
  | correct
  /-- Logos does not accept the proof as a refutation. -/
  | incorrect
  /--
  Logos accepts the proof, but a side condition of `correct___eo_is_refutation`
  fails on it: the proof is a valid CPC derivation that mentions something the
  specification of SMT-LIB semantics does not model, so the theorem says nothing
  about it.
  -/
  | incomplete
deriving DecidableEq, Repr, Inhabited

/-- The verdict for a parsed proof: `correct` exactly when all three checks pass. -/
def logos_verdict (assums : List Term) (cmds : CCmdList) : Verdict :=
  if !logos_check_refutation assums cmds then Verdict.incorrect
  else if !logos_check_translatableAssumptionList assums then Verdict.incomplete
  else if !logos_check_cmdListTranslationOk cmds then Verdict.incomplete
  else Verdict.correct

/-- Parse a proof file and report its verdict: everything `Main.lean` does. -/
def logos_check_proof (input : String) : Except String Verdict :=
  match parseProof input with
  | Except.ok (assums, cmds) => Except.ok (logos_verdict assums cmds)
  | Except.error e => Except.error e

/-! ## Diagnostics

Used only to report *why* a proof fell outside the fragment the specification
covers, once `logos_verdict` has already returned `incomplete`.  They have no
role in the correctness statement.
-/

/-- The first assumption with no SMT-LIB translation, with its position in file order. -/
def logos_untranslatable_assumption (assums : List Term) : Option (Nat × Term) :=
  go 0 assums
where
  go : Nat -> List Term -> Option (Nat × Term)
    | _, [] => none
    | i, A :: assums => if eoHasSmtTranslation A then go (i + 1) assums else some (i, A)

/--
The first command whose arguments fail their translation side condition, with its
position in file order among the proof-stack commands.
-/
def logos_untranslatable_cmd (cmds : CCmdList) : Option (Nat × CCmd) :=
  go 0 cmds
where
  go : Nat -> CCmdList -> Option (Nat × CCmd)
    | _, CCmdList.nil => none
    | i, CCmdList.cons c cmds => if cmdTranslationOk c then go (i + 1) cmds else some (i, c)

end Eo
