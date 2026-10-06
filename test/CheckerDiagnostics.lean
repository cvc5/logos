import Cpc.Diagnostics

open Eo

private def diagnostic (proof : String) : String :=
  match parseProof proof with
  | .ok (assums, cmds) => logos_checker_failure_detail proof assums cmds
  | .error e => e

private def declarationsAndAssumptions : String :=
  "(declare-const x Int)
   (declare-const y Int)
   (assume @p0 (= y x))
   (assume @p1 (not (= x y)))"

-- A command that makes the checker stuck is identified by its source step ID.
#guard (diagnostic (declarationsAndAssumptions ++
    "(step @p2 :rule symm :premises ())
     (step @p3 :rule contra :premises (@p0 @p2))")).startsWith
  "Error: the checker became stuck at step @p2 (proof command 1):"

-- If no command gets stuck, report that it is the final refutation check that failed.
#guard diagnostic (declarationsAndAssumptions ++
    "(step @p2 :rule symm :premises (@p1))") ==
  "Error: every proof command executed without getting stuck, but the final state after step @p2 \
   is not a closed proof of false."

-- A step stating its conclusion is two proof commands, the step and the check of
-- that conclusion, so a wrong one is reported at its check and the commands after
-- it keep their own labels.
#guard (diagnostic (declarationsAndAssumptions ++
    "(step @p2 (= x x) :rule symm :premises (@p1))
     (step @p3 :rule contra :premises (@p0 @p2))")).startsWith
  "Error: the checker became stuck at the conclusion of step @p2 (proof command 2):"
#guard (diagnostic (declarationsAndAssumptions ++
    "(step @p2 (not (= y x)) :rule symm :premises (@p1))
     (step @p3 :rule symm :premises ())")).startsWith
  "Error: the checker became stuck at step @p3 (proof command 3):"
#guard diagnostic (declarationsAndAssumptions ++
    "(step @p2 (not (= y x)) :rule symm :premises (@p1))") ==
  "Error: every proof command executed without getting stuck, but the final state after step @p2 \
   is not a closed proof of false."

private def verdict (proof : String) : Option Verdict :=
  match logos_check_proof proof with
  | .ok v => some v
  | .error _ => none

-- A stated conclusion is checked against the one the rule derives: a refutation
-- whose last step states something other than what `contra` proves is not one.
#guard (verdict (declarationsAndAssumptions ++
    "(step @p2 (not (= y x)) :rule symm :premises (@p1))
     (step @p3 false :rule contra :premises (@p0 @p2))") matches some .correct)
#guard (verdict (declarationsAndAssumptions ++
    "(step @p2 (not (= y x)) :rule symm :premises (@p1))
     (step @p3 (= 1 2) :rule contra :premises (@p0 @p2))") matches some .incorrect)
#guard (verdict (declarationsAndAssumptions ++
    "(step @p2 (not (= x x)) :rule symm :premises (@p1))
     (step @p3 false :rule contra :premises (@p0 @p2))") matches some .incorrect)
