module

public import Cpc.Api

public section

namespace Eo

/-!
Checker diagnostics are a separate replay used only after the ordinary verdict
is `incorrect`.  The verdict and the correctness-critical checking pipeline do
not depend on this code.
-/

inductive CheckerFailure where
  | assumption (index : Nat) (term : Term)
  | command (index : Nat) (cmd : CCmd)
  | finalCheck

/-- Run assumptions until the first one makes the checker state stuck. -/
private def runAssumptions (assums : List Term) : Except (Nat × Term) CState :=
  go 0 logos_checker_init_state assums
where
  go (i : Nat) (state : CState) : List Term → Except (Nat × Term) CState
    | [] => .ok state
    | A :: assums =>
      let state := logos_invoke_input_assume state A
      match state with
      | .Stuck => .error (i, A)
      | state => go (i + 1) state assums

/-- Run proof commands until the first one makes the checker state stuck. -/
private def runCommands (state : CState) (cmds : CCmdList) : Except (Nat × CCmd) CState :=
  go 0 state cmds
where
  go (i : Nat) (state : CState) : CCmdList → Except (Nat × CCmd) CState
    | .nil => .ok state
    | .cons cmd cmds =>
      let state := __eo_invoke_cmd state cmd
      match state with
      | .Stuck => .error (i, cmd)
      | state => go (i + 1) state cmds

/-- Why the checker rejected a parsed proof, found by a diagnostic-only replay. -/
def logos_checker_failure (assums : List Term) (cmds : CCmdList) : Option CheckerFailure :=
  match runAssumptions assums with
  | .error (i, A) => some (.assumption i A)
  | .ok state =>
    match runCommands state cmds with
    | .error (i, cmd) => some (.command i cmd)
    | .ok state => if __eo_state_is_refutation state then none else some .finalCheck

/-- The source labels of the commands represented in `CCmdList`, in the same order. -/
private def proofCommandLabels (proof : String) : List String :=
  match Logos.Sexp.Parser.manySexps!.run proof with
  | .error _ => []
  | .ok ss => ss.filterMap label?
where
  label? : Logos.Sexp → Option String
    | .expr (.atom "assume-push" :: .atom name :: _) => some s!"assume-push {name}"
    | .expr (.atom "step" :: .atom name :: _) => some s!"step {name}"
    | .expr (.atom "step-pop" :: .atom name :: _) => some s!"step-pop {name}"
    | _ => none

/-- Keep diagnostics readable when the offending command is large. -/
private def abbreviate (s : String) : String :=
  if s.length ≤ 400 then s else String.ofList (s.toList.take 400) ++ " ..."

/-- A source-level description of the first checker failure. -/
def logos_checker_failure_detail (proof : String) (assums : List Term) (cmds : CCmdList) :
    String :=
  let labels := proofCommandLabels proof
  match logos_checker_failure assums cmds with
  | some (.assumption i A) =>
    s!"Error: the checker became stuck while loading assumption {i + 1}:\n  \
       {abbreviate (toString (repr A))}"
  | some (.command i cmd) =>
    let location := match labels[i]? with
      | some label => label
      | none => s!"proof command {i + 1}"
    s!"Error: the checker became stuck at {location} (proof command {i + 1}):\n  \
       {abbreviate (toString (repr cmd))}"
  | some .finalCheck =>
    let after := match labels.reverse.head? with
      | some label => s!" after {label}"
      | none => ""
    s!"Error: every proof command executed without getting stuck, but the final state{after} \
       is not a closed proof of false."
  | none => "Error: the checker rejected the proof, but the diagnostic replay succeeded."

end Eo
