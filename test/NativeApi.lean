import Cpc.Native

/-!
The experimental Lean-native front end runs the same checks as `logos`.

`Cpc/Native.lean` proves that a script of the shape `logos-native` expects
computes `Eo.logos_verdict` of the assumptions and commands it names.  These
tests use `Cpc/Parser.lean` only to build the terms conveniently; what they check
is what a script does with them -- in particular that the two side conditions and
the assumption guard, which the generated checker API did not apply, reject the
proofs `logos` does not report `correct` for.
-/

open Eo

private def parsed (proof : String) : List Term × CCmdList :=
  match parseProof proof with
  | .ok p => p
  | .error _ => ([], CCmdList.nil)

/-- What a script that names the assumptions and commands of `proof` evaluates. -/
private def nativeAccepts (proof : String) : Bool :=
  let (assums, cmds) := parsed proof
  logos_state_is_refutation (logos_run assums cmds)

/-- What `logos` reports for the same proof. -/
private def verdict (proof : String) : Verdict :=
  let (assums, cmds) := parsed proof
  logos_verdict assums cmds

/-- The checker run alone, which is what a script used to evaluate. -/
private def uncheckedAccepts (proof : String) : Bool :=
  let (assums, cmds) := parsed proof
  __eo_state_is_refutation
    (__eo_invoke_cmd_list
      (assums.foldl (fun s A => CState.cons (CStateObj.assume A) s) CState.nil) cmds)

private def isStuck : LogosState -> Bool
  | { state := CState.Stuck, .. } => true
  | _ => false

private def refutation : String :=
  "(declare-const x Int)
   (declare-const y Int)
   (assume @p0 (= y x))
   (assume @p1 (not (= x y)))
   (step @p2 :rule symm :premises (@p1))
   (step @p3 :rule contra :premises (@p0 @p2))"

-- A refutation is accepted, and `logos` calls it `correct`.
#guard nativeAccepts refutation
#guard verdict refutation == Verdict.correct

-- A derivation that does not end in `false` is not.
#guard !nativeAccepts
  "(declare-const x Int)
   (declare-const y Int)
   (assume @p0 (= y x))
   (step @p1 :rule symm :premises (@p0))"

/--
The proof of `test/regress/sexp/test-declare-sort.cpc`: Logos accepts it as a CPC
derivation, but `(Box U)` -- a declared sort constructor applied to a sort -- has
no counterpart in `Cpc/SmtModel.lean`, so the side conditions of
`correct___eo_is_refutation` do not hold of it and `logos` reports `incomplete`.
-/
private def untranslatable : String :=
  "(declare-sort U 0)
   (declare-sort Box 1)
   (declare-fun f ((Box U)) U)
   (declare-const b (Box U))
   (assume @p0 (not (= (f b) (f b))))
   (step @p1 :rule refl :args ((f b)))
   (step @p2 :rule contra :premises (@p1 @p0))"

-- The checker accepts it, so a script used to evaluate to `true`, ...
#guard uncheckedAccepts untranslatable
-- ... and now evaluates to `false`, with the `incomplete` `logos` reports for it.
#guard !nativeAccepts untranslatable
#guard logos_state_verdict (logos_run (parsed untranslatable).1 (parsed untranslatable).2)
  == Verdict.incomplete
#guard verdict untranslatable == Verdict.incomplete

-- An input assumption that is not Boolean-typed makes the checker state `Stuck`, and
-- nothing pushed on top of it is ever a refutation.
private def nonBooleanAssumption : Term :=
  (parsed "(declare-const x Int)
           (assume @p0 x)").1.head!

#guard isStuck (logos_invoke_assume logos_init_state nonBooleanAssumption)
#guard !logos_state_is_refutation
  (logos_invoke_assume (logos_invoke_assume logos_init_state nonBooleanAssumption)
    (parsed refutation).1.head!)
