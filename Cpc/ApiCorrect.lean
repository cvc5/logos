module

public import Cpc.ApiChecks
import all Cpc.ApiChecks
public import Cpc.Proofs.Checker
import all Cpc.Proofs.Checker

public section

/-!
# Soundness of the `logos` executable

`correct___eo_is_refutation` (`Cpc/Proofs/Checker.lean`) is stated about an
assumption list `F`, a `CCmdList`, and two side conditions.  The theorems below
restate it about what the executable actually runs:
`Eo.logos_check_proof` (`Cpc/Api.lean`), which takes the text of a proof file to
the word `logos` prints for it.

* `correct___logos_verdict` is about the verdict of a parsed proof.
* `correct___logos_check_proof` is about the file's text: if `logos` prints
  `correct` for it, the assumptions the parser read out of it are unsatisfiable.

Reading the theorem as a statement about a proof file therefore requires only
one thing beyond it: that `Cpc/Parser.lean` read the intended assumptions out of
the file.  That is what stays unverified -- the s-expression reader and parser
have no correctness proof, and `logos` does not compare a proof's assumptions
against an original input problem (`include` and `reference` commands are
ignored).  `Cpc/Native/Correct.lean` states the same theorem for the experimental
Lean-native front end (`MainNative.lean`), where what takes the place of the
parser is the shape of the script.
-/

open Eo
open SmtEval
open Smtm

/--
The checker's input list holds the parser's assumptions in reverse order
(`logos_assumption_arglist`).
-/
theorem argListTerms_logos_assumption_arglist (assums : List Term) :
    argListTerms (logos_assumption_arglist assums) = assums.reverse := by
  suffices h : ∀ acc : CArgList,
      argListTerms (assums.foldl logos_assumption_list_step acc) =
        assums.reverse ++ argListTerms acc by
    simpa [logos_assumption_arglist, argListTerms] using h CArgList.nil
  induction assums with
  | nil => intro acc; simp
  | cons A rest ih =>
      intro acc
      simp [ih, logos_assumption_list_step, argListTerms]

/--
Soundness of the verdict `Main.lean` computes: `correct` for a parsed proof means
every well-formed model evaluates one of its assumptions to `false`.

Each of the three checks `logos_verdict` runs discharges one hypothesis of
`correct___eo_is_refutation`, with no proof obligation left to the caller:

* `logos_check_translatableAssumptionList assums` gives
  `TranslatableAssumptionList (logos_assumption_arglist assums)`,
* `logos_check_cmdListTranslationOk cmds` gives `CmdListTranslationOk cmds`,
* `logos_check_refutation assums cmds` gives
  `eo_is_refutation (logos_assumption_arglist assums) cmds`.

The theorem's conclusion is about `argListTerms (logos_assumption_arglist assums)`,
which is `assums` reversed (`argListTerms_logos_assumption_arglist`), so it has
the same members.
-/
theorem correct___logos_verdict (assums : List Term) (cmds : CCmdList)
    (h : logos_verdict assums cmds = Verdict.correct) :
    ∀ M : SmtModel, model_wf M ->
      ∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
  obtain ⟨hRefutation, hAssums, hCmds⟩ := checks_of_verdict_correct assums cmds h
  intro M hM
  obtain ⟨A, hA, hFalse⟩ := correct___eo_is_refutation (logos_assumption_arglist assums) cmds
    (translatableAssumptionList_of_check assums hAssums)
    (cmdListTranslationOk_of_check cmds hCmds)
    (eo_is_refutation_of_check assums cmds hRefutation) M hM
  rw [argListTerms_logos_assumption_arglist, List.mem_reverse] at hA
  exact ⟨A, hA, hFalse⟩

/--
Soundness of the `logos` executable, stated about the proof file it reads.

If the parser reads the assumptions `assums` (and the commands `cmds`) out of
`input`, and `logos` prints `correct` for `input`, then every well-formed model
evaluates one of those assumptions to `false`.
-/
theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
    (hParse : parseProof input = Except.ok (assums, cmds))
    (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
    ∀ M : SmtModel, model_wf M ->
      ∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
  apply correct___logos_verdict assums cmds
  rw [logos_check_proof_of_parse input assums cmds hParse] at hCorrect
  exact Except.ok.inj hCorrect
