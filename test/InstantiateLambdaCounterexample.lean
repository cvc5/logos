module

public import Cpc.Logos
public import Cpc.SmtTranslate
public import Cpc.SmtTyping
public import Cpc.TranslationChecks
import all Cpc.Logos
import all Cpc.SmtTranslate
import all Cpc.SmtTyping
import all Cpc.TranslationChecks

/-!
Regression test: `instantiate` with a saturated lambda of function type.

Run with:
  lake env lean -j1 -DwarningAsError=true test/InstantiateLambdaCounterexample.lean

Let `actual = ((lambda (u : Bool) g) false)`, where `g : Bool -> Bool`.
The saturated lambda translates to a parallel let and has function type.
Instantiating `forall (f : Bool -> Bool). f true` with `actual` produces
`actual true`. Under the earlier lambda-spine translation that result had no
SMT translation, since the spine rejected the extra argument. Each
application is now translated from what its function and argument translate
to, so `actual true` is the SMT application of the let to `true`, of type
Bool. All computations below are checked by Lean's kernel.
-/

public section

open Eo SmtEval Smtm

namespace InstantiateLambdaCounterexample

def boolFun : Term := .Apply (.Apply .FunType .Bool) .Bool
def u : Term := .Var (.String (native_string_lit "u")) .Bool
def us : Term := .Apply (.Apply .__eo_List_cons u) .__eo_List_nil
def g : Term := .UConst 0 boolFun
def actual : Term :=
  .Apply (.Apply (.Apply (.UOp .lambda) us) g) (.Boolean false)

def f : Term := .Var (.String (native_string_lit "f")) boolFun
def xs : Term := .Apply (.Apply .__eo_List_cons f) .__eo_List_nil
def ss : Term := .Apply (.Apply .__eo_List_cons actual) .__eo_List_nil
def body : Term := .Apply f (.Boolean true)
def premise : Term := .Apply (.Apply (.UOp .forall) xs) body
def result : Term := __eo_prog_instantiate ss (.pf premise)

theorem actual_eo_type : __eo_typeof actual = boolFun := by decide +kernel

theorem actual_smt_type :
    __smtx_typeof (__eo_to_smt actual) = .FunType .Bool .Bool := by
  decide +kernel

theorem premise_smt_type : __smtx_typeof (__eo_to_smt premise) = .Bool := by
  decide +kernel

theorem instantiation_guard : __is_instantiation xs ss = .Boolean true := by
  decide +kernel

theorem binder_type_wf : __smtx_type_wf (__eo_to_smt_type boolFun) = true := by
  decide +kernel

theorem command_translation_ok :
    cmdTranslationOk (.step .instantiate (.cons ss .nil) (.cons 0 .nil)) := by
  decide +kernel

theorem result_eq : result = .Apply actual (.Boolean true) := by
  have hType : __eo_typeof actual = boolFun := actual_eo_type
  simp [result, hType, boolFun, premise, ss, xs, body, f,
    __eo_prog_instantiate, __is_instantiation, __substitute_simul_rec,
    __eo_list_find, __eo_list_find_rec, __assoc_nil_nth, __eo_requires,
    __eo_ite, __eo_is_neg, __eo_is_list, __eo_get_nil_rec, __eo_is_ok,
    __eo_is_list_nil, __eo_eq, native_zlt, __eo_mk_apply, __is_closed_rec,
    native_teq, native_ite, native_not]
  rfl

theorem result_eo_type : __eo_typeof result = .Bool := by
  rw [result_eq]
  decide +kernel

theorem result_translation :
    __eo_to_smt result = .Apply (__eo_to_smt actual) (.Boolean true) := by
  rw [result_eq]
  rfl

theorem result_smt_type_bool :
    __smtx_typeof (__eo_to_smt result) = .Bool := by
  rw [result_eq]
  decide +kernel

/-- The instantiation of a Boolean-translatable premise with this actual has
an SMT translation at the type of its EO result. -/
theorem no_counterexample :
    cmdTranslationOk (.step .instantiate (.cons ss .nil) (.cons 0 .nil)) ∧
    __smtx_typeof (__eo_to_smt premise) = .Bool ∧
    __is_instantiation xs ss = .Boolean true ∧
    __eo_typeof result = .Bool ∧
    __smtx_typeof (__eo_to_smt result) = .Bool :=
  ⟨command_translation_ok, premise_smt_type, instantiation_guard,
    result_eo_type, result_smt_type_bool⟩

end InstantiateLambdaCounterexample
