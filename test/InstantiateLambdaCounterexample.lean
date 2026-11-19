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
Counterexample to SMT-translatability preservation by `instantiate`.

Run with:
  lake env lean -j1 -DwarningAsError=true test/InstantiateLambdaCounterexample.lean

Let `actual = ((lambda (u : Bool) g) false)`, where `g : Bool -> Bool`.
The saturated lambda translates to a parallel let and has function type.
Instantiating `forall (f : Bool -> Bool). f true` with `actual` passes the
instantiation and command-translation guards, and produces an EO Bool.
However, its result `actual true` has no SMT translation: lambda-spine
translation rejects the additional application of the returned function.

This refutes the unconditional translation-preservation obligation, without
assuming that the universally quantified premise is true in any model.
All computations below are checked by Lean's kernel.
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

theorem result_translation_none : __eo_to_smt result = .None := by
  rw [result_eq]
  decide +kernel

theorem result_smt_type_none :
    __smtx_typeof (__eo_to_smt result) = .None := by
  rw [result_translation_none]
  decide +kernel

/-- A valid instantiate command with a Boolean-translatable premise and an
EO Boolean result can still produce a result without an SMT type. -/
theorem counterexample :
    cmdTranslationOk (.step .instantiate (.cons ss .nil) (.cons 0 .nil)) ∧
    __smtx_typeof (__eo_to_smt premise) = .Bool ∧
    __is_instantiation xs ss = .Boolean true ∧
    __eo_typeof result = .Bool ∧
    __smtx_typeof (__eo_to_smt result) = .None :=
  ⟨command_translation_ok, premise_smt_type, instantiation_guard,
    result_eo_type, result_smt_type_none⟩

end InstantiateLambdaCounterexample
