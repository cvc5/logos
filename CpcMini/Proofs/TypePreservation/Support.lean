module

public import CpcMini.Proofs.TypePreservation.Common
import all CpcMini.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

namespace Smtm

/-- Inductive predicate describing the SMT terms covered by the type-preservation proof. -/
inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : native_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : native_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : native_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | string (s : native_String) : supported_preservation_term (SmtTerm.String s)
  | binary (w n : native_Int) : supported_preservation_term (SmtTerm.Binary w n)
  | var (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.UConst s T)
  | ite {c t1 t2 : SmtTerm}
      (htc : term_has_non_none_type c)
      (hsc : supported_preservation_term c)
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term
        (SmtTerm.ite c t1 t2)
  | not {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.not t)
  | or {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.or t1 t2)
  | and {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.and t1 t2)
  | imp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.imp t1 t2)
  | eq (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.eq t1 t2)
  | dt_cons (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
      supported_preservation_term (SmtTerm.DtCons s d i)
  | dt_sel {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat} {x : SmtTerm}
      (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
      (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
      (hWrongMapWF :
        __smtx_type_wf
          (SmtType.Map SmtType.Int
            (SmtType.Map SmtType.Int
              (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)
  | dt_tester (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) (x : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtTester s d i) x)
  | apply {f x : SmtTerm}
      (hTy : generic_apply_type f x)
      (hEval : generic_apply_eval f x)
      (htf : term_has_non_none_type f)
      (hsf : supported_preservation_term f)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply f x)

end Smtm
