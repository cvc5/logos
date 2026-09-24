import Cpc.Native
open Eo
def t1 := (Term.UConst 1 (Term.UOp UserOp.Int))
def t2 := (Term.UConst 2 (Term.UOp UserOp.Int))
def t3 := (Term.Apply (Term.UOp UserOp.eq) t2)
def t4 := (Term.Apply t3 t1)
def t5 := (Term.Apply (Term.UOp UserOp.eq) t1)
def t6 := (Term.Apply t5 t2)
def t7 := (Term.Apply (Term.UOp UserOp.not) t6)
def s0 : LogosState := logos_init_state
def s1 : LogosState := (logos_invoke_assume s0 t4)
def s2 : LogosState := (logos_invoke_assume s1 t7)
def s3 : LogosState := (logos_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s4 : LogosState := (logos_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
#eval!
(logos_state_is_refutation s4)
