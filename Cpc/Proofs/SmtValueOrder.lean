module

public import Cpc.SmtValueOrder
import all Cpc.SmtValueOrder
import Std

public section

set_option linter.unusedVariables false

namespace Smtm

open SmtEval

noncomputable section

namespace SmtValueOrder

theorem Key.lt_ne : ∀ {a b}, Key.lt a b = true → a ≠ b := by
  intro a
  induction a with
  | atom m =>
      intro b h
      cases b with
      | atom n => simp_all [Key.lt]; omega
      | real s => simp
      | pair c d => simp_all
  | real r =>
      intro b h
      cases b with
      | atom n => simp
      | real s =>
          simp [Key.lt] at h
          intro e
          injection e with e
          subst e
          exact lt_irrefl _ h
      | pair c d => simp
  | pair a b iha ihb =>
      intro c h
      cases c with
      | atom n => simp_all [Key.lt]
      | real s => simp
      | pair c d =>
          simp only [Key.lt] at h
          split at h
          · subst c
            intro heq
            simp_all
          · intro heq
            simp_all

theorem Key.lt_flip : ∀ {a b}, a ≠ b → Key.lt a b = false → Key.lt b a = true := by
  intro a
  induction a with
  | atom m =>
      intro b hne hlt
      cases b with
      | atom n => simp_all [Key.lt]; omega
      | real s => simp_all [Key.lt]
      | pair c d => simp_all [Key.lt]
  | real r =>
      intro b hne hlt
      cases b with
      | atom n => simp [Key.lt]
      | real s =>
          have hrs : s ≠ r := fun e => hne (e ▸ rfl)
          simp [Key.lt] at hlt ⊢
          exact lt_of_le_of_ne hlt hrs
      | pair c d => simp_all [Key.lt]
  | pair a b iha ihb =>
      intro c hne hlt
      cases c with
      | atom n => simp_all [Key.lt]
      | real s => simp [Key.lt]
      | pair c d =>
          simp only [Key.lt] at hlt ⊢
          by_cases hac : a = c
          · subst c
            simp only [ite_true]
            apply ihb
            · intro hbd
              simp_all
            · simpa [Key.lt] using hlt
          · simp only [hac, ite_false] at hlt
            have hca : c ≠ a := Ne.symm hac
            simp only [hca, ite_false]
            exact iha hac hlt

theorem Key.lt_asymm : ∀ {a b}, Key.lt a b = true → Key.lt b a = false := by
  intro a
  induction a with
  | atom m =>
      intro b hab
      cases b with
      | atom n => simp_all [Key.lt]; omega
      | real s => simp [Key.lt]
      | pair c d => simp [Key.lt]
  | real r =>
      intro b hab
      cases b with
      | atom n => simp_all [Key.lt]
      | real s =>
          simp [Key.lt] at hab ⊢
          exact le_of_lt hab
      | pair c d => simp [Key.lt]
  | pair a b iha ihb =>
      intro c hab
      cases c with
      | atom n => simp_all [Key.lt]
      | real s => simp_all [Key.lt]
      | pair c d =>
          simp only [Key.lt] at hab ⊢
          by_cases hac : a = c
          · subst c
            simp only [ite_true] at hab ⊢
            exact ihb hab
          · simp only [hac, ite_false] at hab
            have hca : c ≠ a := Ne.symm hac
            simp only [hca, ite_false]
            exact iha hab

theorem Key.lt_trans : ∀ {a b c}, Key.lt a b = true → Key.lt b c = true → Key.lt a c = true := by
  intro a
  induction a with
  | atom m =>
      intro b c hab hbc
      cases b <;> cases c <;> simp_all [Key.lt] <;> omega
  | real r =>
      intro b c hab hbc
      cases b <;> cases c <;> simp_all [Key.lt]
      exact _root_.lt_trans hab hbc
  | pair a₁ a₂ ih₁ ih₂ =>
      intro b c hab hbc
      cases b with
      | atom n => simp_all [Key.lt]
      | real s => simp_all [Key.lt]
      | pair b₁ b₂ =>
          cases c with
          | atom p => simp_all [Key.lt]
          | real t => simp_all [Key.lt]
          | pair c₁ c₂ =>
              simp only [Key.lt] at hab hbc ⊢
              by_cases hab₁ : a₁ = b₁
              · subst b₁
                simp only [ite_true] at hab
                by_cases hbc₁ : a₁ = c₁
                · subst c₁
                  simp only [ite_true] at hbc ⊢
                  exact ih₂ hab hbc
                · simp only [hbc₁, ite_false] at hbc ⊢
                  exact hbc
              · simp only [hab₁, ite_false] at hab
                by_cases hbc₁ : b₁ = c₁
                · subst c₁
                  simp only [hab₁, ite_false]
                  exact hab
                · simp only [hbc₁, ite_false] at hbc
                  by_cases hac₁ : a₁ = c₁
                  · subst c₁
                    exact False.elim (by
                      have hasymm := Key.lt_asymm hab
                      simp_all)
                  · simp only [hac₁, ite_false]
                    exact ih₁ hab hbc

@[expose] def intOfKey : Key → Option Int
  | .pair (.atom 0) (.pair (.atom n) (.atom 0)) => some (.ofNat n)
  | .pair (.atom 1) (.pair (.atom n) (.atom 0)) => some (.negSucc n)
  | _ => none

@[expose] def realOfKey : Key → Option native_Real
  | .real r => some r
  | _ => none

@[expose] def stringOfKey : Key → Option native_String
  | .atom 0 => some []
  | .pair (.atom c) ks => return c :: (← stringOfKey ks)
  | _ => none

theorem intOfKey_intKey (i : Int) : intOfKey (intKey i) = some i := by
  cases i <;> rfl

theorem realOfKey_realKey (r : native_Real) : realOfKey (realKey r) = some r := rfl

theorem stringOfKey_stringKey (s : native_String) :
    stringOfKey (stringKey s) = some s := by
  induction s with
  | nil => rfl
  | cons c cs ih => simp [stringKey, stringOfKey, charKey, ih]

mutual

@[expose] def typeOfKey : Key → Option SmtType
  | .pair (.atom 0) (.atom 0) => some .None
  | .pair (.atom 1) (.atom 0) => some .Bool
  | .pair (.atom 2) (.atom 0) => some .Int
  | .pair (.atom 3) (.atom 0) => some .Real
  | .pair (.atom 4) (.atom 0) => some .RegLan
  | .pair (.atom 5) (.pair (.atom w) (.atom 0)) => some (.BitVec w)
  | .pair (.atom 6) (.pair kt (.pair ku (.atom 0))) =>
      return .Map (← typeOfKey kt) (← typeOfKey ku)
  | .pair (.atom 7) (.pair kt (.atom 0)) => return .Set (← typeOfKey kt)
  | .pair (.atom 8) (.pair kt (.atom 0)) => return .Seq (← typeOfKey kt)
  | .pair (.atom 9) (.atom 0) => some .Char
  | .pair (.atom 10) (.pair ks (.pair kdd (.atom 0))) =>
      return .Datatype (← stringOfKey ks) (← datatypeDeclOfKey kdd)
  | .pair (.atom 11) (.pair ks (.atom 0)) => return .TypeRef (← stringOfKey ks)
  | .pair (.atom 12) (.pair (.atom n) (.atom 0)) => some (.USort n)
  | .pair (.atom 13) (.pair kt (.pair ku (.atom 0))) =>
      return .FunType (← typeOfKey kt) (← typeOfKey ku)
  | .pair (.atom 14) (.pair kt (.pair ku (.atom 0))) =>
      return .DtcAppType (← typeOfKey kt) (← typeOfKey ku)
  | _ => none

@[expose] def valueOfKey : Key → Option SmtValue
  | .pair (.atom 0) (.atom 0) => some .NotValue
  | .pair (.atom 1) (.pair (.atom 0) (.atom 0)) => some (.Boolean false)
  | .pair (.atom 1) (.pair (.atom 1) (.atom 0)) => some (.Boolean true)
  | .pair (.atom 2) (.pair ki (.atom 0)) => return .Numeral (← intOfKey ki)
  | .pair (.atom 3) (.pair kq (.atom 0)) => return .Real (← realOfKey kq)
  | .pair (.atom 4) (.pair kw (.pair ki (.atom 0))) =>
      return .Binary (← intOfKey kw) (← intOfKey ki)
  | .pair (.atom 5) (.pair km (.atom 0)) => return .Map (← mapOfKey km)
  | .pair (.atom 6) (.pair ks (.pair kt (.pair ku (.atom 0)))) =>
      return .Fun (← realOfKey ks) (← typeOfKey kt) (← typeOfKey ku)
  | .pair (.atom 7) (.pair km (.atom 0)) => return .Set (← mapOfKey km)
  | .pair (.atom 8) (.pair ks (.atom 0)) => return .Seq (← seqOfKey ks)
  | .pair (.atom 9) (.pair (.atom c) (.atom 0)) => some (.Char c)
  | .pair (.atom 10) (.pair (.atom i) (.pair kr (.atom 0))) =>
      return .UValue i (← realOfKey kr)
  | .pair (.atom 11) (.pair kr (.atom 0)) => return .RegLan (← regLanOfKey kr)
  | .pair (.atom 12) (.pair ks (.pair kdd (.pair (.atom n) (.atom 0)))) =>
      return .DtCons (← stringOfKey ks) (← datatypeDeclOfKey kdd) n
  | .pair (.atom 13) (.pair kf (.pair ka (.atom 0))) =>
      return .Apply (← valueOfKey kf) (← valueOfKey ka)
  | _ => none

@[expose] def regLanOfKey : Key → Option SmtRegLan
  | .pair (.atom 0) (.atom 0) => some .empty
  | .pair (.atom 1) (.atom 0) => some .epsilon
  | .pair (.atom 2) (.pair kc (.atom 0)) => return .char (← valueOfKey kc)
  | .pair (.atom 3) (.pair klo (.pair khi (.atom 0))) =>
      return .range (← valueOfKey klo) (← valueOfKey khi)
  | .pair (.atom 4) (.atom 0) => some .allchar
  | .pair (.atom 5) (.pair kr₁ (.pair kr₂ (.atom 0))) =>
      return .concat (← regLanOfKey kr₁) (← regLanOfKey kr₂)
  | .pair (.atom 6) (.pair kr₁ (.pair kr₂ (.atom 0))) =>
      return .union (← regLanOfKey kr₁) (← regLanOfKey kr₂)
  | .pair (.atom 7) (.pair kr₁ (.pair kr₂ (.atom 0))) =>
      return .inter (← regLanOfKey kr₁) (← regLanOfKey kr₂)
  | .pair (.atom 8) (.pair kr (.atom 0)) => return .star (← regLanOfKey kr)
  | .pair (.atom 9) (.pair kr (.atom 0)) => return .comp (← regLanOfKey kr)
  | _ => none

@[expose] def mapOfKey : Key → Option SmtMap
  | .pair (.atom 0) (.pair ki (.pair ke (.pair km (.atom 0)))) =>
      return .cons (← valueOfKey ki) (← valueOfKey ke) (← mapOfKey km)
  | .pair (.atom 1) (.pair kt (.pair ke (.atom 0))) =>
      return .default (← typeOfKey kt) (← valueOfKey ke)
  | _ => none

@[expose] def seqOfKey : Key → Option SmtSeq
  | .pair (.atom 0) (.pair kv (.pair kvs (.atom 0))) =>
      return .cons (← valueOfKey kv) (← seqOfKey kvs)
  | .pair (.atom 1) (.pair kt (.atom 0)) => return .empty (← typeOfKey kt)
  | _ => none

@[expose] def datatypeDeclOfKey : Key → Option SmtDatatypeDecl
  | .pair (.atom 0) (.atom 0) => some .nil
  | .pair (.atom 1) (.pair ks (.pair kd (.pair kdd (.atom 0)))) =>
      return .cons (← stringOfKey ks) (← datatypeOfKey kd) (← datatypeDeclOfKey kdd)
  | _ => none

@[expose] def datatypeOfKey : Key → Option SmtDatatype
  | .pair (.atom 0) (.atom 0) => some .null
  | .pair (.atom 1) (.pair kc (.pair kd (.atom 0))) =>
      return .sum (← datatypeConsOfKey kc) (← datatypeOfKey kd)
  | _ => none

@[expose] def datatypeConsOfKey : Key → Option SmtDatatypeCons
  | .pair (.atom 0) (.atom 0) => some .unit
  | .pair (.atom 1) (.pair kt (.pair kc (.atom 0))) =>
      return .cons (← typeOfKey kt) (← datatypeConsOfKey kc)
  | _ => none

end

mutual

theorem typeOfKey_typeKey (t : SmtType) : typeOfKey (typeKey t) = some t := by
  cases t <;> simp [typeKey, typeOfKey, node, fields, natKey, stringOfKey_stringKey,
    typeOfKey_typeKey, datatypeDeclOfKey_datatypeDeclKey]

theorem valueOfKey_valueKey (v : SmtValue) : valueOfKey (valueKey v) = some v := by
  cases v <;> simp [valueKey, valueOfKey, node, fields, natKey, boolKey, charKey,
    intOfKey_intKey, realOfKey_realKey, stringOfKey_stringKey, regLanOfKey_regLanKey,
    typeOfKey_typeKey, valueOfKey_valueKey, mapOfKey_mapKey, seqOfKey_seqKey,
    datatypeDeclOfKey_datatypeDeclKey]
  case Boolean b => cases b <;> rfl

theorem regLanOfKey_regLanKey (r : SmtRegLan) :
    regLanOfKey (regLanKey r) = some r := by
  cases r <;> simp [regLanKey, regLanOfKey, node, fields,
    valueOfKey_valueKey, regLanOfKey_regLanKey]

theorem mapOfKey_mapKey (m : SmtMap) : mapOfKey (mapKey m) = some m := by
  cases m <;> simp [mapKey, mapOfKey, node, fields,
    typeOfKey_typeKey, valueOfKey_valueKey, mapOfKey_mapKey]

theorem seqOfKey_seqKey (s : SmtSeq) : seqOfKey (seqKey s) = some s := by
  cases s <;> simp [seqKey, seqOfKey, node, fields,
    typeOfKey_typeKey, valueOfKey_valueKey, seqOfKey_seqKey]

theorem datatypeDeclOfKey_datatypeDeclKey (dd : SmtDatatypeDecl) :
    datatypeDeclOfKey (datatypeDeclKey dd) = some dd := by
  cases dd <;> simp [datatypeDeclKey, datatypeDeclOfKey, node, fields,
    stringOfKey_stringKey, datatypeOfKey_datatypeKey,
    datatypeDeclOfKey_datatypeDeclKey]

theorem datatypeOfKey_datatypeKey (d : SmtDatatype) :
    datatypeOfKey (datatypeKey d) = some d := by
  cases d <;> simp [datatypeKey, datatypeOfKey, node, fields,
    datatypeConsOfKey_datatypeConsKey, datatypeOfKey_datatypeKey]

theorem datatypeConsOfKey_datatypeConsKey (c : SmtDatatypeCons) :
    datatypeConsOfKey (datatypeConsKey c) = some c := by
  cases c <;> simp [datatypeConsKey, datatypeConsOfKey, node, fields,
    typeOfKey_typeKey, datatypeConsOfKey_datatypeConsKey]

end


theorem valueKey_injective : Function.Injective valueKey := by
  intro a b h
  have h' := congrArg valueOfKey h
  simpa [valueOfKey_valueKey] using h'

theorem lt_flip {a b : SmtValue} (hne : a ≠ b) (hlt : lt a b = false) :
    lt b a = true := by
  apply Key.lt_flip
  · exact fun h => hne (valueKey_injective h)
  · exact hlt

theorem lt_ne {a b : SmtValue} (hlt : lt a b = true) : a ≠ b := by
  intro h
  subst b
  exact Key.lt_ne hlt rfl

theorem lt_trans {a b c : SmtValue} (hab : lt a b = true) (hbc : lt b c = true) :
    lt a c = true := Key.lt_trans hab hbc

end SmtValueOrder

end

end Smtm
