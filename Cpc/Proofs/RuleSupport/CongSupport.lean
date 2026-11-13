module

/-
Facade module: CongSupport was split into Cpc/Proofs/RuleSupport/Cong/*
(Core -> ValueRel -> HoCong -> ApplySpineA -> ApplySpineB -> TupleBvSeq ->
RegLanSpine -> Binders -> TypeSpine -> TrueSpine -> Impl -> Spine), each importing the
previous. Importing this module provides the full CongSupport namespace.
-/
public import Cpc.Proofs.RuleSupport.Cong.Spine
import all Cpc.Proofs.RuleSupport.Cong.Spine

public section
