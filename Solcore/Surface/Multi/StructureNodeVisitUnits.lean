import Solcore.Surface.Multi.AstCarrierEnumeration

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
The structural-resource contract has three unit families.  This module closes
the first family: one unit for each concrete AST carrier visited through the
`astChildren` traversal.  Comparisons and diagnostic insertions remain
separate so later accounting cannot hide either cost in the node traversal.
-/

/-- One recorded `astChildren` visit.  The ordinal distinguishes repeated
carrier sorts while the carrier records the concrete kind visited. -/
structure StructureNodeVisitUnit where
  ordinal : Nat
  carrier : AstCarrier
deriving DecidableEq, Repr

/-- Materialize the node-visit unit stream in the exact traversal order used
by the concrete AST-carrier enumeration. -/
def structureNodeVisitTrace
    (module : ParsedModuleV1) : List StructureNodeVisitUnit :=
  (astCarrierEnumeration module).mapIdx fun ordinal carrier =>
    { ordinal, carrier }

/-- Executable count of structural node-visit units. -/
def structureNodeVisitUnits (module : ParsedModuleV1) : Nat :=
  (structureNodeVisitTrace module).length

@[simp] theorem structureNodeVisitTrace_length
    (module : ParsedModuleV1) :
    (structureNodeVisitTrace module).length =
      (astCarrierEnumeration module).length := by
  simp [structureNodeVisitTrace]

/-- Looking up an event records exactly the carrier at the same ordinal in the
concrete AST traversal. -/
theorem structureNodeVisitTrace_get?
    (module : ParsedModuleV1) (ordinal : Nat) :
    (structureNodeVisitTrace module)[ordinal]? =
      (astCarrierEnumeration module)[ordinal]?.map fun carrier =>
        { ordinal, carrier } := by
  simp [structureNodeVisitTrace]

private theorem nodeVisitTraceFrom_nodup
    (start : Nat) (carriers : List AstCarrier) :
    (carriers.mapIdx fun ordinal carrier =>
      ({ ordinal := start + ordinal, carrier } : StructureNodeVisitUnit)).Nodup := by
  induction carriers generalizing start with
  | nil => simp
  | cons head tail induction =>
      rw [List.mapIdx_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_mapIdx] at member
        rcases member with ⟨ordinal, _within, same⟩
        have ordinalSame := congrArg StructureNodeVisitUnit.ordinal same
        simp only at ordinalSame
        omega
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          induction (start := start + 1)

/-- Visit events are individually distinguishable even when their AST carrier
sorts coincide. -/
theorem structureNodeVisitTrace_nodup (module : ParsedModuleV1) :
    (structureNodeVisitTrace module).Nodup := by
  simpa [structureNodeVisitTrace] using
    nodeVisitTraceFrom_nodup 0 (astCarrierEnumeration module)

/-- Node-visit accounting is exactly the already certified AST measure. -/
@[simp] theorem structureNodeVisitUnits_eq_astNodeMeasure
    (module : ParsedModuleV1) :
    structureNodeVisitUnits module = astNodeMeasure module := by
  simp [structureNodeVisitUnits,
    astNodeMeasure_eq_astCarrier_cardinality]

theorem structureNodeVisitUnits_positive (module : ParsedModuleV1) :
    0 < structureNodeVisitUnits module := by
  rw [structureNodeVisitUnits_eq_astNodeMeasure]
  simp only [astNodeMeasure]
  omega

/-- The node-visit family alone fits within the fixed structural bound. -/
theorem structureNodeVisitUnits_le_structureBound
    (module : ParsedModuleV1) :
    structureNodeVisitUnits module ≤ structureBound (astNodeMeasure module) := by
  rw [structureNodeVisitUnits_eq_astNodeMeasure]
  simp only [structureBound]
  let nodeCount := astNodeMeasure module
  calc
    nodeCount ≤ nodeCount + 1 := Nat.le_succ nodeCount
    _ = 1 * (nodeCount + 1) := by simp
    _ ≤ 32 * (nodeCount + 1) :=
      Nat.mul_le_mul_right (nodeCount + 1) (by omega)
    _ = 32 * (nodeCount + 1) * 1 := by simp
    _ ≤ 32 * (nodeCount + 1) * (nodeCount + 1) :=
      Nat.mul_le_mul_left (32 * (nodeCount + 1)) (by omega)

end Solcore.Surface.Multi
