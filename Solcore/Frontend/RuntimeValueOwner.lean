import Solcore.Frontend.RuntimeValue
import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.LocalNameRenaming

/- Owner relabeling reaches every finite nested source closure. Core syntax,
types, locations and source spans remain literal; no runtime object is executed. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Relabel saved declaration owners and local IDs, preserving every ordered payload. -/
def RuntimeValue.mapOwners (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (value : RuntimeValue) : RuntimeValue :=
  match value with
  | .unit => .unit
  | .bool b => .bool b
  | .word w => .word w
  | .hostFunction f => .hostFunction f
  | .pair left right => .pair (mapOwners mapping left) (mapOwners mapping right)
  | .coreClosure parameter result body captured =>
      .coreClosure parameter result body (captured.attach.map (fun v => mapOwners mapping v.val))
  | .inLeft ty payload => .inLeft ty (mapOwners mapping payload)
  | .inRight ty payload => .inRight ty (mapOwners mapping payload)
  | .cellRef ty location => .cellRef ty location
  | .constructed constructor payload => .constructed constructor (mapOwners mapping payload)
  | .sourceClosure source owner names captured =>
      .sourceClosure source (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (captured.attach.map (fun row => (ownerLocalIdMap mapping row.val.1,mapOwners mapping row.val.2)))
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals first
    | have smaller := List.sizeOf_lt_of_mem v.property; omega
    | have smaller := List.sizeOf_lt_of_mem row.property
      have pairSize : sizeOf row.val = 1 + sizeOf row.val.1 + sizeOf row.val.2 := by
        cases row.val; rfl
      omega

/-- Relabel both keys and complete values of an ordered runtime capture table. -/
def mapRuntimeCapturedOwners (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (captured : Resolved.LocalScope RuntimeValue) : Resolved.LocalScope RuntimeValue :=
  captured.map (fun row => (ownerLocalIdMap mapping row.1,row.2.mapOwners mapping))

/-- Core bodies and types are unchanged; source closures nested in captures are reached. -/
theorem RuntimeValue.mapOwners_coreClosure
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (parameter result : Core.Ty) (body : Core.Expr) (captured : List RuntimeValue) :
    (.coreClosure parameter result body captured : RuntimeValue).mapOwners mapping =
      .coreClosure parameter result body (captured.map (RuntimeValue.mapOwners mapping)) := by
  simp only [mapOwners,List.attach_map_val]

/-- Saved syntax and row order are literal; every owner, key and captured value is mapped. -/
theorem RuntimeValue.mapOwners_sourceClosure
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (source : Syntax.Expr) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) :
    (.sourceClosure source owner names captured : RuntimeValue).mapOwners mapping =
      .sourceClosure source (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) := by
  simp only [mapOwners,mapRuntimeCapturedOwners]
  congr 1
  change captured.attach.map
    ((fun row : Resolved.LocalId × RuntimeValue => (ownerLocalIdMap mapping row.1,mapOwners mapping row.2)) ∘ Subtype.val) = _
  rw [← List.map_map,List.attach_map_subtype_val]

end Solcore.Frontend
