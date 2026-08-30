import Solcore.Oracle.V5.Schema

/-! Whole-tree resource accounting for parsed Oracle v5 JSON values. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

private def maximum (values : List Nat) : Nat :=
  values.foldl Nat.max 0

/--
The greatest root-to-node depth of a JSON value.  The root is at depth one;
empty containers therefore have depth one as well.
-/
partial def jsonDepth : Lean.Json → Nat
  | .arr values =>
      1 + maximum (values.toList.map jsonDepth)
  | .obj fields =>
      1 + maximum (fields.toList.map (fun entry => jsonDepth entry.2))
  | .null
  | .bool _
  | .num _
  | .str _ => 1

/-- Count every JSON value, including the root and unknown subtrees. -/
partial def jsonNodes : Lean.Json → Nat
  | .arr values =>
      1 + (values.toList.map jsonNodes).sum
  | .obj fields =>
      1 + (fields.toList.map (fun entry => jsonNodes entry.2)).sum
  | .null
  | .bool _
  | .num _
  | .str _ => 1

structure JsonDemand where
  depth : Nat
  nodes : Nat
  deriving Repr, BEq, DecidableEq

def measureJson (json : Lean.Json) : JsonDemand := {
  depth := jsonDepth json
  nodes := jsonNodes json
}

/--
Select a whole-tree JSON resource result in the published order: depth before
nodes.  Demand equal to a limit is accepted.
-/
def checkJsonBudget
    (limits : Limits)
    (json : Lean.Json) : Option PreflightExhaustion :=
  let depth := jsonDepth json
  if exceeded : limits.jsonDepth < depth then
    some {
      resource := .jsonDepth
      limit := limits.jsonDepth
      consumed := depth
      exceeded
    }
  else
    let nodes := jsonNodes json
    if exceeded : limits.jsonNodes < nodes then
      some {
        resource := .jsonNodes
        limit := limits.jsonNodes
        consumed := nodes
        exceeded
      }
    else
      none

theorem checkJsonBudget_eq_none_iff
    (limits : Limits)
    (json : Lean.Json) :
    checkJsonBudget limits json = none ↔
      jsonDepth json ≤ limits.jsonDepth ∧
      jsonNodes json ≤ limits.jsonNodes := by
  unfold checkJsonBudget
  by_cases depthExceeded : limits.jsonDepth < jsonDepth json
  · have depthNotWithin : ¬ jsonDepth json ≤ limits.jsonDepth :=
      Nat.not_le_of_gt depthExceeded
    simp [depthExceeded, depthNotWithin]
  · have depthWithin : jsonDepth json ≤ limits.jsonDepth :=
      Nat.le_of_not_gt depthExceeded
    by_cases nodesExceeded : limits.jsonNodes < jsonNodes json
    · have nodesNotWithin : ¬ jsonNodes json ≤ limits.jsonNodes :=
        Nat.not_le_of_gt nodesExceeded
      simp [depthExceeded, depthWithin, nodesExceeded, nodesNotWithin]
    · have nodesWithin : jsonNodes json ≤ limits.jsonNodes :=
        Nat.le_of_not_gt nodesExceeded
      simp [depthExceeded, depthWithin, nodesExceeded, nodesWithin]

end Solcore.Oracle.V5.Wire
