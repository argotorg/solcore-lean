import Solcore.Oracle.V5.Wire.JsonBudget

/-! Regressions for complete Oracle v5 JSON resource measurement. -/

set_option autoImplicit false

namespace Tests.OracleV5JsonBudget

open Solcore.Oracle.V5
open Solcore.Oracle.V5.Wire

private def nested : Lean.Json :=
  .mkObj [
    ("a", .arr #[
      .null,
      .mkObj [("b", true)]
    ])
  ]

private def depthExceeded : Limits := {
  Limits.default with
  jsonDepth := 3
  jsonNodes := 4
}

private def nodesExceeded : Limits := {
  Limits.default with
  jsonDepth := 4
  jsonNodes := 4
}

private def exact : Limits := {
  Limits.default with
  jsonDepth := 4
  jsonNodes := 5
}

private def failureResource? (limits : Limits) : Option PreflightResource :=
  (checkJsonBudget limits nested).map (fun exhaustion => exhaustion.resource)

private def checks : Bool :=
  measureJson .null == { depth := 1, nodes := 1 } &&
    measureJson (.arr #[]) == { depth := 1, nodes := 1 } &&
    measureJson nested == { depth := 4, nodes := 5 } &&
    failureResource? depthExceeded == some .jsonDepth &&
    failureResource? nodesExceeded == some .jsonNodes &&
    (checkJsonBudget exact nested).isNone

private theorem checks_exact : checks = true := by
  native_decide

def testOracleV5JsonBudget : IO Unit := do
  unless checks do
    throw (IO.userError
      "Oracle v5 whole-tree JSON demand or depth-before-nodes precedence changed")

end Tests.OracleV5JsonBudget
