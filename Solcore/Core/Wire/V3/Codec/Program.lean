import Solcore.Core.Wire.V3.Codec.ExprDecode

/-! Complete Program codec and cross-Program Core budget aggregation. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeProgram (program : Program) : Lean.Json :=
  .mkObj [
    ("schema", schemaVersion),
    ("resultType", encodeType program.resultType),
    ("dataDefinitions", encodeDataDefinitions program.dataDefinitions),
    ("body", encodeExpr program.body)
  ]

def programDepth (program : Program) : Nat :=
  Nat.max (typeDepth program.resultType)
    (Nat.max (dataEnvironmentDepth program.dataDefinitions)
      (exprDepth program.body)) + 1

def programNodes (program : Program) : Nat :=
  1 + typeNodes program.resultType +
    dataEnvironmentNodes program.dataDefinitions + exprNodes program.body

def decodeProgramAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (path : DecodePath)
    (json : Lean.Json) : CoreDecodeResult (Program × CoreBudgetState) := do
  let state ← consumeCoreNode limits state 1
  liftProtocol <| ensureExactObject path json
    ["body", "dataDefinitions", "resultType", "schema"]
    ["body", "dataDefinitions", "resultType", "schema"]

  /- Schema is a scalar of the current Program node, so it precedes children. -/
  let schemaPath := path.field "schema"
  let actualSchema ← liftProtocol <| decodeStringAt schemaPath
    (← liftProtocol <| requireField path json "schema")
  unless actualSchema == schemaVersion do
    throw (.protocol {
      path := schemaPath
      code := .invalidSchema
      arguments := .mkObj [
        ("expected", schemaVersion),
        ("actual", actualSchema)
      ]
    })

  /- Child Core positions are traversed by field name. -/
  let (body, state) ← decodeExprAtWithBudget limits state 2
    (path.field "body")
    (← liftProtocol <| requireField path json "body")
  let (dataDefinitions, state) ← decodeDataDefinitionsAtWithBudget limits state 2
    (path.field "dataDefinitions")
    (← liftProtocol <| requireField path json "dataDefinitions")
  let (resultType, state) ← decodeTypeAtWithBudget limits state 2
    (path.field "resultType")
    (← liftProtocol <| requireField path json "resultType")
  pure ({ resultType, dataDefinitions, body }, state)

def decodeProgramWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Program := do
  let (program, _) ← decodeProgramAtWithBudget limits .initial .root json
  pure program

def decodeProgram (json : Lean.Json) : CoreDecodeResult Program :=
  decodeProgramWithBudget .default json

structure LocatedProgramJson where
  path : DecodePath
  json : Lean.Json

private def decodeLocatedProgramList
    (limits : CoreBudgetLimits) :
    CoreBudgetState → List LocatedProgramJson →
      CoreDecodeResult (List Program × CoreBudgetState)
  | state, [] => pure ([], state)
  | state, located :: rest => do
      let (program, state) ←
        decodeProgramAtWithBudget limits state located.path located.json
      let (programs, state) ← decodeLocatedProgramList limits state rest
      pure (program :: programs, state)

/-- Decode canonical package order with cumulative nodes and fresh root depth. -/
def decodeProgramsWithBudget
    (limits : CoreBudgetLimits)
    (programs : List LocatedProgramJson) :
    CoreDecodeResult (List Program × CoreBudgetState) :=
  decodeLocatedProgramList limits .initial programs

def programListDepth : List Program → Nat
  | [] => 0
  | program :: rest => Nat.max (programDepth program) (programListDepth rest)

def programListNodes : List Program → Nat
  | [] => 0
  | program :: rest => programNodes program + programListNodes rest

def canonicalizeProgramWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeProgram <$> decodeProgramWithBudget limits json

theorem canonicalizeProgramWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits)
    (json : Lean.Json)
    (program : Program)
    (success : decodeProgramWithBudget limits json = .ok program) :
    canonicalizeProgramWithBudget limits json = .ok (encodeProgram program) := by
  rw [canonicalizeProgramWithBudget, success]
  rfl

end Solcore.Core.Wire.V3
