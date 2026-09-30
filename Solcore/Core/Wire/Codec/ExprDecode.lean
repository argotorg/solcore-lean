import Solcore.Core.Wire.Codec.ExprMeasure

/-! Strict expression decoding with depth-first, cumulative-node budgets. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

private abbrev ChildExprDecoder :=
  CoreBudgetState → DecodePath → Lean.Json →
    CoreDecodeResult (Expr × CoreBudgetState)

private def decodeExprJsonListAt
    (decodeChild : ChildExprDecoder)
    (path : DecodePath) :
    Nat → CoreBudgetState → List Lean.Json →
      CoreDecodeResult (List Expr × CoreBudgetState)
  | _, state, [] => pure ([], state)
  | index, state, json :: rest => do
      let (expression, state) ← decodeChild state (path.index index) json
      let (expressions, state) ←
        decodeExprJsonListAt decodeChild path (index + 1) state rest
      pure (expression :: expressions, state)

private def decodeExprArrayAt
    (decodeChild : ChildExprDecoder)
    (state : CoreBudgetState)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (List Expr × CoreBudgetState) := do
  let values ← liftProtocol <|
    match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (.mkObj [
        ("expected", "array"),
        ("actual", match json with
          | .null => "null" | .bool _ => "boolean" | .num _ => "number"
          | .str _ => "string" | .arr _ => "array" | .obj _ => "object")
      ])
  decodeExprJsonListAt decodeChild path 0 state values

private def decodeExprAtFuel :
    (fuel : Nat) → (limits : CoreBudgetLimits) → CoreBudgetState →
      (depth : Nat) → fuel = limits.maxDepth + 1 - depth →
      DecodePath → Lean.Json → CoreDecodeResult (Expr × CoreBudgetState)
  | 0, limits, _, depth, exactFuel, _, _ =>
      .error (.exhausted {
        resource := .depth
        limit := limits.maxDepth
        consumed := depth
        exceeded := by
          have zeroSub : limits.maxDepth + 1 - depth = 0 := exactFuel.symm
          have bound := Nat.sub_eq_zero_iff_le.mp zeroSub
          omega
      })
  | fuel + 1, limits, state, depth, exactFuel, path, json => do
      have childFuel : fuel = limits.maxDepth + 1 - (depth + 1) := by omega
      let decodeChild : ChildExprDecoder := fun state path json =>
        decodeExprAtFuel fuel limits state (depth + 1) childFuel path json
      let decodeTypeChild := fun state path json =>
        decodeTypeAtWithBudget limits state (depth + 1) path json
      let state ← consumeCoreNode limits state depth
      liftProtocol <| ensureExactObject path json
        ["tag", "value", "index", "left", "right", "operand", "parameterType",
          "resultType", "body", "function", "argument", "rightType", "payload",
          "leftType", "scrutinee", "leftBranch", "rightBranch", "elementType",
          "initializer", "reference", "constructor", "dataType", "branches", "op",
          "first", "second", "third", "condition", "thenBranch", "elseBranch"]
        ["tag"]
      let tagPath := path.field "tag"
      let tag ← liftProtocol <| decodeStringAt tagPath
        (← liftProtocol <| requireField path json "tag")
      match tag with
      | "unit" =>
          liftProtocol <| ensureExactObject path json ["tag"] ["tag"]
          pure (.unit, state)
      | "bool" =>
          liftProtocol <| ensureExactObject path json ["tag", "value"] ["tag", "value"]
          let value ← liftProtocol <| decodeBoolAt (path.field "value")
            (← liftProtocol <| requireField path json "value")
          pure (.bool value, state)
      | "word" =>
          liftProtocol <| ensureExactObject path json ["tag", "value"] ["tag", "value"]
          let value ← liftProtocol <| decodeWordAt (path.field "value")
            (← liftProtocol <| requireField path json "value")
          pure (.word value, state)
      | "integer" =>
          liftProtocol <| ensureExactObject path json ["tag", "value"] ["tag", "value"]
          let (value, state) ← decodeIntegerAtWithBudget limits state (path.field "value")
            (← liftProtocol <| requireField path json "value")
          pure (.integer value, state)
      | "var" =>
          liftProtocol <| ensureExactObject path json ["index", "tag"] ["index", "tag"]
          let index ← liftProtocol <| decodeNatAt (path.field "index")
            (← liftProtocol <| requireField path json "index")
          pure (.var index, state)
      | "pair" | "apply" | "storeCell" | "let" =>
          let (firstName, secondName) := match tag with
            | "pair" => ("left", "right")
            | "apply" => ("argument", "function")
            | "storeCell" => ("reference", "value")
            | _ => ("body", "initializer")
          let fields := match tag with
            | "pair" => ["left", "right", "tag"]
            | "apply" => ["argument", "function", "tag"]
            | "storeCell" => ["reference", "tag", "value"]
            | _ => ["body", "initializer", "tag"]
          liftProtocol <| ensureExactObject path json fields fields
          let (first, state) ← decodeChild state (path.field firstName)
            (← liftProtocol <| requireField path json firstName)
          let (second, state) ← decodeChild state (path.field secondName)
            (← liftProtocol <| requireField path json secondName)
          match tag with
          | "pair" => pure (.pair first second, state)
          | "apply" => pure (.apply second first, state)
          | "storeCell" => pure (.storeCell first second, state)
          | _ => pure (.letE second first, state)
      | "first" | "second" | "loadCell" =>
          let field := if tag == "loadCell" then "reference" else "operand"
          let fields := if tag == "loadCell" then ["reference", "tag"]
            else ["operand", "tag"]
          liftProtocol <| ensureExactObject path json fields fields
          let (operand, state) ← decodeChild state (path.field field)
            (← liftProtocol <| requireField path json field)
          match tag with
          | "first" => pure (.first operand, state)
          | "second" => pure (.second operand, state)
          | _ => pure (.loadCell operand, state)
      | "lambda" =>
          liftProtocol <| ensureExactObject path json
            ["body", "parameterType", "resultType", "tag"]
            ["body", "parameterType", "resultType", "tag"]
          let (body, state) ← decodeChild state (path.field "body")
            (← liftProtocol <| requireField path json "body")
          let (parameterType, state) ← decodeTypeChild state (path.field "parameterType")
            (← liftProtocol <| requireField path json "parameterType")
          let (resultType, state) ← decodeTypeChild state (path.field "resultType")
            (← liftProtocol <| requireField path json "resultType")
          pure (.lambda parameterType resultType body, state)
      | "inLeft" | "inRight" | "newCell" =>
          let (typeField, exprField) := match tag with
            | "inLeft" => ("rightType", "payload")
            | "inRight" => ("leftType", "payload")
            | _ => ("elementType", "initializer")
          let fields := match tag with
            | "inLeft" => ["payload", "rightType", "tag"]
            | "inRight" => ["leftType", "payload", "tag"]
            | _ => ["elementType", "initializer", "tag"]
          liftProtocol <| ensureExactObject path json fields fields
          let decodeExpressionFirst := exprField < typeField
          let (expression, type, state) ←
            if decodeExpressionFirst then do
              let (expression, state) ← decodeChild state (path.field exprField)
                (← liftProtocol <| requireField path json exprField)
              let (type, state) ← decodeTypeChild state (path.field typeField)
                (← liftProtocol <| requireField path json typeField)
              pure (expression, type, state)
            else do
              let (type, state) ← decodeTypeChild state (path.field typeField)
                (← liftProtocol <| requireField path json typeField)
              let (expression, state) ← decodeChild state (path.field exprField)
                (← liftProtocol <| requireField path json exprField)
              pure (expression, type, state)
          match tag with
          | "inLeft" => pure (.inLeft type expression, state)
          | "inRight" => pure (.inRight type expression, state)
          | _ => pure (.newCell type expression, state)
      | "case" =>
          liftProtocol <| ensureExactObject path json
            ["leftBranch", "rightBranch", "scrutinee", "tag"]
            ["leftBranch", "rightBranch", "scrutinee", "tag"]
          let (leftBranch, state) ← decodeChild state (path.field "leftBranch")
            (← liftProtocol <| requireField path json "leftBranch")
          let (rightBranch, state) ← decodeChild state (path.field "rightBranch")
            (← liftProtocol <| requireField path json "rightBranch")
          let (scrutinee, state) ← decodeChild state (path.field "scrutinee")
            (← liftProtocol <| requireField path json "scrutinee")
          pure (.caseE scrutinee leftBranch rightBranch, state)
      | "construct" =>
          liftProtocol <| ensureExactObject path json ["constructor", "payload", "tag"]
            ["constructor", "payload", "tag"]
          let constructor ← liftProtocol <| decodeConstructorIdAt
            (path.field "constructor")
            (← liftProtocol <| requireField path json "constructor")
          let (payload, state) ← decodeChild state (path.field "payload")
            (← liftProtocol <| requireField path json "payload")
          pure (.construct constructor payload, state)
      | "matchData" =>
          liftProtocol <| ensureExactObject path json
            ["branches", "dataType", "resultType", "scrutinee", "tag"]
            ["branches", "dataType", "resultType", "scrutinee", "tag"]
          let dataType ← liftProtocol <| decodeDataTypeIdAt (path.field "dataType")
            (← liftProtocol <| requireField path json "dataType")
          let (branches, state) ← decodeExprArrayAt decodeChild state
            (path.field "branches")
            (← liftProtocol <| requireField path json "branches")
          let (resultType, state) ← decodeTypeChild state (path.field "resultType")
            (← liftProtocol <| requireField path json "resultType")
          let (scrutinee, state) ← decodeChild state (path.field "scrutinee")
            (← liftProtocol <| requireField path json "scrutinee")
          pure (.matchData dataType resultType scrutinee branches, state)
      | "unary" =>
          liftProtocol <| ensureExactObject path json ["op", "operand", "tag"]
            ["op", "operand", "tag"]
          let op ← liftProtocol <| decodeUnaryOpAt (path.field "op")
            (← liftProtocol <| requireField path json "op")
          let (operand, state) ← decodeChild state (path.field "operand")
            (← liftProtocol <| requireField path json "operand")
          pure (.unary op operand, state)
      | "binary" =>
          liftProtocol <| ensureExactObject path json ["left", "op", "right", "tag"]
            ["left", "op", "right", "tag"]
          let op ← liftProtocol <| decodeBinaryOpAt (path.field "op")
            (← liftProtocol <| requireField path json "op")
          let (left, state) ← decodeChild state (path.field "left")
            (← liftProtocol <| requireField path json "left")
          let (right, state) ← decodeChild state (path.field "right")
            (← liftProtocol <| requireField path json "right")
          pure (.binary op left right, state)
      | "ternary" =>
          liftProtocol <| ensureExactObject path json
            ["first", "op", "second", "tag", "third"]
            ["first", "op", "second", "tag", "third"]
          let op ← liftProtocol <| decodeTernaryOpAt (path.field "op")
            (← liftProtocol <| requireField path json "op")
          let (first, state) ← decodeChild state (path.field "first")
            (← liftProtocol <| requireField path json "first")
          let (second, state) ← decodeChild state (path.field "second")
            (← liftProtocol <| requireField path json "second")
          let (third, state) ← decodeChild state (path.field "third")
            (← liftProtocol <| requireField path json "third")
          pure (.ternary op first second third, state)
      | "if" =>
          liftProtocol <| ensureExactObject path json
            ["condition", "elseBranch", "tag", "thenBranch"]
            ["condition", "elseBranch", "tag", "thenBranch"]
          let (condition, state) ← decodeChild state (path.field "condition")
            (← liftProtocol <| requireField path json "condition")
          let (elseBranch, state) ← decodeChild state (path.field "elseBranch")
            (← liftProtocol <| requireField path json "elseBranch")
          let (thenBranch, state) ← decodeChild state (path.field "thenBranch")
            (← liftProtocol <| requireField path json "thenBranch")
          pure (.ifE condition thenBranch elseBranch, state)
      | _ => throw (.protocol {
          path := tagPath
          code := .invalidTag
          arguments := .mkObj [
            ("actual", tag),
            ("expected", .arr #[
              "unit", "bool", "word", "integer", "var", "pair", "first", "second",
              "lambda", "apply", "inLeft", "inRight", "case", "newCell",
              "loadCell", "storeCell", "construct", "matchData", "unary",
              "binary", "ternary", "let", "if"
            ])
          ]
        })

def decodeExprAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) : CoreDecodeResult (Expr × CoreBudgetState) :=
  decodeExprAtFuel (limits.maxDepth + 1 - depth) limits state depth rfl path json

def decodeExprWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Expr := do
  let (expression, _) ← decodeExprAtWithBudget limits .initial 1 .root json
  pure expression

def decodeExpr (json : Lean.Json) : CoreDecodeResult Expr :=
  decodeExprWithBudget .default json

def canonicalizeExprWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeExpr <$> decodeExprWithBudget limits json

end Solcore.Core.Wire
