import Solcore
import Solcore.Core.Wire
import Solcore.Core.Wire.V2
import Solcore.Oracle.V2.Handler
import Solcore.Oracle.V3.Handler

set_option autoImplicit false

open Solcore
open Solcore.Core
open Solcore.Oracle

namespace Tests

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

def assertJsonRoundTrip {α : Type} [Lean.ToJson α] [Lean.FromJson α]
    (name : String) (value : α) : IO Unit := do
  let encoded := Lean.toJson value
  match (Lean.fromJson? encoded : Except String α) with
  | .error error =>
      throw (IO.userError s!"{name} did not decode: {error}")
  | .ok decoded =>
      assertTrue (Lean.toJson decoded == encoded) s!"{name} changed during JSON round-trip"

def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def validWorkspace : Workspace := {
  entry := "main.solc"
  sources := #[{
    path := "main.solc"
    content := "def main = 0"
  }]
}

def requestFor (kind : QueryKind) : Request := {
  schema := schemaVersion
  id := "test-request"
  spec := draftLanguage.id
  profile := {
    id := draftCoreProfile.id
    digest := draftCoreProfileDigest
  }
  workspace := if kind == .capabilities then none else some validWorkspace
  query := { kind }
}

def testProfile : IO Unit := do
  assertTrue draftCoreProfile.validationErrors.isEmpty
    s!"draft profile is invalid: {draftCoreProfile.validationErrors}"
  assertTrue (canonicalStd.files.size == 6) "canonical std must contain six .solc files"
  assertTrue
    (canonicalStd.manifestSha256 ==
      "3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22")
    "canonical std manifest digest changed"
  assertJsonRoundTrip "draft profile" draftCoreProfile
  let profileText ← IO.FS.readFile "profiles/solcore-0.1.0-draft.1-core.json"
  let profileJson ←
    match Lean.Json.parse profileText with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"profile JSON is invalid: {error}")
  assertTrue (profileJson == Lean.toJson draftCoreProfile)
    "checked-in profile JSON differs from the Lean profile"
  assertTrue rustStdCompatibilitySnapshot.validationErrors.isEmpty
    "Rust compatibility std snapshot metadata is invalid"

def testFeatureMatrix : IO Unit := do
  assertTrue featureMatrixIsComplete
    "feature matrix must contain every feature exactly once"
  assertTrue (featureMatrixRespectsProfile draftCoreProfile)
    "implemented features must be enabled and normative"

def coreConditionalProgram : Program := {
  resultType := .bool
  body :=
    .letE
      (.bool true)
      (.ifE (.var 0) (.bool false) (.bool true))
}

def testSemanticCore : IO Unit := do
  assertTrue coreConditionalProgram.check
    "the closed let/if Core witness must type-check"
  assertTrue (coreConditionalProgram.run 6 == .outOfFuel)
    "six CEK transitions must be insufficient for the seven-step witness"
  assertTrue (coreConditionalProgram.run 7 == .done (.bool false))
    "the Core evaluator must finish exactly at the seven-transition boundary"
  for fuel in [0, 1, 2, 3, 4, 5, 6, 7, 8] do
    match coreConditionalProgram.run fuel with
    | .fault error =>
        throw (IO.userError s!"well-typed Core program faulted: {reprStr error}")
    | _ => pure ()
  let lazyBranchProgram : Program := {
    resultType := .bool
    body := .ifE (.bool true) (.bool false) (.var 99)
  }
  assertTrue (lazyBranchProgram.run 3 == .outOfFuel)
    "three CEK transitions must stop before the selected branch returns"
  assertTrue (lazyBranchProgram.run 4 == .done (.bool false))
    "if must evaluate only the selected branch"
  let nearestBindingProgram : Program := {
    resultType := .bool
    body :=
      .letE
        (.bool true)
        (.letE
          (.bool false)
          (.ifE (.var 0) (.bool false) (.var 1)))
  }
  assertTrue nearestBindingProgram.check
    "nested de Bruijn bindings must type-check"
  assertTrue (nearestBindingProgram.run 16 == .done (.bool true))
    "index 0 must be the nearest binding and index 1 the next outer binding"
  let openProgram : Program := {
    resultType := .bool
    body := .var 0
  }
  assertTrue (!openProgram.check)
    "an unbound de Bruijn index must be rejected statically"
  let nonBooleanCondition : Program := {
    resultType := .bool
    body := .ifE .unit (.bool true) (.bool false)
  }
  assertTrue (!nonBooleanCondition.check)
    "if conditions must have bool type"
  assertTrue (nonBooleanCondition.run 2 == .fault (.expectedBool .unit))
    "the unchecked machine must expose a non-bool condition as a fault"
  let branchMismatch : Program := {
    resultType := .bool
    body := .ifE (.bool true) .unit (.bool false)
  }
  assertTrue (!branchMismatch.check)
    "if branches must have the same type"
  let declaredResultMismatch : Program := {
    resultType := .unit
    body := .bool true
  }
  assertTrue (!declaredResultMismatch.check)
    "the inferred Core result must equal the declared result type"
  assertTrue (Word.ofNat? 42).isSome
    "an in-range word literal must construct a Core word"
  assertTrue (Word.ofNat? wordModulus).isNone
    "a Core word must reject the first out-of-range natural"

def testPrimitiveAlgebra : IO Unit := do
  let word (value : Nat) : IO Word :=
    match Word.ofNat? value with
    | some result => pure result
    | none => throw (IO.userError s!"{value} must be an in-range Core word")
  let one ← word 1
  let two ← word 2
  let three ← word 3
  let seven ← word 7
  let shift255 ← word 255
  let shift256 ← word 256
  let doubledMaximum ← word (wordModulus - 2)
  let highBit ← word (2 ^ 255)
  assertTrue (Word.maximum.add one == Word.zero)
    "word addition must wrap modulo 2^256"
  assertTrue (Word.zero.sub one == Word.maximum)
    "word subtraction must wrap modulo 2^256"
  assertTrue (Word.maximum.mul two == doubledMaximum)
    "word multiplication must wrap modulo 2^256"
  assertTrue (seven.udiv three == two)
    "word division must use the unsigned quotient"
  assertTrue (seven.udiv Word.zero == Word.zero)
    "word division by zero must return zero"
  assertTrue (seven.umod three == one)
    "word modulo must use the unsigned remainder"
  assertTrue (seven.umod Word.zero == Word.zero)
    "word modulo by zero must return zero"
  assertTrue (Word.maximum.bitAnd Word.zero == Word.zero)
    "word bitwise and must operate on 256 bits"
  assertTrue (Word.maximum.bitOr Word.zero == Word.maximum)
    "word bitwise or must operate on 256 bits"
  assertTrue (Word.maximum.bitXor Word.maximum == Word.zero)
    "word bitwise xor must operate on 256 bits"
  assertTrue (Word.zero.bitNot == Word.maximum)
    "word bitwise not must complement exactly 256 bits"
  assertTrue (one.shiftLeft shift255 == highBit)
    "word left shift by 255 must retain the high bit"
  assertTrue (one.shiftLeft shift256 == Word.zero)
    "word left shift by 256 must return zero"
  assertTrue (one.shiftLeft Word.maximum == Word.zero)
    "word left shift by the maximum word must return zero"
  assertTrue (Word.maximum.shiftRight shift255 == one)
    "logical word right shift by 255 must retain the low bit"
  assertTrue (Word.maximum.shiftRight shift256 == Word.zero)
    "word right shift by 256 must return zero"
  assertTrue
    (UnaryOp.boolNot.apply (.bool true) == some (.bool false))
    "boolNot must negate a boolean"
  assertTrue
    (UnaryOp.boolNot.apply (.word one) == none)
    "an unchecked unary primitive must reject an invalid operand"
  assertTrue
    (BinaryOp.wordEq.apply (.word one) (.word one) == some (.bool true))
    "wordEq must return a Core boolean"
  assertTrue
    (BinaryOp.wordGt.apply (.word two) (.word one) == some (.bool true))
    "wordGt must compare words as unsigned values"
  assertTrue
    (BinaryOp.wordAdd.apply (.bool true) (.word one) == none)
    "an unchecked binary primitive must reject invalid operands"

def testM1cKernel : IO Unit := do
  let one ←
    match Word.ofNat? 1 with
    | some value => pure value
    | none => throw (IO.userError "one must be an in-range Core word")
  let addWrap : Program := {
    resultType := .word
    body := .binary .wordAdd (.word Word.maximum) (.word one)
  }
  assertTrue addWrap.check
    "a wordAdd expression with word operands must type-check"
  assertTrue (addWrap.run 4 == .outOfFuel)
    "four CEK transitions must be insufficient for a binary literal expression"
  assertTrue (addWrap.run 5 == .done (.word Word.zero))
    "wordAdd must complete exactly at its five-transition boundary"
  let negated : Program := {
    resultType := .bool
    body := .unary .boolNot (.bool true)
  }
  assertTrue negated.check
    "a boolNot expression with a bool operand must type-check"
  assertTrue (negated.run 2 == .outOfFuel)
    "two CEK transitions must be insufficient for a unary literal expression"
  assertTrue (negated.run 3 == .done (.bool false))
    "boolNot must complete exactly at its three-transition boundary"
  let derivedLessThan : Program := {
    resultType := .bool
    body := Expr.wordLt (.word Word.zero) (.word one)
  }
  assertTrue derivedLessThan.check
    "the derived wordLt combinator must type-check"
  assertTrue (derivedLessThan.run 5 == .done (.bool true))
    "wordLt must reverse wordGt operands without changing its result"
  let leftFaultsFirst : Program := {
    resultType := .word
    body := .binary .wordAdd (.var 11) (.var 22)
  }
  assertTrue
    (leftFaultsFirst.run 1 == .fault (.unboundVariable 11))
    "the unchecked binary machine must evaluate the left operand first"
  let rightBeforeInvalidApplication : Program := {
    resultType := .word
    body := .binary .wordAdd .unit (.var 22)
  }
  assertTrue
    (rightBeforeInvalidApplication.run 3 == .fault (.unboundVariable 22))
    "the unchecked binary machine must evaluate the right operand before applying the operator"
  let invalidUnary : Program := {
    resultType := .bool
    body := .unary .boolNot .unit
  }
  assertTrue
    (invalidUnary.run 2 == .fault (.invalidUnaryOperand .boolNot .unit))
    "the unchecked machine must expose an invalid unary operand"
  assertTrue (Core.Wire.V1.Program.ofCore? addWrap).isNone
    "Semantic Core v1 must not encode M1c primitive expressions"

def assertCoreWireError {α : Type}
    (name : String)
    (result : Except Core.Wire.V1.DecodeError α)
    (code : Core.Wire.V1.DecodeErrorCode)
    (path : String) :
    IO Unit := do
  match result with
  | .ok _ =>
      throw (IO.userError s!"{name} unexpectedly decoded")
  | .error error =>
      assertTrue (error.code == code)
        s!"{name} returned {error.code.wireName}, expected {code.wireName}"
      assertTrue (error.path.toPointer == path)
        s!"{name} failed at {error.path.toPointer}, expected {path}"

def testM1bProfile : IO Unit := do
  assertTrue m1aCoreProfile.validationErrors.isEmpty
    s!"draft.2 Core profile is invalid: {m1aCoreProfile.validationErrors}"
  assertTrue m1aFeatureMatrixIsComplete
    "M1a feature matrix must contain every draft.2 feature exactly once"
  assertTrue (m1aFeatureMatrixRespectsProfile m1aCoreProfile)
    "implemented M1a features must be normative and enabled"
  assertTrue (m1aLanguage.id == "solcore/0.1.0-draft.2")
    "M1a must be published as draft.2"
  assertTrue (m1aCoreProfile.enabledFeatures.size == 5)
    "the M1a profile must enable exactly the five normative Core features"
  assertTrue
    (m1aCoreProfile.enabledFeatures.all fun feature =>
      feature.specMaturity == .normative)
    "every M1a profile feature must be normative"
  assertJsonRoundTrip "draft.2 Core profile" m1aCoreProfile
  assertJsonRoundTrip "M1a feature matrix" m1aFeatureMatrix
  let profileText ←
    IO.FS.readFile "profiles/solcore-0.1.0-draft.2-core-m1a.json"
  let profileJson ←
    match Lean.Json.parse profileText with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"draft.2 profile JSON is invalid: {error}")
  assertTrue (profileJson == Lean.toJson m1aCoreProfile)
    "checked-in draft.2 profile differs from the Lean profile"

def testM1cProfile : IO Unit := do
  assertTrue m1cCoreProfile.validationErrors.isEmpty
    s!"draft.3 Core profile is invalid: {m1cCoreProfile.validationErrors}"
  assertTrue m1cFeatureMatrixIsComplete
    "M1c feature matrix must contain every draft.3 feature exactly once"
  assertTrue (m1cFeatureMatrixRespectsProfile m1cCoreProfile)
    "implemented M1c features must be normative and enabled"
  assertTrue (m1cLanguage.id == "solcore/0.1.0-draft.3")
    "M1c must be published as draft.3"
  assertTrue
    (m1cLanguage.staticSemanticsVersion == some 2 &&
      m1cLanguage.dynamicSemanticsVersion == some 2)
    "M1c must publish static and dynamic semantics version 2"
  assertTrue (m1cCoreProfile.enabledFeatures.size == 9)
    "the M1c profile must enable exactly nine normative Core features"
  assertTrue
    (m1cCoreProfile.enabledFeatures.all fun feature =>
      feature.specMaturity == .normative)
    "every M1c profile feature must be normative"
  assertJsonRoundTrip "draft.3 Core profile" m1cCoreProfile
  assertJsonRoundTrip "M1c feature matrix" m1cFeatureMatrix
  let profileText ←
    IO.FS.readFile "profiles/solcore-0.1.0-draft.3-core-m1c.json"
  let profileJson ←
    match Lean.Json.parse profileText with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"draft.3 profile JSON is invalid: {error}")
  assertTrue (profileJson == Lean.toJson m1cCoreProfile)
    "checked-in draft.3 profile differs from the Lean profile"

def testCoreWire : IO Unit := do
  for type in [Ty.unit, Ty.bool, Ty.word] do
    match Core.Wire.V1.decodeType (Core.Wire.V1.encodeType type) with
    | .ok decoded =>
        assertTrue (decoded == type) s!"Core type failed to round-trip: {reprStr type}"
    | .error error =>
        throw (IO.userError
          s!"encoded Core type did not decode: {(Lean.toJson error).compress}")
  let word42 ←
    match Word.ofNat? 42 with
    | some value => pure value
    | none => throw (IO.userError "42 must be an in-range Core word")
  let values : Array Value := #[
    .unit,
    .bool false,
    .bool true,
    .word Word.zero,
    .word word42
  ]
  for value in values do
    match Core.Wire.V1.decodeValue (Core.Wire.V1.encodeValue value) with
    | .ok decoded =>
        assertTrue (decoded == value) s!"Core value failed to round-trip: {reprStr value}"
    | .error error =>
        throw (IO.userError
          s!"encoded Core value did not decode: {(Lean.toJson error).compress}")
  let expressions : Array Core.Wire.V1.Expr := #[
    .unit,
    .bool false,
    .word word42,
    .var 3,
    .letE (.bool true) (.var 0),
    .ifE (.bool false) (.word Word.zero) (.word word42)
  ]
  for expr in expressions do
    match Core.Wire.V1.decodeExpr (Core.Wire.V1.encodeExpr expr) with
    | .ok decoded =>
        assertTrue (decoded == expr) s!"Core expression failed to round-trip: {reprStr expr}"
    | .error error =>
        throw (IO.userError
          s!"encoded Core expression did not decode: {(Lean.toJson error).compress}")
  let wireProgram : Core.Wire.V1.Program := {
    resultType := .bool
    body :=
      .letE
        (.bool true)
        (.ifE (.var 0) (.bool false) (.bool true))
  }
  assertTrue (wireProgram.toCore == coreConditionalProgram)
    "the Semantic Core v1 AST embedding changed the represented Core program"
  assertTrue
    (Core.Wire.V1.Program.ofCore? coreConditionalProgram == some wireProgram)
    "the M1a Core witness must remain representable in Semantic Core v1"
  match Core.Wire.V1.decodeProgram (Core.Wire.V1.encodeProgram wireProgram) with
  | .ok decoded =>
      assertTrue (decoded == wireProgram)
        "Semantic Core v1 Program failed to round-trip"
  | .error error =>
      throw (IO.userError
        s!"encoded Core Program did not decode: {(Lean.toJson error).compress}")
  let zeroText := "0x" ++ String.ofList (List.replicate 64 '0')
  let maximumText := "0x" ++ String.ofList (List.replicate 64 'f')
  let uppercaseText := "0x" ++ String.ofList (List.replicate 64 'F')
  assertTrue (Core.Wire.V1.encodeWordText Word.zero == zeroText)
    "Core word zero must use fixed-width lowercase hexadecimal"
  match Core.Wire.V1.decodeWordText maximumText with
  | .ok value =>
      assertTrue (value.val + 1 == wordModulus)
        "the maximum 256-bit Core word decoded incorrectly"
  | .error error =>
      throw (IO.userError
        s!"the maximum Core word did not decode: {(Lean.toJson error).compress}")
  assertCoreWireError "uppercase Core word"
    (Core.Wire.V1.decodeWordText uppercaseText) .invalidWord ""
  assertCoreWireError "short Core word"
    (Core.Wire.V1.decodeWordText "0x00") .invalidWord ""
  assertCoreWireError "missing Core word prefix"
    (Core.Wire.V1.decodeWordText (String.ofList (List.replicate 64 '0')))
    .invalidWord ""
  let unitWithUnknownField : Lean.Json :=
    .mkObj [("tag", "unit"), ("surprise", true)]
  assertCoreWireError "unknown expression field"
    (Core.Wire.V1.decodeExpr unitWithUnknownField) .unknownField "/surprise"
  let boolWithVariantField : Lean.Json :=
    .mkObj [("tag", "bool"), ("value", true), ("index", 0)]
  assertCoreWireError "field from another expression variant"
    (Core.Wire.V1.decodeExpr boolWithVariantField) .unknownField "/index"
  let missingBoolValue : Lean.Json := .mkObj [("tag", "bool")]
  assertCoreWireError "missing expression field"
    (Core.Wire.V1.decodeExpr missingBoolValue) .missingField "/value"
  let unknownTag : Lean.Json := .mkObj [("tag", "call")]
  assertCoreWireError "unknown expression tag"
    (Core.Wire.V1.decodeExpr unknownTag) .invalidTag "/tag"
  let postV1PrimitiveTag : Lean.Json := .mkObj [("tag", "unary")]
  assertCoreWireError "post-v1 primitive expression tag"
    (Core.Wire.V1.decodeExpr postV1PrimitiveTag) .invalidTag "/tag"
  let nonNaturalIndex : Lean.Json :=
    .mkObj [("tag", "var"), ("index", "zero")]
  assertCoreWireError "non-natural de Bruijn index"
    (Core.Wire.V1.decodeExpr nonNaturalIndex) .expectedNatural "/index"
  let decimalIntegralIndex ←
    match StrictJson.parse "{\"tag\":\"var\",\"index\":1.0}" with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"integral decimal Core fixture did not parse: {error}")
  match Core.Wire.V1.decodeExpr decimalIntegralIndex with
  | .ok (.var 1) => pure ()
  | .ok value =>
      throw (IO.userError
        s!"integral decimal index decoded unexpectedly: {reprStr value}")
  | .error error =>
      throw (IO.userError
        s!"integral decimal index did not decode: {(Lean.toJson error).compress}")
  let fractionalIndex ←
    match StrictJson.parse "{\"tag\":\"var\",\"index\":1.5}" with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"fractional Core fixture did not parse: {error}")
  assertCoreWireError "fractional de Bruijn index"
    (Core.Wire.V1.decodeExpr fractionalIndex) .expectedNatural "/index"
  let negativeIndex ←
    match StrictJson.parse "{\"tag\":\"var\",\"index\":-1}" with
    | .ok value => pure value
    | .error error =>
        throw (IO.userError s!"negative Core fixture did not parse: {error}")
  assertCoreWireError "negative de Bruijn index"
    (Core.Wire.V1.decodeExpr negativeIndex) .expectedNatural "/index"
  let wrongSchema :=
    (Core.Wire.V1.encodeProgram wireProgram).setObjVal!
      "schema" "solcore-semantic-core/v999"
  assertCoreWireError "unknown Core schema"
    (Core.Wire.V1.decodeProgram wrongSchema) .invalidSchema "/schema"
  let wrongResultType :=
    (Core.Wire.V1.encodeProgram wireProgram).setObjVal!
      "resultType" "boolean"
  assertCoreWireError "unknown Core result type"
    (Core.Wire.V1.decodeProgram wrongResultType) .invalidType "/resultType"
  let uppercaseWordProgram : Lean.Json :=
    .mkObj [
      ("schema", Core.Wire.V1.schemaVersion),
      ("resultType", "word"),
      ("body", .mkObj [("tag", "word"), ("value", uppercaseText)])
    ]
  assertCoreWireError "uppercase word in Program"
    (Core.Wire.V1.decodeProgram uppercaseWordProgram) .invalidWord "/body/value"
  assertCoreWireError "Core expression depth limit"
    (Core.Wire.V1.decodeExprWith { maxDepth := 0, maxNodes := 10 } (.mkObj [("tag", "unit")]))
    .depthLimitExceeded ""
  assertCoreWireError "Core expression node limit"
    (Core.Wire.V1.decodeExprWith { maxDepth := 10, maxNodes := 0 } (.mkObj [("tag", "unit")]))
    .nodeLimitExceeded ""

def assertCoreWireV2Error {α : Type}
    (name : String)
    (result : Except Core.Wire.V2.DecodeError α)
    (code : Core.Wire.V2.DecodeErrorCode)
    (path : String) :
    IO Unit := do
  match result with
  | .ok _ =>
      throw (IO.userError s!"{name} unexpectedly decoded")
  | .error error =>
      assertTrue (error.code == code)
        s!"{name} returned {error.code.wireName}, expected {code.wireName}"
      assertTrue (error.path.toPointer == path)
        s!"{name} failed at {error.path.toPointer}, expected {path}"

def testCoreWireV2 : IO Unit := do
  let unaryOps : Array Core.Wire.V2.UnaryOp := #[
    .boolNot,
    .wordNot
  ]
  for op in unaryOps do
    match Core.Wire.V2.decodeUnaryOp (Core.Wire.V2.encodeUnaryOp op) with
    | .ok decoded =>
        assertTrue (decoded == op)
          s!"Semantic Core v2 unary op failed to round-trip: {reprStr op}"
    | .error error =>
        throw (IO.userError
          s!"encoded v2 unary op did not decode: {(Lean.toJson error).compress}")
  let binaryOps : Array Core.Wire.V2.BinaryOp := #[
    .wordAdd,
    .wordSub,
    .wordMul,
    .wordDiv,
    .wordMod,
    .wordEq,
    .wordGt,
    .wordAnd,
    .wordOr,
    .wordXor,
    .wordShl,
    .wordShr
  ]
  for op in binaryOps do
    match Core.Wire.V2.decodeBinaryOp (Core.Wire.V2.encodeBinaryOp op) with
    | .ok decoded =>
        assertTrue (decoded == op)
          s!"Semantic Core v2 binary op failed to round-trip: {reprStr op}"
    | .error error =>
        throw (IO.userError
          s!"encoded v2 binary op did not decode: {(Lean.toJson error).compress}")
  let wireProgram : Core.Wire.V2.Program := {
    resultType := .word
    body :=
      .binary .wordAdd
        (.unary .wordNot (.word Word.zero))
        (.word (Word.ofNatModulo 1))
  }
  match Core.Wire.V2.decodeProgram (Core.Wire.V2.encodeProgram wireProgram) with
  | .ok decoded =>
      assertTrue (decoded == wireProgram)
        "Semantic Core v2 Program failed to round-trip"
  | .error error =>
      throw (IO.userError
        s!"encoded v2 Program did not decode: {(Lean.toJson error).compress}")
  assertTrue
    (Core.Wire.V2.Program.ofCore? wireProgram.toCore == some wireProgram)
    "the Semantic Core v2 embedding must have a partial inverse"
  assertTrue (wireProgram.toCore.run 8 == .done (.word Word.zero))
    "the decoded v2 primitive program must use the M1c evaluator"
  let encoded := Core.Wire.V2.encodeProgram wireProgram
  assertCoreWireError "Semantic Core v1 rejects a v2 program"
    (Core.Wire.V1.decodeProgram encoded) .invalidSchema "/schema"
  let v1Program : Core.Wire.V1.Program := {
    resultType := .bool
    body := .bool true
  }
  assertCoreWireV2Error "Semantic Core v2 rejects a v1 program"
    (Core.Wire.V2.decodeProgram (Core.Wire.V1.encodeProgram v1Program))
    .invalidSchema "/schema"
  let invalidOperator : Lean.Json :=
    .mkObj [
      ("schema", Core.Wire.V2.schemaVersion),
      ("resultType", "word"),
      ("body", .mkObj [
        ("tag", "binary"),
        ("op", "wordPow"),
        ("left", .mkObj [("tag", "word"), ("value", Core.Wire.V2.encodeWord Word.zero)]),
        ("right", .mkObj [("tag", "word"), ("value", Core.Wire.V2.encodeWord Word.zero)])
      ])
    ]
  assertCoreWireV2Error "unknown Semantic Core v2 operator"
    (Core.Wire.V2.decodeProgram invalidOperator) .invalidTag "/body/op"
  let binaryExpr : Core.Wire.V2.Expr :=
    .binary .wordAdd (.word Word.zero) (.word Word.zero)
  assertCoreWireV2Error "Semantic Core v2 expression depth limit"
    (Core.Wire.V2.decodeExprWith
      { maxDepth := 1, maxNodes := 10 }
      (Core.Wire.V2.encodeExpr binaryExpr))
    .depthLimitExceeded "/left"
  assertCoreWireV2Error "Semantic Core v2 expression node limit"
    (Core.Wire.V2.decodeExprWith
      { maxDepth := 10, maxNodes := 2 }
      (Core.Wire.V2.encodeExpr binaryExpr))
    .nodeLimitExceeded "/right"

def assertCheckError
    (name : String)
    (program : Program)
    (code : CheckErrorCode)
    (path : CheckPath) :
    IO CheckError := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == code)
        s!"{name} returned {error.codeName}, expected {code.name}"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      pure error

def testDetailedCoreChecker : IO Unit := do
  let unbound : Program := {
    resultType := .bool
    body :=
      .letE (.bool true)
        (.ifE (.bool true) (.var 2) (.bool false))
  }
  let unboundError ←
    assertCheckError "unbound variable" unbound .unboundVariable
      [.letBody, .ifThen]
  assertTrue (unboundError.data == .unboundVariable 2 1)
    "unbound-variable diagnostic arguments changed"
  let expectedBool : Program := {
    resultType := .bool
    body := .ifE .unit (.bool true) (.bool false)
  }
  let expectedBoolError ←
    assertCheckError "non-bool condition" expectedBool .expectedBool
      [.ifCondition]
  assertTrue (expectedBoolError.data == .expectedBool .unit)
    "expected-bool diagnostic arguments changed"
  let branchMismatch : Program := {
    resultType := .bool
    body := .ifE (.bool true) .unit (.bool false)
  }
  let branchError ←
    assertCheckError "branch type mismatch" branchMismatch .branchTypeMismatch
      [.ifElse]
  assertTrue (branchError.data == .branchTypeMismatch .unit .bool)
    "branch-mismatch diagnostic arguments changed"
  let resultMismatch : Program := {
    resultType := .unit
    body := .bool true
  }
  let resultError ←
    assertCheckError "declared result mismatch" resultMismatch
      .declaredResultTypeMismatch []
  assertTrue
    (resultError.data == .declaredResultTypeMismatch .unit .bool)
    "declared-result-mismatch diagnostic arguments changed"
  let unaryMismatch : Program := {
    resultType := .bool
    body := .unary .boolNot .unit
  }
  let unaryError ←
    assertCheckError "unary operand mismatch" unaryMismatch
      .primitiveOperandTypeMismatch [.unaryOperand]
  assertTrue
    (unaryError.data == .primitiveOperandTypeMismatch .bool .unit)
    "unary primitive diagnostic arguments changed"
  let binaryLeftMismatch : Program := {
    resultType := .word
    body := .binary .wordAdd (.bool true) (.var 99)
  }
  let binaryLeftError ←
    assertCheckError "binary left operand mismatch" binaryLeftMismatch
      .primitiveOperandTypeMismatch [.binaryLeft]
  assertTrue
    (binaryLeftError.data == .primitiveOperandTypeMismatch .word .bool)
    "binary-left primitive diagnostic arguments changed"
  let binaryRightMismatch : Program := {
    resultType := .word
    body := .binary .wordAdd (.word Word.zero) (.bool true)
  }
  let binaryRightError ←
    assertCheckError "binary right operand mismatch" binaryRightMismatch
      .primitiveOperandTypeMismatch [.binaryRight]
  assertTrue
    (binaryRightError.data == .primitiveOperandTypeMismatch .word .bool)
    "binary-right primitive diagnostic arguments changed"

def requestV2For
    (kind : Oracle.V2.QueryKind)
    (program : Option Program := none)
    (limits : Oracle.V2.CoreLimits := Oracle.V2.CoreLimits.default) :
    Oracle.V2.Request := {
  schema := Oracle.V2.schemaVersion
  id := "test-v2-request"
  spec := m1aLanguage.id
  profile := {
    id := m1aCoreProfile.id
    digest := m1aCoreProfileDigest
  }
  limits
  query := {
    kind
    program := program.bind fun coreProgram =>
      (Core.Wire.V1.Program.ofCore? coreProgram).map Core.Wire.V1.encodeProgram
  }
}

def handleV2OrThrow (request : Oracle.V2.Request) : IO Oracle.V2.Response := do
  match Oracle.V2.handle request with
  | .ok response =>
      assertTrue response.validationErrors.isEmpty
        s!"Oracle v2 produced an invalid response: {response.validationErrors}"
      pure response
  | .error error =>
      throw (IO.userError
        s!"valid Oracle v2 request failed: {(Lean.toJson error).compress}")

def assertExecutedBool
    (name : String)
    (response : Oracle.V2.Response)
    (expected : Bool) :
    IO Unit := do
  match response.verdict with
  | .executed observation =>
      assertTrue (observation.schema == Oracle.V2.valueObservationSchema)
        s!"{name} used the wrong observation schema"
      assertTrue
        (observation.value == .mkObj [
          ("resultType", Core.Wire.V1.encodeType .bool),
          ("value", Core.Wire.V1.encodeValue (.bool expected))
        ])
        s!"{name} returned an unexpected observation"
  | _ =>
      throw (IO.userError
        s!"{name} was not executed: {(Lean.toJson response).compress}")

def testOracleV2 : IO Unit := do
  let capabilities ←
    handleV2OrThrow (requestV2For .capabilities)
  match capabilities.verdict with
  | .accepted .protocol result =>
      assertTrue (result.schema == Oracle.V2.capabilitiesSchema)
        "Oracle v2 capability result schema changed"
      assertTrue
        (result.value.getObjValD "spec" == m1aLanguage.id)
        "Oracle v2 capabilities must identify draft.2"
      assertTrue
        (result.value.getObjValD "coreSchema" == Core.Wire.V1.schemaVersion)
        "Oracle v2 capabilities must identify the Core wire schema"
  | _ =>
      throw (IO.userError "Oracle v2 capabilities were not accepted")
  let checked ←
    handleV2OrThrow (requestV2For .coreCheck (some coreConditionalProgram))
  match checked.verdict with
  | .accepted .coreChecking result =>
      assertTrue (result.schema == Oracle.V2.checkResultSchema)
        "Core check result schema changed"
      assertTrue (result.value.getObjValD "resultType" == "bool")
        "Core check returned the wrong result type"
  | _ =>
      throw (IO.userError
        s!"well-typed Core program was not accepted: {(Lean.toJson checked).compress}")
  let illTyped : Program := {
    resultType := .bool
    body := .ifE .unit (.bool true) (.bool false)
  }
  let rejected ←
    handleV2OrThrow (requestV2For .coreCheck (some illTyped))
  match rejected.verdict with
  | .rejected .coreChecking diagnostic additional =>
      assertTrue (diagnostic.code == "core.check.expected-bool")
        "Oracle v2 Core diagnostic code changed"
      assertTrue (diagnostic.path == #["ifCondition"])
        "Oracle v2 Core diagnostic path changed"
      assertTrue additional.isEmpty
        "the deterministic Core checker must emit one primary diagnostic"
  | _ =>
      throw (IO.userError
        s!"ill-typed Core program was not rejected: {(Lean.toJson rejected).compress}")
  let evalRejected ←
    handleV2OrThrow (requestV2For .coreEval (some illTyped))
  match evalRejected.verdict with
  | .rejected .coreChecking diagnostic additional =>
      assertTrue
        (diagnostic.code == "core.check.expected-bool" &&
          diagnostic.path == #["ifCondition"] &&
          additional.isEmpty)
        "coreEval must use the same deterministic checker rejection as coreCheck"
  | _ =>
      throw (IO.userError
        s!"coreEval did not reject an ill-typed program: {(Lean.toJson evalRejected).compress}")
  let fuel6 : Oracle.V2.CoreLimits := {
    Oracle.V2.CoreLimits.default with
    evaluationSteps := 6
  }
  let outOfFuel ←
    handleV2OrThrow
      (requestV2For .coreEval (some coreConditionalProgram) fuel6)
  match outOfFuel.verdict with
  | .inconclusive .coreEvaluation .evaluationSteps 6 (some 6) => pure ()
  | _ =>
      throw (IO.userError
        s!"fuel 6 did not produce the exact resource result: {(Lean.toJson outOfFuel).compress}")
  let fuel7 : Oracle.V2.CoreLimits := {
    Oracle.V2.CoreLimits.default with
    evaluationSteps := 7
  }
  let executed ←
    handleV2OrThrow
      (requestV2For .coreEval (some coreConditionalProgram) fuel7)
  assertExecutedBool "fuel 7 Core evaluation" executed false
  let expensiveUnselectedBranch : Program := {
    resultType := .bool
    body :=
      .ifE (.bool true) (.bool false)
        (.letE (.bool true)
          (.letE (.bool false)
            (.letE (.bool true) (.var 0))))
  }
  let selectedBranchLimits : Oracle.V2.CoreLimits := {
    Oracle.V2.CoreLimits.default with
    evaluationSteps := 4
  }
  let selectedOnly ←
    handleV2OrThrow
      (requestV2For .coreEval (some expensiveUnselectedBranch) selectedBranchLimits)
  assertExecutedBool "selected-branch-only Core evaluation" selectedOnly false
  let depthZero : Oracle.V2.CoreLimits := {
    Oracle.V2.CoreLimits.default with
    inputDepth := 0
  }
  let depthLimited ←
    handleV2OrThrow
      (requestV2For .coreCheck (some {
        resultType := .unit
        body := .unit
      }) depthZero)
  match depthLimited.verdict with
  | .inconclusive .coreDecoding .inputDepth 0 none => pure ()
  | _ =>
      throw (IO.userError
        s!"input depth limit was not reported: {(Lean.toJson depthLimited).compress}")
  let nodeOne : Oracle.V2.CoreLimits := {
    Oracle.V2.CoreLimits.default with
    inputNodes := 1
  }
  let nodesLimited ←
    handleV2OrThrow
      (requestV2For .coreCheck (some {
        resultType := .bool
        body := .ifE (.bool true) (.bool true) (.bool false)
      }) nodeOne)
  match nodesLimited.verdict with
  | .inconclusive .coreDecoding .inputNodes 1 none => pure ()
  | _ =>
      throw (IO.userError
        s!"input node limit was not reported: {(Lean.toJson nodesLimited).compress}")
  let wrongProfile : Oracle.V2.Request := {
    requestV2For .coreCheck (some coreConditionalProgram) with
    profile := {
      id := draftCoreProfile.id
      digest := draftCoreProfileDigest
    }
  }
  match Oracle.V2.handle wrongProfile with
  | .error error =>
      assertTrue (error.code == "invalid-request")
        "profile mismatch must be an Oracle v2 protocol error"
  | .ok response =>
      throw (IO.userError
        s!"draft.1 profile accessed M1a semantics: {(Lean.toJson response).compress}")
  let wrongDigest : Oracle.V2.Request := {
    requestV2For .coreCheck (some coreConditionalProgram) with
    profile := {
      id := m1aCoreProfile.id
      digest := draftCoreProfileDigest
    }
  }
  assertTrue (isError (Oracle.V2.handle wrongDigest))
    "a mismatched M1a profile digest must be rejected"
  let requestWithUnknownField :=
    (Lean.toJson (requestV2For .capabilities)).setObjVal! "surprise" true
  match Oracle.V2.decodeRequest requestWithUnknownField with
  | .error error =>
      assertTrue (error.code == "unknown-field" && error.path == "/surprise")
        "Oracle v2 must strictly reject unknown request fields"
  | .ok _ =>
      throw (IO.userError "Oracle v2 accepted an unknown request field")
  let decimalLimit : Lean.Json := .num {
    mantissa := 10
    exponent := 1
  }
  let requestJson := Lean.toJson (requestV2For .capabilities)
  let decimalLimits :=
    (requestJson.getObjValD "limits").setObjVal! "inputDepth" decimalLimit
  match Oracle.V2.decodeRequest (requestJson.setObjVal! "limits" decimalLimits) with
  | .ok request =>
      assertTrue (request.limits.inputDepth == 1)
        "Oracle v2 integral decimal limits must use their mathematical value"
  | .error error =>
      throw (IO.userError
        s!"Oracle v2 rejected an integral decimal limit: {error.display}")

def requestV3For
    (kind : Oracle.V3.QueryKind)
    (program : Option Program := none)
    (limits : Oracle.V3.CoreLimits := Oracle.V3.CoreLimits.default) :
    Oracle.V3.Request := {
  schema := Oracle.V3.schemaVersion
  id := "test-v3-request"
  spec := m1cLanguage.id
  profile := {
    id := m1cCoreProfile.id
    digest := m1cCoreProfileDigest
  }
  limits
  query := {
    kind
    program := program.bind fun coreProgram =>
      (Core.Wire.V2.Program.ofCore? coreProgram).map Core.Wire.V2.encodeProgram
  }
}

def handleV3OrThrow (request : Oracle.V3.Request) : IO Oracle.V3.Response := do
  match Oracle.V3.handle request with
  | .ok response =>
      let errors := Oracle.V3.Response.validationErrors response
      assertTrue errors.isEmpty
        s!"Oracle v3 produced an invalid response: {errors}"
      pure response
  | .error error =>
      throw (IO.userError
        s!"valid Oracle v3 request failed: {(Lean.toJson error).compress}")

def assertV3ExecutedWord
    (name : String)
    (response : Oracle.V3.Response)
    (expected : Word) :
    IO Unit := do
  match response.verdict with
  | .executed observation =>
      assertTrue (observation.schema == Oracle.V3.valueObservationSchema)
        s!"{name} used the wrong observation schema"
      assertTrue
        (observation.value == .mkObj [
          ("resultType", Core.Wire.V2.encodeType .word),
          ("value", Core.Wire.V2.encodeValue (.word expected))
        ])
        s!"{name} returned an unexpected word observation"
  | _ =>
      throw (IO.userError
        s!"{name} was not executed: {(Lean.toJson response).compress}")

def testOracleV3 : IO Unit := do
  let capabilities ←
    handleV3OrThrow (requestV3For .capabilities)
  match capabilities.verdict with
  | .accepted .protocol result =>
      assertTrue (result.schema == Oracle.V3.capabilitiesSchema)
        "Oracle v3 capability result schema changed"
      assertTrue
        (result.value.getObjValD "spec" == m1cLanguage.id)
        "Oracle v3 capabilities must identify draft.3"
      assertTrue
        (result.value.getObjValD "coreSchema" == Core.Wire.V2.schemaVersion)
        "Oracle v3 capabilities must identify Semantic Core v2"
  | _ =>
      throw (IO.userError "Oracle v3 capabilities were not accepted")
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let three := Word.ofNatModulo 3
  let addition : Program := {
    resultType := .word
    body := .binary .wordAdd (.word one) (.word two)
  }
  let checked ←
    handleV3OrThrow (requestV3For .coreCheck (some addition))
  match checked.verdict with
  | .accepted .coreChecking result =>
      assertTrue
        (result.schema == Oracle.V3.checkResultSchema &&
          result.value.getObjValD "resultType" == "word")
        "Oracle v3 Core check returned an unexpected result"
  | _ =>
      throw (IO.userError
        s!"Oracle v3 did not accept wordAdd: {(Lean.toJson checked).compress}")
  let fuel4 : Oracle.V3.CoreLimits := {
    Oracle.V3.CoreLimits.default with
    evaluationSteps := 4
  }
  let outOfFuel ←
    handleV3OrThrow (requestV3For .coreEval (some addition) fuel4)
  match outOfFuel.verdict with
  | .inconclusive .coreEvaluation .evaluationSteps 4 (some 4) => pure ()
  | _ =>
      throw (IO.userError
        s!"Oracle v3 fuel boundary changed: {(Lean.toJson outOfFuel).compress}")
  let fuel5 : Oracle.V3.CoreLimits := {
    Oracle.V3.CoreLimits.default with
    evaluationSteps := 5
  }
  let executed ←
    handleV3OrThrow (requestV3For .coreEval (some addition) fuel5)
  assertV3ExecutedWord "Oracle v3 wordAdd" executed three
  let unaryMismatch : Program := {
    resultType := .bool
    body := .unary .boolNot .unit
  }
  let rejected ←
    handleV3OrThrow (requestV3For .coreCheck (some unaryMismatch))
  match rejected.verdict with
  | .rejected .coreChecking diagnostic additional =>
      assertTrue
        (diagnostic.code == "core.check.primitive-operand-type-mismatch" &&
          diagnostic.path == #["unaryOperand"] &&
          diagnostic.arguments == .mkObj [
            ("expected", "bool"),
            ("actual", "unit")
          ] &&
          additional.isEmpty)
        "Oracle v3 primitive diagnostic changed"
  | _ =>
      throw (IO.userError
        s!"Oracle v3 did not reject an invalid boolNot: {(Lean.toJson rejected).compress}")
  let v2Wire ←
    match Core.Wire.V2.Program.ofCore? addition with
    | some program => pure (Core.Wire.V2.encodeProgram program)
    | none => throw (IO.userError "wordAdd must be representable in Semantic Core v2")
  let v2RequestWithV2Wire : Oracle.V2.Request := {
    requestV2For .coreCheck with
    query := {
      kind := .coreCheck
      program := some v2Wire
    }
  }
  match Oracle.V2.handle v2RequestWithV2Wire with
  | .error error =>
      assertTrue (error.code == "core.wire.invalid-schema")
        "Oracle v2 must reject Semantic Core v2"
  | .ok response =>
      throw (IO.userError
        s!"Oracle v2 accepted Semantic Core v2: {(Lean.toJson response).compress}")
  let v1Wire : Core.Wire.V1.Program := {
    resultType := .bool
    body := .bool true
  }
  let v3RequestWithV1Wire : Oracle.V3.Request := {
    requestV3For .coreCheck with
    query := {
      kind := .coreCheck
      program := some (Core.Wire.V1.encodeProgram v1Wire)
    }
  }
  match Oracle.V3.handle v3RequestWithV1Wire with
  | .error error =>
      assertTrue (error.code == "core.wire.invalid-schema")
        "Oracle v3 must reject Semantic Core v1"
  | .ok response =>
      throw (IO.userError
        s!"Oracle v3 accepted Semantic Core v1: {(Lean.toJson response).compress}")

def testOracleVersionDispatch : IO Unit := do
  let v3Program : Program := {
    resultType := .bool
    body := .unary .boolNot (.bool false)
  }
  let v3Eval :=
    processJsonLine
      (Lean.toJson
        (requestV3For .coreEval (some v3Program) {
          Oracle.V3.CoreLimits.default with
          evaluationSteps := 3
        })).compress
  assertTrue (v3Eval.getObjValD "schema" == Oracle.V3.schemaVersion)
    "stream dispatcher did not route an Oracle v3 record"
  assertTrue
    ((v3Eval.getObjValD "verdict").getObjValD "kind" == "executed")
    "stream dispatcher did not execute a valid Oracle v3 primitive request"
  let v2Eval :=
    processJsonLine
      (Lean.toJson
        (requestV2For .coreEval (some coreConditionalProgram) {
          Oracle.V2.CoreLimits.default with
          evaluationSteps := 7
        })).compress
  assertTrue (v2Eval.getObjValD "schema" == Oracle.V2.schemaVersion)
    "stream dispatcher did not route an Oracle v2 record"
  assertTrue (v2Eval.getObjValD "query" == "coreEval")
    "stream dispatcher changed the Oracle v2 query"
  assertTrue
    ((v2Eval.getObjValD "verdict").getObjValD "kind" == "executed")
    "stream dispatcher did not execute a valid Oracle v2 Core request"
  let v1Check :=
    processJsonLine (Lean.toJson (requestFor .check)).compress
  assertTrue (v1Check.getObjValD "schema" == schemaVersion)
    "stream dispatcher did not preserve Oracle v1"
  assertTrue
    ((v1Check.getObjValD "verdict").getObjValD "kind" == "unsupported")
    "Oracle v1 check must remain unsupported"
  let v1Eval :=
    processJsonLine (Lean.toJson (requestFor .eval)).compress
  assertTrue
    ((v1Eval.getObjValD "verdict").getObjValD "kind" == "unsupported")
    "Oracle v1 eval must remain unsupported"
  let v1Capabilities :=
    processJsonLine (Lean.toJson (requestFor .capabilities)).compress
  assertTrue
    ((v1Capabilities.getObjValD "verdict").getObjValD "kind" == "accepted")
    "Oracle v1 capabilities must remain accepted after adding v2 and v3"

def testOracle : IO Unit := do
  assertJsonRoundTrip "request" (requestFor .check)
  assertJsonRoundTrip "capability report" capabilityReport
  for kind in QueryKind.all do
    let response ←
      match handle (requestFor kind) with
      | .ok response => pure response
      | .error error =>
          throw (IO.userError s!"valid {reprStr kind} request failed: {error.display}")
    let expected := if kind == .capabilities then VerdictKind.accepted else .unsupported
    assertTrue (response.verdict.kind == expected)
      s!"unexpected verdict for {reprStr kind}"
    assertTrue (response.profile == (requestFor kind).profile)
      "response must identify the exact request profile"
    assertTrue (response.query == kind) "response must identify the query"
    assertTrue (response.verdict.validationErrorsFor kind).isEmpty
      s!"invalid verdict for {reprStr kind}: {response.verdict.validationErrorsFor kind}"
    assertJsonRoundTrip s!"{reprStr kind} response" response
    match decodeResponse (Lean.toJson response) with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"strict response decode failed: {error}")
  let malformedPathRequest : Request := {
    requestFor .check with
    workspace := some {
      entry := "../main.solc"
      sources := #[{
        path := "../main.solc"
        content := ""
      }]
    }
  }
  assertTrue (isError (handle malformedPathRequest))
    "parent-relative workspace paths must be protocol errors"
  let unknownSchema := { requestFor .capabilities with schema := "solcore-oracle/v999" }
  assertTrue (isError (handle unknownSchema)) "unknown schemas must be protocol errors"
  let requestWithUnknownField :=
    (Lean.toJson (requestFor .capabilities)).setObjVal! "surprise" true
  assertTrue (isError (decodeRequest requestWithUnknownField))
    "unknown request fields must be protocol errors"
  let requestWithoutLimits :=
    (Lean.toJson (requestFor .capabilities)).setObjVal! "limits" .null
  assertTrue (isError (decodeRequest requestWithoutLimits))
    "null limits must not be accepted"
  let diagnostic : Diagnostic := {
    code := "test-error"
    severity := .error
    phase := .checking
    primary := {
      source := "main.solc"
      startByte := 0
      endByte := 1
    }
  }
  let verdicts : Array (QueryKind × Verdict) := #[
    (.capabilities, .accepted .protocol {
      schema := capabilitiesSchema
      value := Lean.toJson capabilityReport
    }),
    (.check, .rejected .checking diagnostic #[]),
    (.elaborate, .unsupported .elaboration #[.modules]),
    (.eval, .inconclusive .evaluation .evaluationSteps 10 (some 10)),
    (.eval, .executed {
      schema := "solcore-value-observation/v1"
      value := .null
    }),
    (.check, .internalError (some .checking) "test-invariant")
  ]
  for (query, verdict) in verdicts do
    assertTrue (verdict.validationErrorsFor query).isEmpty
      s!"sample verdict is invalid: {verdict.validationErrorsFor query}"
    assertJsonRoundTrip "verdict" verdict
  let capabilityResponse ←
    match handle (requestFor .capabilities) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid capabilities request failed: {error.display}")
  let capabilityResponseJson := Lean.toJson capabilityResponse
  assertTrue
    (isError (decodeResponse (capabilityResponseJson.setObjVal! "id" "")))
    "empty response ids must be rejected"
  let capabilityVerdictJson := capabilityResponseJson.getObjValD "verdict"
  let capabilityResultJson := capabilityVerdictJson.getObjValD "result"
  let resultWithUnknownField := capabilityResultJson.setObjVal! "surprise" true
  let verdictWithUnknownResultField :=
    capabilityVerdictJson.setObjVal! "result" resultWithUnknownField
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithUnknownResultField)))
    "unknown result payload fields must be rejected"
  let resultWithNullValue := capabilityResultJson.setObjVal! "value" .null
  let verdictWithNullCapability :=
    capabilityVerdictJson.setObjVal! "result" resultWithNullValue
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithNullCapability)))
    "capabilities result values must decode as CapabilityReport"
  let reportWithUnknownField :=
    (capabilityResultJson.getObjValD "value").setObjVal! "surprise" true
  let resultWithUnknownReportField :=
    capabilityResultJson.setObjVal! "value" reportWithUnknownField
  let verdictWithUnknownReportField :=
    capabilityVerdictJson.setObjVal! "result" resultWithUnknownReportField
  assertTrue
    (isError (decodeResponse
      (capabilityResponseJson.setObjVal! "verdict" verdictWithUnknownReportField)))
    "unknown capability report fields must be rejected"
  let checkResponse ←
    match handle (requestFor .check) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid check request failed: {error.display}")
  let diagnosticWithUnknownField :=
    (Lean.toJson diagnostic).setObjVal! "surprise" true
  let rejectedWithUnknownDiagnostic := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.rejected),
    ("phase", Lean.toJson Phase.checking),
    ("diagnostics", Lean.Json.arr #[diagnosticWithUnknownField])
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson checkResponse).setObjVal! "verdict" rejectedWithUnknownDiagnostic)))
    "unknown diagnostic fields must be rejected"
  let spanWithUnknownField :=
    (Lean.toJson diagnostic.primary).setObjVal! "surprise" true
  let diagnosticWithUnknownSpan :=
    (Lean.toJson diagnostic).setObjVal! "primary" spanWithUnknownField
  let rejectedWithUnknownSpan := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.rejected),
    ("phase", Lean.toJson Phase.checking),
    ("diagnostics", Lean.Json.arr #[diagnosticWithUnknownSpan])
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson checkResponse).setObjVal! "verdict" rejectedWithUnknownSpan)))
    "unknown source span fields must be rejected"
  let evalResponse ←
    match handle (requestFor .eval) with
    | .ok response => pure response
    | .error error =>
        throw (IO.userError s!"valid eval request failed: {error.display}")
  let observationWithUnknownField :=
    (Lean.toJson (show ObservationPayload from {
      schema := "solcore-value-observation/v1"
      value := .null
    })).setObjVal! "surprise" true
  let executedWithUnknownObservation := Lean.Json.mkObj [
    ("kind", Lean.toJson VerdictKind.executed),
    ("observation", observationWithUnknownField)
  ]
  assertTrue
    (isError (decodeResponse
      ((Lean.toJson evalResponse).setObjVal! "verdict" executedWithUnknownObservation)))
    "unknown observation payload fields must be rejected"
  let malformedOutput := processJsonLine "{"
  assertTrue (malformedOutput.getObjValD "kind" == "protocolError")
    "malformed JSON must produce a protocolError record"
  let recoveredOutput :=
    processJsonLine (Lean.toJson (requestFor .capabilities)).compress
  let recoveredVerdict := recoveredOutput.getObjValD "verdict"
  assertTrue (recoveredVerdict.getObjValD "kind" == "accepted")
    "a valid record after a malformed record must still be accepted"
  let encodedRequest := (Lean.toJson (requestFor .capabilities)).compress
  let duplicateIdRequest :=
    encodedRequest.replace
      "\"id\":\"test-request\""
      "\"id\":\"first\",\"id\":\"second\""
  let duplicateIdOutput := processJsonLine duplicateIdRequest
  assertTrue (duplicateIdOutput.getObjValD "kind" == "protocolError")
    "duplicate JSON object keys must be rejected"
  let shapeErrorOutput := processJsonLine requestWithUnknownField.compress
  assertTrue (shapeErrorOutput.getObjValD "id" == "test-request")
    "shape errors must preserve a usable request id"
  for unsafePath in
      ["/main.solc", "../main.solc", "a/./main.solc", "a//main.solc", "C:/main.solc",
        "a\\main.solc"] do
    assertTrue (!isSafeSourcePath unsafePath) s!"unsafe path was accepted: {unsafePath}"

def testSchemaJson : IO Unit := do
  for path in
      ["schema/oracle-v1.schema.json", "schema/oracle-v2.schema.json",
        "schema/semantic-core-v1.schema.json", "schema/semantic-core-v2.schema.json",
        "metadata/baselines.json",
        "metadata/standard-library.json", "profiles/manifest.json",
        "profiles/solcore-0.1.0-draft.2-core-m1a.json",
        "profiles/solcore-0.1.0-draft.3-core-m1c.json",
        "Tests/golden/wire-manifest.json"] do
    let text ← IO.FS.readFile path
    match Lean.Json.parse text with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"{path} is invalid JSON: {error}")
  let requestText ← IO.FS.readFile "Tests/golden/check-request.ndjson"
  let requestJson ←
    match StrictJson.parse requestText.trimAscii.copy with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"golden request is invalid: {error}")
  match decodeRequest requestJson with
  | .ok _ => pure ()
  | .error error => throw (IO.userError s!"golden request violates the wire contract: {error}")
  let responseText ← IO.FS.readFile "Tests/golden/check-response.ndjson"
  let responseJson ←
    match StrictJson.parse responseText.trimAscii.copy with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"golden response is invalid: {error}")
  match decodeResponse responseJson with
  | .ok response =>
      assertTrue (Lean.toJson response == responseJson)
        "golden response is not the canonical Lean encoding"
  | .error error => throw (IO.userError s!"golden response violates the wire contract: {error}")
  let coreGoldenPairs := [
    ("Tests/golden/core-check-rejected-request.ndjson",
      "Tests/golden/core-check-rejected-response.ndjson"),
    ("Tests/golden/core-eval-out-of-fuel-request.ndjson",
      "Tests/golden/core-eval-out-of-fuel-response.ndjson"),
    ("Tests/golden/core-eval-request.ndjson",
      "Tests/golden/core-eval-response.ndjson"),
    ("Tests/golden/core-eval-selected-branch-request.ndjson",
      "Tests/golden/core-eval-selected-branch-response.ndjson"),
    ("Tests/golden/core-wire-invalid-request.ndjson",
      "Tests/golden/core-wire-invalid-response.ndjson")
  ]
  for (requestPath, responsePath) in coreGoldenPairs do
    let coreRequestText ← IO.FS.readFile requestPath
    let expectedText ← IO.FS.readFile responsePath
    let expected ←
      match StrictJson.parse expectedText.trimAscii.copy with
      | .ok value => pure value
      | .error error =>
          throw (IO.userError s!"{responsePath} is invalid strict JSON: {error}")
    let actual := processJsonLine coreRequestText
    assertTrue (actual == expected)
      s!"{requestPath} did not produce its checked-in golden response"

def run : IO Unit := do
  testProfile
  testFeatureMatrix
  testSemanticCore
  testPrimitiveAlgebra
  testM1cKernel
  testM1bProfile
  testM1cProfile
  testCoreWire
  testCoreWireV2
  testDetailedCoreChecker
  testOracle
  testOracleV2
  testOracleV3
  testOracleVersionDispatch
  testSchemaJson

end Tests

def main : IO UInt32 := do
  Tests.run
  IO.println "solcore-lean M0/M1a/M1b/M1c primitive tests passed"
  return 0
