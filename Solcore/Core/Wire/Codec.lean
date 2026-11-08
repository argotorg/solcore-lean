import Lean.Data.Json
import Solcore.Util.Json
import Solcore.Core.Wire.Syntax
import Solcore.ContractRuntime.Internal.ScalarText

/-!
# Wire codecs

The JSON codecs of the Core wire boundary, with decoding that counts nodes, depth and integer bytes
against a `Wire.CoreBudgetLimits`. The sections run from strict JSON through scalars, operators,
types and expressions to whole programs: `Wire.decodeProgram`, `Wire.canonicalizeProgramWithBudget`
and `Wire.canonicalizeProgramWithBudget_of_decode_eq_ok`.
-/

section
-- leanmerge: from Solcore.Core.Wire.Codec.Foundation
/-! Strict JSON-decoding primitives owned by Semantic Core Wire. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

inductive PathSegment where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, BEq, DecidableEq

structure DecodePath where
  segments : Array PathSegment := #[]
  deriving Repr, BEq, DecidableEq

namespace DecodePath

def root : DecodePath := {}

def field (path : DecodePath) (name : String) : DecodePath :=
  { segments := path.segments.push (.field name) }

def index (path : DecodePath) (value : Nat) : DecodePath :=
  { segments := path.segments.push (.index value) }

private def escapeToken (value : String) : String :=
  (value.replace "~" "~0").replace "/" "~1"

private def segmentToken : PathSegment → String
  | .field name => escapeToken name
  | .index value => toString value

def toPointer (path : DecodePath) : String :=
  path.segments.foldl
    (fun result segment => result ++ "/" ++ segmentToken segment) ""

end DecodePath

inductive DecodeErrorCode where
  | expectedObject
  | expectedArray
  | expectedString
  | expectedBool
  | expectedNatural
  | missingField
  | unknownField
  | invalidSchema
  | invalidTag
  | invalidType
  | invalidWord
  | invalidInteger
  deriving Repr, BEq, DecidableEq

namespace DecodeErrorCode

def wireName : DecodeErrorCode → String
  | .expectedObject => "expected-object"
  | .expectedArray => "expected-array"
  | .expectedString => "expected-string"
  | .expectedBool => "expected-bool"
  | .expectedNatural => "expected-natural"
  | .missingField => "missing-field"
  | .unknownField => "unknown-field"
  | .invalidSchema => "invalid-schema"
  | .invalidTag => "invalid-tag"
  | .invalidType => "invalid-type"
  | .invalidWord => "invalid-word"
  | .invalidInteger => "invalid-integer"

end DecodeErrorCode

structure DecodeError where
  path : DecodePath
  code : DecodeErrorCode
  arguments : Lean.Json := .null

namespace DecodeError

def toJson (error : DecodeError) : Lean.Json :=
  .mkObj [
    ("path", error.path.toPointer),
    ("code", error.code.wireName),
    ("arguments", error.arguments)
  ]

end DecodeError

instance : Lean.ToJson DecodeError := ⟨DecodeError.toJson⟩

abbrev DecodeResult (α : Type) := Except DecodeError α

def failAt {α : Type}
    (path : DecodePath)
    (code : DecodeErrorCode)
    (arguments : Lean.Json := .null) :
    DecodeResult α :=
  .error { path, code, arguments }

private def jsonKind : Lean.Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

private def expectedArguments
    (expected : String)
    (actual : Lean.Json) :
    Lean.Json :=
  .mkObj [
    ("expected", expected),
    ("actual", jsonKind actual)
  ]

private def lexicographicMinimum? : List String → Option String
  | [] => none
  | first :: rest =>
      some <| rest.foldl (fun current candidate =>
        if (compare candidate current).isLE then candidate else current) first

/-- Accept an object only when its key set is exactly the expected one. -/
def ensureExactObject
    (path : DecodePath)
    (json : Lean.Json)
    (allowed required : List String) :
    DecodeResult Unit := do
  let fields ←
    match json with
    | .obj fields => pure fields
    | _ => failAt path .expectedObject (expectedArguments "object" json)
  let unknown? := lexicographicMinimum? <|
    fields.keys.filter (fun key => !allowed.contains key)
  let missing? := lexicographicMinimum? <|
    required.filter (fun key => !fields.contains key)
  match unknown?, missing? with
  | none, none => pure ()
  | some key, none =>
      failAt (path.field key) .unknownField (.mkObj [("field", key)])
  | none, some key =>
      failAt (path.field key) .missingField (.mkObj [("field", key)])
  | some unknown, some missing =>
      if (compare unknown missing).isLE then
        failAt (path.field unknown) .unknownField (.mkObj [("field", unknown)])
      else
        failAt (path.field missing) .missingField (.mkObj [("field", missing)])

def requireField
    (path : DecodePath)
    (json : Lean.Json)
    (name : String) :
    DecodeResult Lean.Json :=
  match json with
  | .obj _ =>
      match json.getObjVal? name with
      | .ok value => pure value
      | .error _ =>
          failAt (path.field name) .missingField (.mkObj [("field", name)])
  | _ => failAt path .expectedObject (expectedArguments "object" json)

def decodeStringAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult String :=
  match json with
  | .str value => pure value
  | _ => failAt path .expectedString (expectedArguments "string" json)

def decodeBoolAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Bool :=
  match json with
  | .bool value => pure value
  | _ => failAt path .expectedBool (expectedArguments "boolean" json)

def decodeNatAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Nat :=
  match Util.jsonNatural? json with
  | some value => pure value
  | none => failAt path .expectedNatural (expectedArguments "number" json)

def decodeListAt {α : Type}
    (decodeValue : DecodePath → Lean.Json → DecodeResult α)
    (path : DecodePath) :
    Nat → List Lean.Json → DecodeResult (List α)
  | _, [] => pure []
  | index, json :: rest => do
      let value ← decodeValue (path.index index) json
      let values ← decodeListAt decodeValue path (index + 1) rest
      pure (value :: values)

def decodeArrayAt {α : Type}
    (decodeValue : DecodePath → Lean.Json → DecodeResult α)
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult (List α) :=
  match json with
  | .arr values => decodeListAt decodeValue path 0 values.toList
  | _ => failAt path .expectedArray (expectedArguments "array" json)

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.Budget
/-! Typed Core-resource accounting, kept separate from protocol failures. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

inductive CoreBudgetResource where
  | depth
  | nodes
  | integerBytes
  deriving Repr, BEq, DecidableEq

structure CoreBudgetLimits where
  maxDepth : Nat
  maxNodes : Nat
  /-- Cumulative UTF-8 bytes of integer literal spellings, before parsing. -/
  maxIntegerBytes : Nat := 1000000
  deriving Repr, BEq, DecidableEq

namespace CoreBudgetLimits

def default : CoreBudgetLimits := {
  maxDepth := 1024
  maxNodes := 1000000
}

end CoreBudgetLimits

structure CoreBudgetState where
  consumedNodes : Nat := 0
  consumedIntegerBytes : Nat := 0
  deriving Repr, BEq, DecidableEq

namespace CoreBudgetState

def initial : CoreBudgetState := {}

end CoreBudgetState

/-- Demand at the first Core position which could not be consumed. -/
structure CoreBudgetExhaustion where
  resource : CoreBudgetResource
  limit : Nat
  consumed : Nat
  exceeded : limit < consumed
  deriving Repr, DecidableEq

namespace CoreBudgetExhaustion

instance : BEq CoreBudgetExhaustion :=
  ⟨fun left right =>
    left.resource == right.resource && left.limit == right.limit &&
      left.consumed == right.consumed⟩

end CoreBudgetExhaustion

inductive CoreDecodeFailure where
  | protocol (error : DecodeError)
  | exhausted (exhaustion : CoreBudgetExhaustion)

abbrev CoreDecodeResult (α : Type) := Except CoreDecodeFailure α

def liftProtocol {α : Type} (result : DecodeResult α) : CoreDecodeResult α :=
  result.mapError .protocol

/-- Consume depth first, then the cumulative node counter. -/
def consumeCoreNode
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat) :
    CoreDecodeResult CoreBudgetState := do
  if exceeded : limits.maxDepth < depth then
    throw (.exhausted {
      resource := .depth
      limit := limits.maxDepth
      consumed := depth
      exceeded
    })
  let consumed := state.consumedNodes + 1
  if exceeded : limits.maxNodes < consumed then
    throw (.exhausted {
      resource := .nodes
      limit := limits.maxNodes
      consumed
      exceeded
    })
  pure { state with consumedNodes := consumed }

@[simp] theorem consumeCoreNode_at_limits
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (depthFits : depth ≤ limits.maxDepth)
    (nodesFit : state.consumedNodes + 1 ≤ limits.maxNodes) :
    consumeCoreNode limits state depth =
      .ok { state with consumedNodes := state.consumedNodes + 1 } := by
  simp [consumeCoreNode, Nat.not_lt.mpr depthFits, Nat.not_lt.mpr nodesFit]
  rfl

/-- Consume the spelling before any conversion to an arbitrary precision integer. -/
def consumeIntegerBytes
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (bytes : Nat) : CoreDecodeResult CoreBudgetState := do
  let consumed := state.consumedIntegerBytes + bytes
  if exceeded : limits.maxIntegerBytes < consumed then
    throw (.exhausted {
      resource := .integerBytes
      limit := limits.maxIntegerBytes
      consumed
      exceeded
    })
  pure { state with consumedIntegerBytes := consumed }

@[simp] theorem consumeIntegerBytes_at_limits
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (bytes : Nat)
    (fits : state.consumedIntegerBytes + bytes ≤ limits.maxIntegerBytes) :
    consumeIntegerBytes limits state bytes =
      .ok { state with consumedIntegerBytes := state.consumedIntegerBytes + bytes } := by
  simp [consumeIntegerBytes, Nat.not_lt.mpr fits]
  rfl

theorem consumeIntegerBytes_of_eq_ok
    {limits : CoreBudgetLimits} {state finalState : CoreBudgetState} {bytes : Nat}
    (success : consumeIntegerBytes limits state bytes = .ok finalState) :
    finalState.consumedIntegerBytes = state.consumedIntegerBytes + bytes ∧
    finalState.consumedIntegerBytes ≤ limits.maxIntegerBytes ∧
    finalState.consumedNodes = state.consumedNodes := by
  by_cases exceeded : limits.maxIntegerBytes < state.consumedIntegerBytes + bytes
  · simp [consumeIntegerBytes, exceeded] at success
    cases success
  · rw [consumeIntegerBytes_at_limits limits state bytes (Nat.le_of_not_gt exceeded)] at success
    cases success
    exact ⟨rfl, Nat.le_of_not_gt exceeded, rfl⟩

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.Scalar
/-! Canonical scalar and identity codecs for Semantic Core Wire. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

/-- Integers use signed decimal strings rather than JSON numbers. -/
def encodeIntegerText (value : Int) : String := toString value

private def decodeCanonicalIntegerTextAt
    (path : DecodePath) (text : String) : DecodeResult Int :=
  match text.toInt? with
  | some value =>
      if encodeIntegerText value = text then pure value
      else failAt path .invalidInteger (.mkObj [("reason", "canonical-decimal")])
  | none => failAt path .invalidInteger (.mkObj [("reason", "signed-decimal")])

private theorem encodeIntegerText_of_decodeCanonicalIntegerTextAt_eq_ok
    (path : DecodePath) (text : String) (value : Int)
    (success : decodeCanonicalIntegerTextAt path text = .ok value) :
    encodeIntegerText value = text := by
  unfold decodeCanonicalIntegerTextAt at success
  split at success
  · split at success
    · cases success
      assumption
    · contradiction
  · contradiction

/-- The byte budget is consumed before parsing even malformed spellings. -/
def decodeIntegerTextAtWithBudget
    (limits : CoreBudgetLimits) (state : CoreBudgetState)
    (path : DecodePath) (text : String) : CoreDecodeResult (Int × CoreBudgetState) := do
  let state ← consumeIntegerBytes limits state text.utf8ByteSize
  let value ← liftProtocol <| decodeCanonicalIntegerTextAt path text
  pure (value, state)

theorem encodeIntegerText_of_decodeIntegerTextAtWithBudget_eq_ok
    (limits : CoreBudgetLimits) (state finalState : CoreBudgetState)
    (path : DecodePath) (text : String) (value : Int)
    (success : decodeIntegerTextAtWithBudget limits state path text = .ok (value, finalState)) :
    encodeIntegerText value = text := by
  unfold decodeIntegerTextAtWithBudget at success
  cases consumed : consumeIntegerBytes limits state text.utf8ByteSize with
  | error error =>
      simp [consumed] at success
      cases success
  | ok consumedState =>
      cases decoded : decodeCanonicalIntegerTextAt path text with
      | error error =>
          simp [consumed, liftProtocol, decoded] at success
          cases success
      | ok decodedValue =>
          simp [consumed, liftProtocol, decoded] at success
          rcases success with ⟨rfl, _⟩
          exact encodeIntegerText_of_decodeCanonicalIntegerTextAt_eq_ok path text value decoded

def encodeInteger (value : Int) : Lean.Json := encodeIntegerText value

def decodeIntegerAtWithBudget
    (limits : CoreBudgetLimits) (state : CoreBudgetState)
    (path : DecodePath) (json : Lean.Json) : CoreDecodeResult (Int × CoreBudgetState) := do
  let text ← liftProtocol <| decodeStringAt path json
  decodeIntegerTextAtWithBudget limits state path text

def decodeIntegerWithBudget (limits : CoreBudgetLimits) (json : Lean.Json) : CoreDecodeResult Int := do
  let (value, _) ← decodeIntegerAtWithBudget limits .initial .root json
  pure value

def decodeInteger (json : Lean.Json) : CoreDecodeResult Int :=
  decodeIntegerWithBudget .default json

def canonicalizeIntegerWithBudget
    (limits : CoreBudgetLimits) (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeInteger <$> decodeIntegerWithBudget limits json

theorem canonicalizeIntegerWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits) (json : Lean.Json) (value : Int)
    (success : decodeIntegerWithBudget limits json = .ok value) :
    canonicalizeIntegerWithBudget limits json = .ok (encodeInteger value) := by
  rw [canonicalizeIntegerWithBudget, success]
  rfl

def encodeWordText (value : Solcore.Core.Word) : String :=
  Solcore.ContractRuntime.encodeWordText value

def decodeWordTextAt
    (path : DecodePath)
    (text : String) :
    DecodeResult Solcore.Core.Word :=
  match Solcore.ContractRuntime.decodeWordText? text with
  | some value => pure value
  | none =>
      let reason :=
        if !(text.startsWith "0x") then "prefix"
        else if text.toList.length != 66 then "length"
        else "lowercase-hex"
      failAt path .invalidWord (.mkObj [("reason", reason)])

def decodeWordText (text : String) : DecodeResult Solcore.Core.Word :=
  decodeWordTextAt .root text

@[simp] theorem decodeWordTextAt_encodeWordText
    (path : DecodePath)
    (value : Solcore.Core.Word) :
    decodeWordTextAt path (encodeWordText value) = .ok value := by
  unfold decodeWordTextAt encodeWordText
  rw [Solcore.ContractRuntime.decodeWordText?_encodeWordText]
  rfl

@[simp] theorem decodeWordText_encodeWordText
    (value : Solcore.Core.Word) :
    decodeWordText (encodeWordText value) = .ok value :=
  decodeWordTextAt_encodeWordText .root value

/-- Every accepted spelling is already the unique canonical spelling. -/
theorem encodeWordText_of_decodeWordTextAt_eq_ok
    (path : DecodePath)
    (text : String)
    (value : Solcore.Core.Word)
    (success : decodeWordTextAt path text = .ok value) :
    encodeWordText value = text := by
  simp only [decodeWordTextAt] at success
  cases decoded : Solcore.ContractRuntime.decodeWordText? text with
  | none =>
      rw [decoded] at success
      contradiction
  | some decodedValue =>
      rw [decoded] at success
      change Except.ok decodedValue = Except.ok value at success
      injection success with equality
      subst value
      exact Solcore.ContractRuntime.encodeWordText_of_decodeWordText?_eq_some
        text decodedValue decoded

def encodeWord (value : Solcore.Core.Word) : Lean.Json :=
  encodeWordText value

def decodeWordAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult Solcore.Core.Word := do
  decodeWordTextAt path (← decodeStringAt path json)

def decodeWord (json : Lean.Json) : DecodeResult Solcore.Core.Word :=
  decodeWordAt .root json

@[simp] theorem decodeWordAt_encodeWord
    (path : DecodePath)
    (value : Solcore.Core.Word) :
    decodeWordAt path (encodeWord value) = .ok value := by
  simp [decodeWordAt, encodeWord, decodeStringAt]

@[simp] theorem decodeWord_encodeWord (value : Solcore.Core.Word) :
    decodeWord (encodeWord value) = .ok value :=
  decodeWordAt_encodeWord .root value

def encodeDataTypeId (id : DataTypeId) : Lean.Json :=
  id.index

def decodeDataTypeIdAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult DataTypeId :=
  return ⟨← decodeNatAt path json⟩

def decodeDataTypeId (json : Lean.Json) : DecodeResult DataTypeId :=
  decodeDataTypeIdAt .root json

@[simp] theorem decodeDataTypeIdAt_encodeDataTypeId
    (path : DecodePath)
    (id : DataTypeId) :
    decodeDataTypeIdAt path (encodeDataTypeId id) = .ok id := by
  cases id with
  | mk index =>
      have decoded : decodeNatAt path (Lean.toJson index) = .ok index := by
        unfold decodeNatAt
        rw [Util.jsonNatural_toJson]
        rfl
      change (do
        let value ← decodeNatAt path (Lean.toJson index)
        pure (DataTypeId.mk value)) = .ok (DataTypeId.mk index)
      rw [decoded]
      rfl

@[simp] theorem decodeDataTypeId_encodeDataTypeId (id : DataTypeId) :
    decodeDataTypeId (encodeDataTypeId id) = .ok id :=
  decodeDataTypeIdAt_encodeDataTypeId .root id

def encodeConstructorId (id : ConstructorId) : Lean.Json :=
  .mkObj [
    ("owner", encodeDataTypeId id.owner),
    ("index", id.index)
  ]

def decodeConstructorIdAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult ConstructorId := do
  ensureExactObject path json ["index", "owner"] ["index", "owner"]
  let index ← decodeNatAt (path.field "index")
    (← requireField path json "index")
  let owner ← decodeDataTypeIdAt (path.field "owner")
    (← requireField path json "owner")
  pure { owner, index }

def decodeConstructorId (json : Lean.Json) : DecodeResult ConstructorId :=
  decodeConstructorIdAt .root json

@[simp] theorem decodeConstructorIdAt_encodeConstructorId
    (path : DecodePath)
    (id : ConstructorId) :
    decodeConstructorIdAt path (encodeConstructorId id) = .ok id := by
  cases id with
  | mk owner index =>
      have decoded :
          decodeNatAt (path.field "index") (Lean.toJson index) = .ok index := by
        unfold decodeNatAt
        rw [Util.jsonNatural_toJson]
        rfl
      change (do
        let decodedIndex ← decodeNatAt (path.field "index") (Lean.toJson index)
        let decodedOwner ←
          decodeDataTypeIdAt (path.field "owner") (encodeDataTypeId owner)
        pure (ConstructorId.mk decodedOwner decodedIndex)) =
          .ok (ConstructorId.mk owner index)
      rw [decoded, decodeDataTypeIdAt_encodeDataTypeId]
      rfl

@[simp] theorem decodeConstructorId_encodeConstructorId
    (id : ConstructorId) :
    decodeConstructorId (encodeConstructorId id) = .ok id :=
  decodeConstructorIdAt_encodeConstructorId .root id

def canonicalizeWord (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeWord json).map encodeWord

def canonicalizeDataTypeId (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeDataTypeId json).map encodeDataTypeId

def canonicalizeConstructorId (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeConstructorId json).map encodeConstructorId

@[simp] theorem canonicalizeWord_encodeWord (value : Solcore.Core.Word) :
    canonicalizeWord (encodeWord value) = .ok (encodeWord value) := by
  rw [canonicalizeWord, decodeWord_encodeWord]
  rfl

@[simp] theorem canonicalizeDataTypeId_encodeDataTypeId (id : DataTypeId) :
    canonicalizeDataTypeId (encodeDataTypeId id) = .ok (encodeDataTypeId id) := by
  rw [canonicalizeDataTypeId, decodeDataTypeId_encodeDataTypeId]
  rfl

@[simp] theorem canonicalizeConstructorId_encodeConstructorId
    (id : ConstructorId) :
    canonicalizeConstructorId (encodeConstructorId id) =
      .ok (encodeConstructorId id) := by
  rw [canonicalizeConstructorId, decodeConstructorId_encodeConstructorId]
  rfl

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.Operator
/-! Canonical operator-name codecs for Semantic Core Wire. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeUnaryOp : UnaryOp → Lean.Json
  | .boolNot => "boolNot"
  | .wordNot => "wordNot"
  | .wordClz => "wordClz"
  | .integerNot => "integerNot"
  | .integerToWord => "integerToWord"
  | .wordToInteger => "wordToInteger"

def decodeUnaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult UnaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "boolNot" => pure .boolNot
  | "wordNot" => pure .wordNot
  | "wordClz" => pure .wordClz
  | "integerNot" => pure .integerNot
  | "integerToWord" => pure .integerToWord
  | "wordToInteger" => pure .wordToInteger
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("expected", .arr #["boolNot", "wordNot", "wordClz",
          "integerNot", "integerToWord", "wordToInteger"])
      ])

def decodeUnaryOp (json : Lean.Json) : DecodeResult UnaryOp :=
  decodeUnaryOpAt .root json

@[simp] theorem decodeUnaryOpAt_encodeUnaryOp
    (path : DecodePath)
    (op : UnaryOp) :
    decodeUnaryOpAt path (encodeUnaryOp op) = .ok op := by
  cases op <;> rfl

@[simp] theorem decodeUnaryOp_encodeUnaryOp (op : UnaryOp) :
    decodeUnaryOp (encodeUnaryOp op) = .ok op :=
  decodeUnaryOpAt_encodeUnaryOp .root op

def encodeBinaryOp : BinaryOp → Lean.Json
  | .wordAdd => "wordAdd"
  | .wordSub => "wordSub"
  | .wordMul => "wordMul"
  | .wordDiv => "wordDiv"
  | .wordMod => "wordMod"
  | .wordEq => "wordEq"
  | .wordGt => "wordGt"
  | .wordSgt => "wordSgt"
  | .wordAnd => "wordAnd"
  | .wordOr => "wordOr"
  | .wordXor => "wordXor"
  | .wordShl => "wordShl"
  | .wordShr => "wordShr"
  | .wordByte => "wordByte"
  | .wordSar => "wordSar"
  | .wordPow => "wordPow"
  | .wordSignExtend => "wordSignExtend"
  | .wordSdiv => "wordSdiv"
  | .wordSmod => "wordSmod"
  | .integerAdd => "integerAdd"
  | .integerSub => "integerSub"
  | .integerMul => "integerMul"
  | .integerDiv => "integerDiv"
  | .integerMod => "integerMod"
  | .integerEq => "integerEq"
  | .integerLt => "integerLt"
  | .integerAnd => "integerAnd"
  | .integerOr => "integerOr"
  | .integerXor => "integerXor"

def decodeBinaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult BinaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "wordAdd" => pure .wordAdd
  | "wordSub" => pure .wordSub
  | "wordMul" => pure .wordMul
  | "wordDiv" => pure .wordDiv
  | "wordMod" => pure .wordMod
  | "wordEq" => pure .wordEq
  | "wordGt" => pure .wordGt
  | "wordSgt" => pure .wordSgt
  | "wordAnd" => pure .wordAnd
  | "wordOr" => pure .wordOr
  | "wordXor" => pure .wordXor
  | "wordShl" => pure .wordShl
  | "wordShr" => pure .wordShr
  | "wordByte" => pure .wordByte
  | "wordSar" => pure .wordSar
  | "wordPow" => pure .wordPow
  | "wordSignExtend" => pure .wordSignExtend
  | "wordSdiv" => pure .wordSdiv
  | "wordSmod" => pure .wordSmod
  | "integerAdd" => pure .integerAdd
  | "integerSub" => pure .integerSub
  | "integerMul" => pure .integerMul
  | "integerDiv" => pure .integerDiv
  | "integerMod" => pure .integerMod
  | "integerEq" => pure .integerEq
  | "integerLt" => pure .integerLt
  | "integerAnd" => pure .integerAnd
  | "integerOr" => pure .integerOr
  | "integerXor" => pure .integerXor
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("expected", .arr #[
          "wordAdd", "wordSub", "wordMul", "wordDiv", "wordMod",
          "wordEq", "wordGt", "wordSgt", "wordAnd", "wordOr", "wordXor",
          "wordShl", "wordShr", "wordByte", "wordSar", "wordPow",
          "wordSignExtend", "wordSdiv", "wordSmod",
          "integerAdd", "integerSub", "integerMul", "integerDiv", "integerMod",
          "integerEq", "integerLt", "integerAnd", "integerOr", "integerXor"
        ])
      ])

def decodeBinaryOp (json : Lean.Json) : DecodeResult BinaryOp :=
  decodeBinaryOpAt .root json

@[simp] theorem decodeBinaryOpAt_encodeBinaryOp
    (path : DecodePath)
    (op : BinaryOp) :
    decodeBinaryOpAt path (encodeBinaryOp op) = .ok op := by
  cases op <;> rfl

@[simp] theorem decodeBinaryOp_encodeBinaryOp (op : BinaryOp) :
    decodeBinaryOp (encodeBinaryOp op) = .ok op :=
  decodeBinaryOpAt_encodeBinaryOp .root op

def encodeTernaryOp : TernaryOp → Lean.Json
  | .wordAddMod => "wordAddMod"
  | .wordMulMod => "wordMulMod"

def decodeTernaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult TernaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "wordAddMod" => pure .wordAddMod
  | "wordMulMod" => pure .wordMulMod
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("expected", .arr #["wordAddMod", "wordMulMod"])
      ])

def decodeTernaryOp (json : Lean.Json) : DecodeResult TernaryOp :=
  decodeTernaryOpAt .root json

@[simp] theorem decodeTernaryOpAt_encodeTernaryOp
    (path : DecodePath)
    (op : TernaryOp) :
    decodeTernaryOpAt path (encodeTernaryOp op) = .ok op := by
  cases op <;> rfl

@[simp] theorem decodeTernaryOp_encodeTernaryOp (op : TernaryOp) :
    decodeTernaryOp (encodeTernaryOp op) = .ok op :=
  decodeTernaryOpAt_encodeTernaryOp .root op

def canonicalizeUnaryOp (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeUnaryOp json).map encodeUnaryOp

def canonicalizeBinaryOp (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeBinaryOp json).map encodeBinaryOp

def canonicalizeTernaryOp (json : Lean.Json) : DecodeResult Lean.Json :=
  (decodeTernaryOp json).map encodeTernaryOp

@[simp] theorem canonicalizeUnaryOp_encodeUnaryOp (op : UnaryOp) :
    canonicalizeUnaryOp (encodeUnaryOp op) = .ok (encodeUnaryOp op) := by
  rw [canonicalizeUnaryOp, decodeUnaryOp_encodeUnaryOp]
  rfl

@[simp] theorem canonicalizeBinaryOp_encodeBinaryOp (op : BinaryOp) :
    canonicalizeBinaryOp (encodeBinaryOp op) = .ok (encodeBinaryOp op) := by
  rw [canonicalizeBinaryOp, decodeBinaryOp_encodeBinaryOp]
  rfl

@[simp] theorem canonicalizeTernaryOp_encodeTernaryOp (op : TernaryOp) :
    canonicalizeTernaryOp (encodeTernaryOp op) = .ok (encodeTernaryOp op) := by
  rw [canonicalizeTernaryOp, decodeTernaryOp_encodeTernaryOp]
  rfl

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.Type
/-! Strict, budgeted type codecs for Semantic Core Wire. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeType : Ty → Lean.Json
  | .unit => "unit"
  | .bool => "bool"
  | .word => "word"
  | .integer => "integer"
  | .product left right =>
      .mkObj [
        ("tag", "product"),
        ("left", encodeType left),
        ("right", encodeType right)
      ]
  | .function parameter result =>
      .mkObj [
        ("tag", "function"),
        ("parameter", encodeType parameter),
        ("result", encodeType result)
      ]
  | .sum left right =>
      .mkObj [
        ("tag", "sum"),
        ("left", encodeType left),
        ("right", encodeType right)
      ]
  | .cell elementType =>
      .mkObj [
        ("tag", "cell"),
        ("elementType", encodeType elementType)
      ]
  | .namedData dataType =>
      .mkObj [
        ("tag", "namedData"),
        ("dataType", encodeDataTypeId dataType)
      ]
termination_by type => sizeOf type

def typeDepth : Ty → Nat
  | .unit | .bool | .word | .integer | .namedData _ => 1
  | .product left right | .function left right | .sum left right =>
      Nat.max (typeDepth left) (typeDepth right) + 1
  | .cell elementType => typeDepth elementType + 1

def typeNodes : Ty → Nat
  | .unit | .bool | .word | .integer | .namedData _ => 1
  | .product left right | .function left right | .sum left right =>
      1 + typeNodes left + typeNodes right
  | .cell elementType => 1 + typeNodes elementType

private def decodeTypeAtFuel :
    (fuel : Nat) → (limits : CoreBudgetLimits) → CoreBudgetState → (depth : Nat) →
      fuel = limits.maxDepth + 1 - depth →
      DecodePath → Lean.Json → CoreDecodeResult (Ty × CoreBudgetState)
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
      have childFuel : fuel = limits.maxDepth + 1 - (depth + 1) := by
        omega
      let state ← consumeCoreNode limits state depth
      match json with
      | .str name =>
          match name with
          | "unit" => pure (.unit, state)
          | "bool" => pure (.bool, state)
          | "word" => pure (.word, state)
          | "integer" => pure (.integer, state)
          | _ => throw (.protocol {
              path
              code := .invalidType
              arguments := .mkObj [
                ("actual", name),
                ("allowed", .arr #["unit", "bool", "word", "integer"])
              ]
            })
      | .obj _ => do
          liftProtocol <| ensureExactObject path json
            ["tag", "left", "right", "parameter", "result", "elementType",
              "dataType"] ["tag"]
          let tagPath := path.field "tag"
          let tag ← liftProtocol <| decodeStringAt tagPath
            (← liftProtocol <| requireField path json "tag")
          match tag with
          | "product" | "sum" =>
              liftProtocol <| ensureExactObject path json ["left", "right", "tag"]
                ["left", "right", "tag"]
              let (left, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "left")
                (← liftProtocol <| requireField path json "left")
              let (right, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "right")
                (← liftProtocol <| requireField path json "right")
              if tag == "product" then pure (.product left right, state)
              else pure (.sum left right, state)
          | "function" =>
              liftProtocol <| ensureExactObject path json
                ["parameter", "result", "tag"] ["parameter", "result", "tag"]
              let (parameter, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "parameter")
                (← liftProtocol <| requireField path json "parameter")
              let (result, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "result")
                (← liftProtocol <| requireField path json "result")
              pure (.function parameter result, state)
          | "cell" =>
              liftProtocol <| ensureExactObject path json ["elementType", "tag"]
                ["elementType", "tag"]
              let (elementType, state) ← decodeTypeAtFuel fuel limits state (depth + 1) childFuel
                (path.field "elementType")
                (← liftProtocol <| requireField path json "elementType")
              pure (.cell elementType, state)
          | "namedData" =>
              liftProtocol <| ensureExactObject path json ["dataType", "tag"]
                ["dataType", "tag"]
              let dataType ← liftProtocol <| decodeDataTypeIdAt (path.field "dataType")
                (← liftProtocol <| requireField path json "dataType")
              pure (.namedData dataType, state)
          | _ => throw (.protocol {
              path := tagPath
              code := .invalidTag
              arguments := .mkObj [
                ("actual", tag),
                ("expected", .arr #[
                  "product", "function", "sum", "cell", "namedData"
                ])
              ]
            })
      | _ => throw (.protocol {
          path
          code := .invalidType
          arguments := .mkObj [
            ("actual", match json with
              | .null => "null" | .bool _ => "boolean" | .num _ => "number"
              | .str _ => "string" | .arr _ => "array" | .obj _ => "object"),
            ("allowed", .arr #["string", "object"])
          ]
        })

def decodeTypeAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (Ty × CoreBudgetState) :=
  decodeTypeAtFuel (limits.maxDepth + 1 - depth) limits state depth rfl path json

def decodeTypeWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Ty := do
  let (type, _) ← decodeTypeAtWithBudget limits .initial 1 .root json
  pure type

def decodeType (json : Lean.Json) : CoreDecodeResult Ty :=
  decodeTypeWithBudget .default json

def canonicalizeTypeWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeType <$> decodeTypeWithBudget limits json

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.TypeProperties
/-! Canonicalization laws which do not conflate budgets with protocol errors. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

theorem canonicalizeTypeWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits)
    (json : Lean.Json)
    (type : Ty)
    (success : decodeTypeWithBudget limits json = .ok type) :
    canonicalizeTypeWithBudget limits json = .ok (encodeType type) := by
  rw [canonicalizeTypeWithBudget, success]
  rfl

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.DataDefinition
/-! Data-definition codecs with shared Core-node accounting. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeTypeList (types : List Ty) : Lean.Json :=
  .arr (types.map encodeType).toArray

private def decodeTypeJsonListAtWithBudget
    (limits : CoreBudgetLimits)
    (depth : Nat)
    (path : DecodePath) :
    Nat → CoreBudgetState → List Lean.Json →
      CoreDecodeResult (List Ty × CoreBudgetState)
  | _, state, [] => pure ([], state)
  | index, state, json :: rest => do
      let (type, state) ← decodeTypeAtWithBudget limits state depth
        (path.index index) json
      let (types, state) ← decodeTypeJsonListAtWithBudget limits depth path
        (index + 1) state rest
      pure (type :: types, state)

def decodeTypeListAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (List Ty × CoreBudgetState) := do
  let values ← liftProtocol <|
    match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (.mkObj [
        ("expected", "array"),
        ("actual", match json with
          | .null => "null" | .bool _ => "boolean" | .num _ => "number"
          | .str _ => "string" | .arr _ => "array" | .obj _ => "object")
      ])
  decodeTypeJsonListAtWithBudget limits depth path 0 state values

def encodeDataDefinition (definition : DataDefinition) : Lean.Json :=
  .mkObj [
    ("constructorPayloadTypes",
      encodeTypeList definition.constructorPayloadTypes)
  ]

def decodeDataDefinitionAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (DataDefinition × CoreBudgetState) := do
  let state ← consumeCoreNode limits state depth
  liftProtocol <| ensureExactObject path json ["constructorPayloadTypes"]
    ["constructorPayloadTypes"]
  let (payloadTypes, state) ← decodeTypeListAtWithBudget limits state (depth + 1)
    (path.field "constructorPayloadTypes")
    (← liftProtocol <| requireField path json "constructorPayloadTypes")
  pure ({ constructorPayloadTypes := payloadTypes }, state)

def decodeDataDefinitionWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult DataDefinition := do
  let (definition, _) ←
    decodeDataDefinitionAtWithBudget limits .initial 1 .root json
  pure definition

def encodeDataDefinitions (definitions : DataEnvironment) : Lean.Json :=
  .arr (definitions.map encodeDataDefinition).toArray

private def decodeDefinitionJsonListAtWithBudget
    (limits : CoreBudgetLimits)
    (depth : Nat)
    (path : DecodePath) :
    Nat → CoreBudgetState → List Lean.Json →
      CoreDecodeResult (DataEnvironment × CoreBudgetState)
  | _, state, [] => pure ([], state)
  | index, state, json :: rest => do
      let (definition, state) ← decodeDataDefinitionAtWithBudget limits state depth
        (path.index index) json
      let (definitions, state) ← decodeDefinitionJsonListAtWithBudget
        limits depth path (index + 1) state rest
      pure (definition :: definitions, state)

def decodeDataDefinitionsAtWithBudget
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (path : DecodePath)
    (json : Lean.Json) :
    CoreDecodeResult (DataEnvironment × CoreBudgetState) := do
  let values ← liftProtocol <|
    match json with
    | .arr values => pure values.toList
    | _ => failAt path .expectedArray (.mkObj [
        ("expected", "array"),
        ("actual", match json with
          | .null => "null" | .bool _ => "boolean" | .num _ => "number"
          | .str _ => "string" | .arr _ => "array" | .obj _ => "object")
      ])
  decodeDefinitionJsonListAtWithBudget limits depth path 0 state values

def typeListDepth : List Ty → Nat
  | [] => 0
  | type :: rest => Nat.max (typeDepth type) (typeListDepth rest)

def typeListNodes : List Ty → Nat
  | [] => 0
  | type :: rest => typeNodes type + typeListNodes rest

def dataDefinitionDepth (definition : DataDefinition) : Nat :=
  Nat.max 1 (typeListDepth definition.constructorPayloadTypes + 1)

def dataDefinitionNodes (definition : DataDefinition) : Nat :=
  1 + typeListNodes definition.constructorPayloadTypes

def dataEnvironmentDepth : DataEnvironment → Nat
  | [] => 0
  | definition :: rest =>
      Nat.max (dataDefinitionDepth definition) (dataEnvironmentDepth rest)

def dataEnvironmentNodes : DataEnvironment → Nat
  | [] => 0
  | definition :: rest =>
      dataDefinitionNodes definition + dataEnvironmentNodes rest

def canonicalizeDataDefinitionWithBudget
    (limits : CoreBudgetLimits)
    (json : Lean.Json) : CoreDecodeResult Lean.Json :=
  encodeDataDefinition <$> decodeDataDefinitionWithBudget limits json

theorem canonicalizeDataDefinitionWithBudget_of_decode_eq_ok
    (limits : CoreBudgetLimits)
    (json : Lean.Json)
    (definition : DataDefinition)
    (success : decodeDataDefinitionWithBudget limits json = .ok definition) :
    canonicalizeDataDefinitionWithBudget limits json =
      .ok (encodeDataDefinition definition) := by
  rw [canonicalizeDataDefinitionWithBudget, success]
  rfl

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.ExprEncoding
/-! Canonical JSON encoding for every Wire expression. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeExpr : Expr → Lean.Json
  | .unit => .mkObj [("tag", "unit")]
  | .bool value => .mkObj [("tag", "bool"), ("value", value)]
  | .word value =>
      .mkObj [("tag", "word"), ("value", encodeWord value)]
  | .integer value =>
      .mkObj [("tag", "integer"), ("value", encodeInteger value)]
  | .var index => .mkObj [("tag", "var"), ("index", index)]
  | .pair left right =>
      .mkObj [
        ("tag", "pair"),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
      ]
  | .first operand =>
      .mkObj [("tag", "first"), ("operand", encodeExpr operand)]
  | .second operand =>
      .mkObj [("tag", "second"), ("operand", encodeExpr operand)]
  | .lambda parameterType resultType body =>
      .mkObj [
        ("tag", "lambda"),
        ("parameterType", encodeType parameterType),
        ("resultType", encodeType resultType),
        ("body", encodeExpr body)
      ]
  | .apply function argument =>
      .mkObj [
        ("tag", "apply"),
        ("function", encodeExpr function),
        ("argument", encodeExpr argument)
      ]
  | .inLeft rightType payload =>
      .mkObj [
        ("tag", "inLeft"),
        ("rightType", encodeType rightType),
        ("payload", encodeExpr payload)
      ]
  | .inRight leftType payload =>
      .mkObj [
        ("tag", "inRight"),
        ("leftType", encodeType leftType),
        ("payload", encodeExpr payload)
      ]
  | .caseE scrutinee leftBranch rightBranch =>
      .mkObj [
        ("tag", "case"),
        ("scrutinee", encodeExpr scrutinee),
        ("leftBranch", encodeExpr leftBranch),
        ("rightBranch", encodeExpr rightBranch)
      ]
  | .newCell elementType initializer =>
      .mkObj [
        ("tag", "newCell"),
        ("elementType", encodeType elementType),
        ("initializer", encodeExpr initializer)
      ]
  | .loadCell reference =>
      .mkObj [("tag", "loadCell"), ("reference", encodeExpr reference)]
  | .storeCell reference value =>
      .mkObj [
        ("tag", "storeCell"),
        ("reference", encodeExpr reference),
        ("value", encodeExpr value)
      ]
  | .construct constructor payload =>
      .mkObj [
        ("tag", "construct"),
        ("constructor", encodeConstructorId constructor),
        ("payload", encodeExpr payload)
      ]
  | .matchData dataType resultType scrutinee branches =>
      .mkObj [
        ("tag", "matchData"),
        ("dataType", encodeDataTypeId dataType),
        ("resultType", encodeType resultType),
        ("scrutinee", encodeExpr scrutinee),
        ("branches", .arr (branches.map encodeExpr).toArray)
      ]
  | .unary op operand =>
      .mkObj [
        ("tag", "unary"),
        ("op", encodeUnaryOp op),
        ("operand", encodeExpr operand)
      ]
  | .binary op left right =>
      .mkObj [
        ("tag", "binary"),
        ("op", encodeBinaryOp op),
        ("left", encodeExpr left),
        ("right", encodeExpr right)
      ]
  | .ternary op first second third =>
      .mkObj [
        ("tag", "ternary"),
        ("op", encodeTernaryOp op),
        ("first", encodeExpr first),
        ("second", encodeExpr second),
        ("third", encodeExpr third)
      ]
  | .letE initializer body =>
      .mkObj [
        ("tag", "let"),
        ("initializer", encodeExpr initializer),
        ("body", encodeExpr body)
      ]
  | .ifE condition thenBranch elseBranch =>
      .mkObj [
        ("tag", "if"),
        ("condition", encodeExpr condition),
        ("thenBranch", encodeExpr thenBranch),
        ("elseBranch", encodeExpr elseBranch)
      ]
termination_by expression => sizeOf expression

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.ExprMeasure
/-! Exact typed-node demand for Wire expressions. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

private def max3 (first second third : Nat) : Nat :=
  Nat.max first (Nat.max second third)

mutual

  def exprDepth : Expr → Nat
    | .unit | .bool _ | .word _ | .integer _ | .var _ => 1
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        Nat.max (exprDepth left) (exprDepth right) + 1
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand =>
        exprDepth operand + 1
    | .lambda parameterType resultType body =>
        max3 (typeDepth parameterType) (typeDepth resultType) (exprDepth body) + 1
    | .inLeft rightType payload | .inRight rightType payload |
        .newCell rightType payload =>
        Nat.max (typeDepth rightType) (exprDepth payload) + 1
    | .caseE scrutinee leftBranch rightBranch =>
        max3 (exprDepth scrutinee) (exprDepth leftBranch)
          (exprDepth rightBranch) + 1
    | .matchData _ resultType scrutinee branches =>
        max3 (typeDepth resultType) (exprDepth scrutinee)
          (exprListDepth branches) + 1
    | .ternary _ first second third | .ifE first second third =>
        max3 (exprDepth first) (exprDepth second) (exprDepth third) + 1
  termination_by expression => sizeOf expression

  def exprListDepth : List Expr → Nat
    | [] => 0
    | expression :: rest =>
        Nat.max (exprDepth expression) (exprListDepth rest)
  termination_by expressions => sizeOf expressions

end

mutual

  def exprNodes : Expr → Nat
    | .unit | .bool _ | .word _ | .integer _ | .var _ => 1
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        1 + exprNodes left + exprNodes right
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand =>
        1 + exprNodes operand
    | .lambda parameterType resultType body =>
        1 + typeNodes parameterType + typeNodes resultType + exprNodes body
    | .inLeft rightType payload | .inRight rightType payload |
        .newCell rightType payload =>
        1 + typeNodes rightType + exprNodes payload
    | .caseE scrutinee leftBranch rightBranch =>
        1 + exprNodes scrutinee + exprNodes leftBranch + exprNodes rightBranch
    | .matchData _ resultType scrutinee branches =>
        1 + typeNodes resultType + exprNodes scrutinee + exprListNodes branches
    | .ternary _ first second third | .ifE first second third =>
        1 + exprNodes first + exprNodes second + exprNodes third
  termination_by expression => sizeOf expression

  def exprListNodes : List Expr → Nat
    | [] => 0
    | expression :: rest => exprNodes expression + exprListNodes rest
  termination_by expressions => sizeOf expressions

end

mutual

  /-- Cumulative bytes charged to canonical integer literal spellings. -/
  def exprIntegerBytes : Expr → Nat
    | .integer value => (encodeIntegerText value).utf8ByteSize
    | .unit | .bool _ | .word _ | .var _ => 0
    | .pair left right | .apply left right | .storeCell left right |
        .binary _ left right | .letE left right =>
        exprIntegerBytes left + exprIntegerBytes right
    | .first operand | .second operand | .loadCell operand |
        .construct _ operand | .unary _ operand | .lambda _ _ operand |
        .inLeft _ operand | .inRight _ operand | .newCell _ operand =>
        exprIntegerBytes operand
    | .caseE first second third | .ternary _ first second third | .ifE first second third =>
        exprIntegerBytes first + exprIntegerBytes second + exprIntegerBytes third
    | .matchData _ _ scrutinee branches =>
        exprIntegerBytes scrutinee + exprListIntegerBytes branches
  termination_by expression => sizeOf expression

  def exprListIntegerBytes : List Expr → Nat
    | [] => 0
    | expression :: rest => exprIntegerBytes expression + exprListIntegerBytes rest
  termination_by expressions => sizeOf expressions

end

@[simp] theorem exprDepth_positive (expression : Expr) :
    0 < exprDepth expression := by
  cases expression <;> simp [exprDepth]

@[simp] theorem exprNodes_positive (expression : Expr) :
  0 < exprNodes expression := by
  cases expression <;> simp [exprNodes] <;> omega

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.ExprDecode
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
end

section
-- leanmerge: from Solcore.Core.Wire.Codec.Program
/-! Complete Program codec and cross-Program Core budget aggregation. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

def encodeProgram (program : Program) : Lean.Json :=
  .mkObj [
    ("schema", schemaName),
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

def programIntegerBytes (program : Program) : Nat := exprIntegerBytes program.body

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
  unless actualSchema == schemaName do
    throw (.protocol {
      path := schemaPath
      code := .invalidSchema
      arguments := .mkObj [
        ("expected", schemaName),
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

/-- Decode canonical package order with cumulative nodes/integers and fresh root depth. -/
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

def programListIntegerBytes : List Program → Nat
  | [] => 0
  | program :: rest => programIntegerBytes program + programListIntegerBytes rest

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

end Solcore.Core.Wire
end

section
-- leanmerge: from Solcore.Core.Wire.Codec
/-! Executable JSON codecs for the canonical Semantic Core wire boundary. -/
end
