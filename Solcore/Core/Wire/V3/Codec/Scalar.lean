import Solcore.Core.Wire.V3.Codec.Foundation
import Solcore.Core.Wire.V3.Syntax
import Solcore.Semantics.RuntimeScalars.TextProperties

/-! Canonical scalar and identity codecs for Semantic Core Wire v3. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeWordText (value : Solcore.Core.Word) : String :=
  Solcore.Semantics.encodeWordText value

def decodeWordTextAt
    (path : DecodePath)
    (text : String) :
    DecodeResult Solcore.Core.Word :=
  match Solcore.Semantics.decodeWordText? text with
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
  rw [Solcore.Semantics.decodeWordText?_encodeWordText]
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
  cases decoded : Solcore.Semantics.decodeWordText? text with
  | none =>
      rw [decoded] at success
      contradiction
  | some decodedValue =>
      rw [decoded] at success
      change Except.ok decodedValue = Except.ok value at success
      injection success with equality
      subst value
      exact Solcore.Semantics.encodeWordText_of_decodeWordText?_eq_some
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
        rw [Foundation.jsonNatural_toJson]
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
  ensureExactObject path json ["owner", "index"] ["owner", "index"]
  let owner ← decodeDataTypeIdAt (path.field "owner")
    (← requireField path json "owner")
  let index ← decodeNatAt (path.field "index")
    (← requireField path json "index")
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
        rw [Foundation.jsonNatural_toJson]
        rfl
      change (do
        let decodedOwner ←
          decodeDataTypeIdAt (path.field "owner") (encodeDataTypeId owner)
        let decodedIndex ← decodeNatAt (path.field "index") (Lean.toJson index)
        pure (ConstructorId.mk decodedOwner decodedIndex)) =
          .ok (ConstructorId.mk owner index)
      rw [decodeDataTypeIdAt_encodeDataTypeId, decoded]
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

end Solcore.Core.Wire.V3
