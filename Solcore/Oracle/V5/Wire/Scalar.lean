import Solcore.Oracle.V5.Schema
import Solcore.Oracle.V5.Wire.Foundation
import Solcore.Semantics.RuntimeScalars.TextProperties

/-! Canonical Oracle v5 scalar codecs. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.Semantics

private def scalarReason
    (text : String)
    (exactLength : Option Nat)
    (bytes : Bool := false) : String :=
  if !(text.startsWith "0x") then
    "prefix"
  else
    match exactLength with
    | some length =>
        if text.toList.length != length then "length" else "lowercase-hex"
    | none =>
        if bytes && (text.toList.length - 2) % 2 != 0 then
          "odd-length"
        else
          "lowercase-hex"

def encodeWord (value : Core.Word) : Lean.Json :=
  Solcore.Semantics.encodeWordText value

def decodeWordAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Core.Word := do
  let text ← decodeStringAt path json
  match Solcore.Semantics.decodeWordText? text with
  | some value => pure value
  | none => failAt path .invalidWord (.mkObj [
      ("reason", scalarReason text (some 66))
    ])

def encodeAddress (value : Address) : Lean.Json :=
  Solcore.Semantics.encodeAddressText value

def decodeAddressAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Address := do
  let text ← decodeStringAt path json
  match Solcore.Semantics.decodeAddressText? text with
  | some value => pure value
  | none => failAt path .invalidAddress (.mkObj [
      ("reason", scalarReason text (some 42))
    ])

def encodeBytes (value : Bytes) : Lean.Json :=
  Solcore.Semantics.encodeBytesText value

def decodeBytesAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Bytes := do
  let text ← decodeStringAt path json
  match Solcore.Semantics.decodeBytesText? text with
  | some value => pure value
  | none => failAt path .invalidBytes (.mkObj [
      ("reason", scalarReason text none true)
    ])

def encodeRequestId (id : RequestId) : Lean.Json :=
  id.value

def decodeRequestIdAt
    (path : Path)
    (json : Lean.Json) : DecodeResult RequestId := do
  let value ← decodeStringAt path json
  match RequestId.ofString? value with
  | some id => pure id
  | none => failAt path .invalidRequestId (.mkObj [
      ("constraint", "nonempty-utf8")
    ])

def encodeNullableString : Option String → Lean.Json
  | none => .null
  | some value => value

def decodeNullableStringAt
    (path : Path)
    (json : Lean.Json) : DecodeResult (Option String) :=
  match json with
  | .null => pure none
  | _ => some <$> decodeStringAt path json

@[simp] theorem decodeWordAt_encodeWord
    (path : Path)
    (value : Core.Word) :
    decodeWordAt path (encodeWord value) = .ok value := by
  simp [decodeWordAt, encodeWord, decodeStringAt,
    Solcore.Semantics.decodeWordText?_encodeWordText]
  rfl

@[simp] theorem decodeAddressAt_encodeAddress
    (path : Path)
    (value : Address) :
    decodeAddressAt path (encodeAddress value) = .ok value := by
  simp [decodeAddressAt, encodeAddress, decodeStringAt,
    Solcore.Semantics.decodeAddressText?_encodeAddressText]
  rfl

@[simp] theorem decodeBytesAt_encodeBytes
    (path : Path)
    (value : Bytes) :
    decodeBytesAt path (encodeBytes value) = .ok value := by
  simp [decodeBytesAt, encodeBytes, decodeStringAt,
    Solcore.Semantics.decodeBytesText?_encodeBytesText]
  rfl

@[simp] theorem decodeRequestIdAt_encodeRequestId
    (path : Path)
    (id : RequestId) :
    decodeRequestIdAt path (encodeRequestId id) = .ok id := by
  simp [decodeRequestIdAt, encodeRequestId, decodeStringAt]
  rfl

end Solcore.Oracle.V5.Wire
