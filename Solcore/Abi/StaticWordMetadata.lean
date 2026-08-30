import Solcore.Abi.Keccak256

/-! Validated metadata and selectors for the Static Word ABI profile. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

open Solcore.Semantics

/-- The only external value type admitted by the first ABI profile. -/
inductive SupportedType where
  | uint256
  deriving Repr, BEq, DecidableEq

def SupportedType.canonicalText : SupportedType → String
  | .uint256 => "uint256"

private def isAsciiLetter (character : Char) : Bool :=
  let code := character.toNat
  (65 ≤ code && code ≤ 90) || (97 ≤ code && code ≤ 122)

private def isAsciiDigit (character : Char) : Bool :=
  let code := character.toNat
  48 ≤ code && code ≤ 57

private def isMethodNameStart (character : Char) : Bool :=
  isAsciiLetter character || character == '_'

private def isMethodNameContinue (character : Char) : Bool :=
  isMethodNameStart character || isAsciiDigit character

/-- Decide the exact ASCII grammar `[A-Za-z_][A-Za-z0-9_]*`. -/
def isValidMethodName (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      isMethodNameStart first && rest.all isMethodNameContinue

/-- A method name carrying evidence that it satisfies the Static Word grammar. -/
structure MethodName where
  text : String
  valid : isValidMethodName text = true

/-- Validate an arbitrary string without normalization or partial failure. -/
def validateMethodName? (text : String) : Option MethodName :=
  if valid : isValidMethodName text = true then
    some ⟨text, valid⟩
  else
    none

/-- Syntax-independent metadata for one `uint256 -> uint256` method. -/
structure MethodMetadata where
  name : MethodName
  inputType : SupportedType
  outputType : SupportedType

def MethodMetadata.staticWord (name : MethodName) : MethodMetadata where
  name := name
  inputType := .uint256
  outputType := .uint256

/-- Canonical Ethereum signature spelling; return types are not included. -/
def MethodMetadata.canonicalSignatureText
    (metadata : MethodMetadata) : String :=
  metadata.name.text ++ "(" ++ metadata.inputType.canonicalText ++ ")"

def MethodMetadata.canonicalSignatureBytes
    (metadata : MethodMetadata) : Bytes :=
  metadata.canonicalSignatureText.toUTF8

/-- An ABI selector whose four-octet width is part of its type. -/
structure Selector where
  bytes : Vector UInt8 4
  deriving Repr, BEq, DecidableEq

def Selector.encode (selector : Selector) : Bytes :=
  ⟨selector.bytes.toArray⟩

/-- Decode only an exact four-byte sequence. -/
def Selector.decode? (bytes : Bytes) : Option Selector :=
  if width : bytes.size = 4 then
    some ⟨⟨bytes.data, width⟩⟩
  else
    none

@[simp] theorem Selector.encode_size (selector : Selector) :
    selector.encode.size = 4 := by
  change selector.bytes.toArray.size = 4
  exact selector.bytes.size_toArray

@[simp] theorem Selector.decode_encode (selector : Selector) :
    Selector.decode? selector.encode = some selector := by
  unfold Selector.decode?
  rw [dif_pos selector.encode_size]
  congr

def Selector.toUInt32 (selector : Selector) : UInt32 :=
  selector.bytes.toArray.foldl
    (fun value byte => (value <<< 8) ||| byte.toUInt32) 0

/-- Big-endian numeric view of the selector in the exact `2^32` range. -/
def Selector.toFin (selector : Selector) : Fin (2 ^ 32) :=
  Fin.cast (by decide) selector.toUInt32.toFin

/-- Derive the first four Keccak digest bytes from arbitrary signature bytes. -/
def selectorFromSignatureBytes (signature : Bytes) : Selector :=
  let digest := Keccak256.hash signature
  ⟨Vector.ofFn (fun index => digest.get! index.val)⟩

def MethodMetadata.selector (metadata : MethodMetadata) : Selector :=
  selectorFromSignatureBytes metadata.canonicalSignatureBytes

end Solcore.Abi.V1
