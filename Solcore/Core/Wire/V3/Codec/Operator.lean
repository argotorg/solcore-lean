import Solcore.Core.Wire.V3.Codec.Scalar

/-! Closed operator-name codecs for Semantic Core Wire v3. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

def encodeUnaryOp : UnaryOp → Lean.Json
  | .boolNot => "boolNot"
  | .wordNot => "wordNot"
  | .wordClz => "wordClz"

def decodeUnaryOpAt
    (path : DecodePath)
    (json : Lean.Json) :
    DecodeResult UnaryOp := do
  let name ← decodeStringAt path json
  match name with
  | "boolNot" => pure .boolNot
  | "wordNot" => pure .wordNot
  | "wordClz" => pure .wordClz
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("expected", .arr #["boolNot", "wordNot", "wordClz"])
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
  | _ =>
      failAt path .invalidTag (.mkObj [
        ("actual", name),
        ("expected", .arr #[
          "wordAdd", "wordSub", "wordMul", "wordDiv", "wordMod",
          "wordEq", "wordGt", "wordSgt", "wordAnd", "wordOr", "wordXor",
          "wordShl", "wordShr", "wordByte", "wordSar", "wordPow",
          "wordSignExtend", "wordSdiv", "wordSmod"
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

end Solcore.Core.Wire.V3
