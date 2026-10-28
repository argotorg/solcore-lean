import Solcore.Synthesis.Core.GeneratorV2
import Solcore.Core.Wire.Codec.Program

/-! User-defined enum declarations, their closed instances and values, as
plans for the original Core reference. An enum is a right-nested Core sum of
its constructors' payloads, a payload is Unit, its one field or the product of
its two fields, and a generic declaration is substituted at each instance.
Nothing here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Enums

open Solcore.Core (Word)
open Solcore.Core.Wire

abbrev WireTy := Solcore.Core.Wire.Ty

/-- Field, argument and scrutinee types. `param` is a generic declaration's
parameter `a`; a closed type has none. -/
inductive Ty where
  | word
  | param
  | tuple (left right : Ty)
  | enum (index : Nat)
  | applied (index : Nat) (argument : Ty)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Ty

def closed : Ty → Bool
  | .word | .enum _ => true
  | .param => false
  | .tuple left right => left.closed && right.closed
  | .applied _ argument => argument.closed

/-- Substitute a declaration's parameter. -/
def subst (argument : Ty) : Ty → Ty
  | .word => .word
  | .param => argument
  | .tuple left right => .tuple (subst argument left) (subst argument right)
  | .enum index => .enum index
  | .applied index inner => .applied index (subst argument inner)

def nodes : Ty → Nat
  | .word | .param | .enum _ => 1
  | .tuple left right => 1 + left.nodes + right.nodes
  | .applied _ argument => 1 + argument.nodes

end Ty

/-- Two to four constructors of zero to two fields. With `sameName`,
constructor 0, which has a field, carries the enum's own name. -/
structure Decl where
  generic : Bool
  sameName : Bool
  constructors : List (List Ty)
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumDecls : Nat := 3
def maximumConstructors : Nat := 4
def maximumFields : Nat := 2

/-- The largest Core type of a closed type in a plan, in Wire type nodes. -/
def typeLimit : Nat := 64

/-- The constructors' field types of a type, substituted at its argument;
none for a Word, the parameter or an unknown declaration. A tuple is one
constructor of two fields. -/
def constructorsOf (decls : List Decl) : Ty → Option (List (List Ty))
  | .tuple left right => some [[left, right]]
  | .enum index => match decls[index]? with
      | some decl => if decl.generic then none else some decl.constructors
      | none => none
  | .applied index argument => match decls[index]? with
      | some decl => if decl.generic then some (decl.constructors.map (·.map (Ty.subst argument))) else none
      | none => none
  | .word | .param => none

/-- Declaration `index` may refer to the earlier declarations only, so a type
reaches at most `maximumDecls` declarations below its own nesting. -/
def validIn (decls : List Decl) (index : Nat) (generic : Bool) : Ty → Bool
  | .word => true
  | .param => generic
  | .tuple left right => validIn decls index generic left && validIn decls index generic right
  | .enum target => target < index && (match decls[target]? with
      | some decl => !decl.generic
      | none => false)
  | .applied target argument => target < index && (match decls[target]? with
      | some decl => decl.generic
      | none => false) && validIn decls index generic argument

/-- A use-site type: every declaration reference is valid, at any index. -/
def validUse (decls : List Decl) (generic : Bool) : Ty → Bool :=
  validIn decls decls.length generic

def sumChain : List WireTy → WireTy
  | [] => .unit
  | [last] => last
  | first :: rest => .sum first (sumChain rest)

/-- The Core type: right-nested sums of payloads. Fuel bounds the descent
through declarations; admitted plans never exhaust it. -/
def coreTy (decls : List Decl) : Nat → Ty → WireTy
  | 0, _ => .unit
  | _ + 1, .word => .word
  | _ + 1, .param => .unit
  | fuel + 1, .tuple left right => .product (coreTy decls fuel left) (coreTy decls fuel right)
  | fuel + 1, .enum index => match decls[index]? with
      | some decl => sumChain (decl.constructors.map fun fields => payloadTy fuel fields)
      | none => .unit
  | fuel + 1, .applied index argument => match decls[index]? with
      | some decl => sumChain (decl.constructors.map fun fields =>
          payloadTy fuel (fields.map (Ty.subst argument)))
      | none => .unit
where
  payloadTy (fuel : Nat) : List Ty → WireTy
    | [] => .unit
    | [field] => coreTy decls fuel field
    | [first, second] => .product (coreTy decls fuel first) (coreTy decls fuel second)
    | _ => .unit

/-- Fuel for `coreTy`: every declaration level adds at most two tuple levels
and one application. -/
def typeFuel : Nat := 4 * (maximumDecls + 2)

def wireTy (decls : List Decl) (type : Ty) : WireTy := coreTy decls typeFuel type

def wireTypeNodes (wire : WireTy) : Nat := typeNodes wire

/-- A leaf Word of a value, from the builder's input `x`. -/
inductive LeafOp where
  | input
  | add
  | xor
  | mul
  deriving Repr, BEq, DecidableEq, Inhabited

namespace LeafOp

def name : LeafOp → String
  | .input => "input"
  | .add => "add"
  | .xor => "xor"
  | .mul => "mul"

def ofString? : String → Option LeafOp
  | "input" => some .input
  | "add" => some .add
  | "xor" => some .xor
  | "mul" => some .mul
  | _ => none

end LeafOp

/-- How a constructor is written: `T.C`, `.C` (in a pattern, or a builder's
returned value) or unqualified `T` for a same-name constructor. -/
inductive Form where
  | qualified
  | dot
  | sameName
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def name : Form → String
  | .qualified => "qualified"
  | .dot => "dot"
  | .sameName => "same-name"

def ofString? : String → Option Form
  | "qualified" => some .qualified
  | "dot" => some .dot
  | "same-name" => some .sameName
  | _ => none

end Form

inductive Value where
  | leaf (op : LeafOp) (constant : Nat)
  | tuple (left right : Value)
  | ctor0 (index : Nat) (form : Form)
  | ctor1 (index : Nat) (field : Value) (form : Form)
  | ctor2 (index : Nat) (first second : Value) (form : Form)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Value

def nodes : Value → Nat
  | .leaf _ _ | .ctor0 _ _ => 1
  | .tuple left right | .ctor2 _ left right _ => 1 + left.nodes + right.nodes
  | .ctor1 _ field _ => 1 + field.nodes

def constructor? : Value → Option (Nat × List Value × Form)
  | .ctor0 index form => some (index, [], form)
  | .ctor1 index field form => some (index, [field], form)
  | .ctor2 index first second form => some (index, [first, second], form)
  | _ => none

end Value

/-- The form a constructor may take: `top` is a builder's returned value. -/
def formAdmitted (decls : List Decl) (type : Ty) (index : Nat) (top : Bool) : Form → Bool
  | .qualified => true
  | .dot => top
  | .sameName => index = 0 && (match type with
      | .enum target | .applied target _ => (decls[target]?.map (·.sameName)).getD false
      | _ => false)

/-- Values are typed structurally; leaves are canonical, with no constant
for the input itself. -/
def valueTyped (decls : List Decl) : Nat → Bool → Ty → Value → Bool
  | 0, _, _, _ => false
  | _ + 1, _, .word, .leaf op constant =>
      constant < 2 ^ 256 && (op != .input || constant = 0)
  | fuel + 1, _, .tuple left right, .tuple first second =>
      valueTyped decls fuel false left first && valueTyped decls fuel false right second
  | fuel + 1, top, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (index, fields, form) => match type with
          | .tuple _ _ => false
          | _ => match constructors[index]? with
              | some types => types.length = fields.length && formAdmitted decls type index top form &&
                  (types.zip fields).all fun (fieldType, field) => valueTyped decls fuel false fieldType field
              | none => false
      | _, _ => false

def valueFuel : Nat := 4 * typeFuel

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

def leafExpr (input : Nat) : LeafOp → Nat → Expr
  | .input, _ => .var input
  | .add, constant => .binary .wordAdd (.var input) (word constant)
  | .xor, constant => .binary .wordXor (.var input) (word constant)
  | .mul, constant => .binary .wordMul (.var input) (word constant)

/-- A payload's Core type: Unit, its one field, or the product of its two. -/
def payloadWire (decls : List Decl) : List Ty → WireTy
  | [] => .unit
  | [field] => wireTy decls field
  | [first, second] => .product (wireTy decls first) (wireTy decls second)
  | _ => .unit

def payloadWires (decls : List Decl) (constructors : List (List Ty)) : List WireTy :=
  constructors.map (payloadWire decls)

/-- Constructor `index` of the sum chain of these payload types. -/
def injectWire : List WireTy → Nat → Expr → Expr
  | [], _, payload => payload
  | [_], _, payload => payload
  | _ :: rest, 0, payload => .inLeft (sumChain rest) payload
  | first :: rest, index + 1, payload => .inRight first (injectWire rest index payload)

/-- The Core value at a closed type, with the builder's input at de Bruijn
index `input`. -/
def valueExpr (decls : List Decl) (input : Nat) : Nat → Ty → Value → Expr
  | 0, _, _ => .unit
  | _ + 1, .word, .leaf op constant => leafExpr input op constant
  | fuel + 1, .tuple left right, .tuple first second =>
      .pair (valueExpr decls input fuel left first) (valueExpr decls input fuel right second)
  | fuel + 1, type, value => match constructorsOf decls type, value.constructor? with
      | some constructors, some (index, fields, _) =>
          let types := constructors.getD index []
          let payload := match types, fields with
            | [type], [field] => valueExpr decls input fuel type field
            | [first, second], [left, right] =>
                .pair (valueExpr decls input fuel first left) (valueExpr decls input fuel second right)
            | _, _ => .unit
          injectWire (payloadWires decls constructors) index payload
      | _, _ => .unit

/-- The values a builder returns: residue `(x + offset) & 3` selects tree
`min residue (trees - 1)`. -/
structure Builder where
  offset : Nat
  trees : List Value
  deriving Repr, BEq, DecidableEq, Inhabited

def maximumTrees : Nat := 4

def Builder.admitted (decls : List Decl) (type : Ty) (builder : Builder) : Bool :=
  builder.offset < 4 && 0 < builder.trees.length && builder.trees.length ≤ maximumTrees &&
    builder.trees.all (valueTyped decls valueFuel true type)

private def residueTest (index : Nat) : Expr :=
  .binary .wordEq (.var 0) (word index)

/-- The builder as a Core closure from Words; with one tree, no residue. -/
def builderExpr (decls : List Decl) (type : Ty) (builder : Builder) : Expr :=
  match builder.trees with
  | [tree] => .lambda .word (wireTy decls type) (valueExpr decls 0 valueFuel type tree)
  | trees =>
      let selected := chain trees 0
      .lambda .word (wireTy decls type)
        (.letE (.binary .wordAnd (.binary .wordAdd (.var 0) (word builder.offset)) (word 3)) selected)
where
  chain : List Value → Nat → Expr
    | [], _ => .unit
    | [last], _ => valueExpr decls 1 valueFuel type last
    | tree :: rest, index =>
        .ifE (residueTest index) (valueExpr decls 1 valueFuel type tree) (chain rest (index + 1))

/-- The tree a builder returns for one input. -/
def Builder.selected (builder : Builder) (input : Word) : Option Value :=
  let residue := ((input.val + builder.offset) % 2 ^ 256) % 4
  builder.trees[min residue (builder.trees.length - 1)]?

/-! The SplitMix64 stream of a case seed, separated by a domain per profile. -/

private def gamma : UInt64 := 0x9e3779b97f4a7c15

structure Stream where
  seed : UInt64
  domain : UInt64
  index : Nat

abbrev Gen := StateM Stream

private def Stream.value (stream : Stream) : UInt64 :=
  GeneratorV2.mix ((stream.seed ^^^ stream.domain) + UInt64.ofNat (stream.index + 1) * gamma)

/-- The next value reduced to `[0, bound)` from its upper 32 bits; a zero
bound still consumes one value. -/
def draw (bound : Nat) : Gen Nat := modifyGet fun stream =>
  (if bound = 0 then 0 else (stream.value.toNat / 2 ^ 32) % bound, {stream with index := stream.index + 1})

/-- The next value as 64 bits. -/
def drawBits : Gen Nat := modifyGet fun stream =>
  (stream.value.toNat, {stream with index := stream.index + 1})

/-- Choose by integer weights; a zero total chooses 0. -/
def drawWeighted (weights : List Nat) : Gen Nat := do
  let total := weights.foldl (· + ·) 0
  let point ← draw total
  let mut remaining := point
  for (weight, index) in weights.zipIdx do
    if remaining < weight then return index
    remaining := remaining - weight
  return 0

/-- A Word constant: small, 64-bit, high-bit or near the maximum. -/
def drawConstant : Gen Nat := do
  match ← draw 4 with
  | 0 => return 1 + (← draw 255)
  | 1 => drawBits
  | 2 => return 2 ^ 255 + (← draw 256)
  | _ => return 2 ^ 256 - 1 - (← draw 256)

private def drawArgument (generic : Bool) : Gen Ty := do
  match ← drawWeighted [2, 1, if generic then 1 else 0] with
  | 0 => return .word
  | 1 => return .tuple .word .word
  | _ => return .param

private def drawReference (decls : List Decl) (index : Nat) (generic : Bool) : Gen Ty := do
  let target ← draw index
  match decls[target]? with
  | some decl => if decl.generic then return .applied target (← drawArgument generic) else return .enum target
  | none => return .word

private def drawComponent (decls : List Decl) (index : Nat) (generic : Bool) : Gen Ty := do
  match ← drawWeighted [2, if generic then 1 else 0, if index > 0 then 1 else 0] with
  | 0 => return .word
  | 1 => return .param
  | _ => drawReference decls index generic

/-- A field: a Word, the parameter, a tuple of two non-tuple components, or
an earlier declaration (at an argument when generic). -/
def drawField (decls : List Decl) (index : Nat) (generic : Bool) : Gen Ty := do
  match ← drawWeighted [3, if generic then 2 else 0, 1, if index > 0 then 2 else 0] with
  | 0 => return .word
  | 1 => return .param
  | 2 => return .tuple (← drawComponent decls index generic) (← drawComponent decls index generic)
  | _ => drawReference decls index generic

/-- The widest Core type of a declaration, its parameter at `(word, word)`. -/
def declNodes (decls : List Decl) (decl : Decl) : Nat :=
  let constructors := decl.constructors.map (·.map (Ty.subst (.tuple .word .word)))
  wireTypeNodes (sumChain (payloadWires decls constructors))

/-- A declaration whose widest Core type exceeds `typeLimit` keeps only Word
fields. -/
def drawDecl (decls : List Decl) (index : Nat) : Gen Decl := do
  let generic := (← draw 2) = 1
  let count := 2 + (← draw (maximumConstructors - 1))
  let mut constructors : List (List Ty) := []
  for _ in List.range count do
    let fields := ← draw (maximumFields + 1)
    let mut types : List Ty := []
    for _ in List.range fields do
      types := types ++ [← drawField decls index generic]
    constructors := constructors ++ [types]
  let sameName := (← draw 4) = 0 && (constructors.headD []).length > 0
  let decl : Decl := {generic, sameName, constructors}
  if declNodes decls decl ≤ typeLimit then return decl
  else return {decl with constructors := decl.constructors.map (·.map fun _ => .word)}

def drawDecls : Gen (List Decl) := do
  let count := 1 + (← draw maximumDecls)
  let mut decls : List Decl := []
  for index in List.range count do
    decls := decls ++ [← drawDecl decls index]
  return decls

/-- A random leaf. -/
def drawLeaf : Gen Value := do
  let op := match ← draw 4 with
    | 0 => LeafOp.input
    | 1 => .add
    | 2 => .xor
    | _ => .mul
  if op == .input then return .leaf op 0 else return .leaf op (← drawConstant)

/-- A random value of a closed type; `top` admits the dot form. -/
def drawValue (decls : List Decl) : Nat → Bool → Ty → Gen Value
  | 0, _, _ => return .leaf .input 0
  | _ + 1, _, .word => drawLeaf
  | fuel + 1, _, .tuple left right =>
      return .tuple (← drawValue decls fuel false left) (← drawValue decls fuel false right)
  | fuel + 1, top, type => do
      match constructorsOf decls type with
      | some constructors =>
          let index ← draw constructors.length
          let types := constructors.getD index []
          let sameName := formAdmitted decls type index top .sameName
          let form := match ← drawWeighted [3, if top then 1 else 0, if sameName then 2 else 0] with
            | 0 => Form.qualified
            | 1 => .dot
            | _ => .sameName
          match types with
          | [] => return .ctor0 index form
          | [field] => return .ctor1 index (← drawValue decls fuel false field) form
          | [first, second] =>
              return .ctor2 index (← drawValue decls fuel false first) (← drawValue decls fuel false second) form
          | _ => return .ctor0 index form
      | none => return .leaf .input 0

end Solcore.Synthesis.Core.Enums
