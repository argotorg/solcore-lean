import Solcore.Synthesis.Core.Fragment

/-! The G0 operators and forms a swarm mask can disable. Literal and local
leaves are always available, so every mask still admits a program. -/

set_option autoImplicit false

namespace Solcore.Synthesis.Core

open Solcore.Core.Wire

/-- The enabled maskable features, in `FeatureMask.catalog` order. -/
structure FeatureMask where
  private mk ::
  enabled : List Feature
  deriving Repr, BEq, DecidableEq

namespace FeatureMask

/-- Every operator and non-leaf form of the G0 grammar, in a fixed bit order. -/
def catalog : List Feature :=
  [.unary .boolNot, .unary .wordNot, .unary .wordClz] ++
    ([.wordAdd, .wordSub, .wordMul, .wordDiv, .wordMod, .wordAnd, .wordOr, .wordXor,
      .wordShl, .wordShr, .wordByte, .wordSar, .wordPow, .wordSignExtend, .wordSdiv, .wordSmod,
      .wordEq, .wordGt, .wordSgt] : List BinaryOp).map .binary ++
    [.ternary .wordAddMod, .ternary .wordMulMod, .letE, .ifE]

/-- The unrestricted mask of revisions one and two. -/
def all : FeatureMask := ⟨catalog⟩

/-- Bit `i` enables `catalog[i]`; higher bits are ignored. -/
def ofBits (bits : Nat) : FeatureMask :=
  ⟨catalog.zipIdx.filterMap fun (feature, index) =>
    if bits / 2 ^ index % 2 = 1 then some feature else none⟩

/-- Canonical order: any subset of the catalog, in catalog order. -/
def ofFeatures? (features : List Feature) : Option FeatureMask :=
  if features.all catalog.contains && features.eraseDups.length = features.length then
    let enabled := catalog.filter features.contains
    if enabled = features then some ⟨enabled⟩ else none
  else none

def allows (mask : FeatureMask) (feature : Feature) : Bool :=
  mask.enabled.contains feature

/-- The catalog features an emitter renders, from its own operator predicates.
Every G0 emitter renders `let` and `if`. -/
def supporting (unary : UnaryOp → Bool) (binary : BinaryOp → Bool) (ternary : TernaryOp → Bool) :
    FeatureMask :=
  ⟨catalog.filter fun
    | .unary operation => unary operation
    | .binary operation => binary operation
    | .ternary operation => ternary operation
    | _ => true⟩

/-- A unary, binary or ternary operator, rather than a `let` or `if` form. -/
def isOperator : Feature → Bool
  | .unary _ | .binary _ | .ternary _ => true
  | _ => false

def hasOperator (mask : FeatureMask) : Bool :=
  mask.enabled.any isOperator

/-- Whether every feature `mask` enables is in `support`. -/
def subset (mask support : FeatureMask) : Bool :=
  mask.enabled.all support.allows

/-- `mask` restricted to `support`. When that removes every operator `mask`
enables, the result is `support` itself, so that a restriction never leaves only
leaves and forms; a mask that enables no operator restricts plainly. -/
def within (mask support : FeatureMask) : FeatureMask :=
  let kept : FeatureMask := ⟨mask.enabled.filter support.allows⟩
  if kept.hasOperator || !mask.hasOperator then kept else support

end FeatureMask

end Solcore.Synthesis.Core
