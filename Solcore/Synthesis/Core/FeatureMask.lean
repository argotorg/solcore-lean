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

end FeatureMask

end Solcore.Synthesis.Core
