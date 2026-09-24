import Solcore.Core.Wire.Codec.Foundation

/-! Typed Core-resource accounting, kept separate from protocol failures. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

inductive CoreBudgetResource where
  | depth
  | nodes
  deriving Repr, BEq, DecidableEq

structure CoreBudgetLimits where
  maxDepth : Nat
  maxNodes : Nat
  deriving Repr, BEq, DecidableEq

namespace CoreBudgetLimits

def default : CoreBudgetLimits := {
  maxDepth := 1024
  maxNodes := 1000000
}

end CoreBudgetLimits

structure CoreBudgetState where
  consumedNodes : Nat := 0
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
  pure { consumedNodes := consumed }

@[simp] theorem consumeCoreNode_at_limits
    (limits : CoreBudgetLimits)
    (state : CoreBudgetState)
    (depth : Nat)
    (depthFits : depth ≤ limits.maxDepth)
    (nodesFit : state.consumedNodes + 1 ≤ limits.maxNodes) :
    consumeCoreNode limits state depth =
      .ok { consumedNodes := state.consumedNodes + 1 } := by
  simp [consumeCoreNode, Nat.not_lt.mpr depthFits, Nat.not_lt.mpr nodesFit]
  rfl

end Solcore.Core.Wire
