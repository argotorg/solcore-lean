import Solcore.Frontend.SourceCorePublicValues
import Solcore.Frontend.SourceRuntimeValues

/-! Data and uninitialized cells for an inert initial heap. Callable cells from
an existing execution use an authenticated snapshot export. Conversion is pure
and retains raw nominal metadata and ordered mapping entries. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreHeapInput

structure Cell where
  type : TypeSystem.Ty
  value : Option SourceCorePublicValues.Value
  deriving Repr

inductive PathElement where
  | cell (index : Nat)
  | left | right
  | payload (index : Nat)
  | key (index : Nat)
  | mapped (index : Nat)
  deriving Repr, DecidableEq

inductive ErrorCode where
  | conversionFuelExhausted
  | callableRequiresSnapshot
  | validationRejected (fuel : Nat)
  | emptyArtifactHeap (size : Nat)
  deriving Repr, DecidableEq

structure Error where
  path : List PathElement := []
  code : ErrorCode
  deriving Repr, DecidableEq

private def prependPath (element : PathElement) (error : Error) : Error :=
  {error with path := element :: error.path}

private def convertValue : Nat → SourceCorePublicValues.Value → Except Error SourceTypedRuntime.Value
  | 0, _ => .error ⟨[], .conversionFuelExhausted⟩
  | fuel + 1, value => do
      match value with
      | .unit => pure .unit
      | .bool value => pure (.bool value)
      | .word value => pure (.word value)
      | .integer value => pure (.integer value)
      | .proxy type => pure (.proxy type)
      | .product left right =>
          let left ← (convertValue fuel left).mapError (prependPath .left)
          let right ← (convertValue fuel right).mapError (prependPath .right)
          pure (.product left right)
      | .constructed instantiation payloads =>
          let payloads ← payloads.zipIdx.mapM fun (value, index) =>
            (convertValue fuel value).mapError (prependPath (.payload index))
          pure (.constructed instantiation payloads)
      | .mapping keyType valueType entries =>
          let entries ← entries.zipIdx.mapM fun ((key, value), index) => do
            let key ← (convertValue fuel key).mapError (prependPath (.key index))
            let value ← (convertValue fuel value).mapError (prependPath (.mapped index))
            pure (key, value)
          pure (.mapping keyType valueType entries)
      | .function _ => throw ⟨[], .callableRequiresSnapshot⟩

namespace Internal
/-- Used only by the validating prefix adapter. It adds no runtime behavior. -/
def convert (cells : List Cell) (fuel : Nat) : Except Error SourceTypedRuntime.RuntimeState := do
  let cells ← cells.zipIdx.mapM fun (cell, index) => do
    let value ← match cell.value with
      | none => pure none
      | some value => (convertValue fuel value).map some |>.mapError (prependPath (.cell index))
    pure (⟨cell.type, value⟩ : SourceTypedRuntime.Cell)
  pure ⟨cells⟩
end Internal
end Solcore.Frontend.SourceCoreHeapInput
