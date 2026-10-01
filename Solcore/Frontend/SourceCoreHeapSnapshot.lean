import Solcore.Frontend.SourceCorePublicValues
import Solcore.Frontend.SourceCoreCallableIndexedPrincipalAllocations
import Solcore.Frontend.SourceRuntimeDeepValidation

/-! Read-only source heap observations. Raw source callables remain private;
the public view exposes their signature, evidence and source capture indices,
but provides no source body, native reference, or registration operation.

Principal observations use the owning allocation/header restoration receipt.
In particular, an unused generic initializer may have a native Unit payload
and an open raw source type. It is never presented as a closed callable handle.
The Legacy namespace is the explicit migration boundary for checked inert
prefixes. None of these observation capabilities can be invoked. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreHeapSnapshot
open SourceInference TypeSystem

structure ObservedValue where private mk ::
  private source : SourceTypedRuntime.Value

instance : Repr ObservedValue where
  reprPrec _ _ := "<opaque source observation>"

inductive ValueView where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : ObservedValue)
  | proxy (inner : Ty)
  | constructed (instantiation : DataConstructorInstantiation) (payloads : List ObservedValue)
  | mapping (keyType valueType : Ty) (entries : List (ObservedValue × ObservedValue))
  | closure (parameters : List TypedBinder) (resultType : Ty)
      (owner : SourceSpecialization.SpecializationKey)
      (captures : List (Resolved.LocalId × Nat))
      (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  | instantiated (substitution : Substitution)
      (requirements : List SourceTypedRuntime.LocalRequirementWitness) (principal : ObservedValue)
  | global (key : SourceSpecialization.SpecializationKey)
      (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  | builtin (function : BuiltinFunctionId)
  deriving Repr

def ObservedValue.view (value : ObservedValue) : ValueView :=
  match value.source with
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .product left right => .product ⟨left⟩ ⟨right⟩
  | .proxy inner => .proxy inner
  | .constructed instantiation payloads => .constructed instantiation (payloads.map ObservedValue.mk)
  | .mapping key value entries => .mapping key value (entries.map fun (key, value) => (⟨key⟩, ⟨value⟩))
  | .closure parameters result _ _ owner captures evidence =>
      .closure parameters result owner (captures.map fun (binder, location) => (binder, location.index)) evidence
  | .instantiated substitution requirements principal => .instantiated substitution requirements ⟨principal⟩
  | .global key evidence => .global key evidence
  | .builtin function => .builtin function

structure Principal where private mk ::
  private rawType : Ty
  private rawScheme : Scheme
  private source : ObservedValue

def Principal.type (principal : Principal) : Ty := principal.rawType
def Principal.scheme (principal : Principal) : Scheme := principal.rawScheme
def Principal.observation (principal : Principal) : ObservedValue := principal.source

instance : Repr Principal where
  reprPrec principal _ := "<principal " ++ repr principal.type ++ ">"

/-- This constructor needs an actual cached header/allocation join. The native
payload is deliberately not required to be a ground callable. -/
def Principal.ofRestored {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) : Principal :=
  ⟨restored.cell.type, restored.header.declaration.binder.scheme,
    ⟨restored.header.sourceValue row.environment⟩⟩

theorem Principal.ofRestored_type {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) :
    (Principal.ofRestored restored).type = restored.header.declaration.binder.scheme.body :=
  restored.raw_type

theorem Principal.ofRestored_captures {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) :
    (Principal.ofRestored restored).observation.view = .closure
      restored.header.parameters restored.header.resultType restored.header.state.metadata.owner
      (row.environment.map fun (binder, location) => (binder, location.index))
      restored.header.principal.context.evidence := rfl

inductive Contents where
  | data (value : SourceCorePublicValues.Value)
  | principal (value : Principal)
  | legacy (value : ObservedValue)
  deriving Repr

structure Cell where
  location : Nat
  type : Ty
  value : Option Contents
  deriving Repr

namespace Legacy

private def observeCell (location : Nat) (cell : SourceTypedRuntime.Cell) : Cell :=
  ⟨location, cell.type, cell.value.map fun value => .legacy ⟨value⟩⟩

/-- Migration-only factory. The existing deep validator decides admission;
read-only observation adds no closed-type, payload, or callable restriction.
The erased receipt means building the view does not rerun validation. -/
def observeAccepted (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan)
    (state : SourceTypedRuntime.RuntimeState) (fuel : Nat)
    (_accepted : state.isDeeplySafe fuel signatures plan = true) : List Cell :=
  state.heap.zipIdx.map fun (cell, index) => observeCell index cell

theorem observeAccepted_length {signatures : ProgramSignatures} {plan : SourceCompilationPlan.Plan}
    {state : SourceTypedRuntime.RuntimeState} {fuel : Nat}
    (accepted : state.isDeeplySafe fuel signatures plan = true) :
    (observeAccepted signatures plan state fuel accepted).length = state.heap.length := by
  simp [observeAccepted]

theorem observeAccepted_types {signatures : ProgramSignatures} {plan : SourceCompilationPlan.Plan}
    {state : SourceTypedRuntime.RuntimeState} {fuel : Nat}
    (accepted : state.isDeeplySafe fuel signatures plan = true) :
    (observeAccepted signatures plan state fuel accepted).map Cell.type = state.heap.map SourceTypedRuntime.Cell.type := by
  simp only [observeAccepted, List.map_map]
  change state.heap.zipIdx.map (SourceTypedRuntime.Cell.type ∘ Prod.fst) = state.heap.map SourceTypedRuntime.Cell.type
  rw [← List.map_map (f := Prod.fst) (g := SourceTypedRuntime.Cell.type), List.zipIdx_map_fst]

end Legacy
end Solcore.Frontend.SourceCoreHeapSnapshot
