import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics

/-! The fault relation is constructed from the literal receiving diagnostic
 table. Its finite view keeps the error category and raw mapping or operand
 type. Source locations and reached heaps remain in the original semantic
 trace and reached witness; the public projected-place error has no location
 field. A decoded error does not manufacture a Source fault or an execution.

 The two reached-place interpretation fields follow from this definition.
 Assignment and unary rows still need a genuine producer preserving their
 issued-table lookups through program aggregation, compatible fixed-prefix
 rebuilding and the actual filtered callable append. This module supplies no
 arbitrary whole FaultRep, registry transport, or decoder-coverage premise.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
open Core Frontend SourceInference GeneralHeap CompatiblePayload
universe u v

/-- The actual public errors erase the runtime location but retain the raw
 missing-default type and assignment operator. Native lookup is separate. -/
inductive ErrorView : Dynamic.SemanticFault → SourceTypedRuntime.RuntimeError → Prop where
  | missing (rawValue : TypeSystem.Ty) :
      ErrorView (.missingMappingDefault rawValue) (.typeMismatch rawValue none)
  | projectedUninitialized (location : Dynamic.Location) :
      ErrorView (.uninitializedLocation location) .invalidPlaceProjection
  | readUninitialized (location : Dynamic.Location) (binder : Resolved.LocalId) :
      ErrorView (.uninitializedLocation location) (.uninitializedLocal binder)
  | operand (operator : Syntax.ValueAssignOp) (rawType : TypeSystem.Ty) :
      ErrorView (.invalidAssignmentOperands operator)
        (.invalidAssignmentOperands operator none (some rawType))
  | unary : ErrorView (.invalidUnaryOperand .bitNot) (.invalidUnaryOperand .bitNot none)

/-- Every related token is decoded by this exact table. No other table or
 caller-supplied semantic verdict enters the concrete relation. -/
def faults (table : SourceCoreFaultSites.Table) : FunctionCalls.FaultRep :=
  fun reason token => ∃ diagnostic,
    table.diagnostic? token = some diagnostic ∧ ErrorView reason diagnostic.error

/-- The literal decoder equation and finite view construct the relation. -/
theorem of_decoded {table : SourceCoreFaultSites.Table} {reason : Dynamic.SemanticFault}
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic)
    (view : ErrorView reason diagnostic.error) : faults table reason token :=
  ⟨diagnostic, decoded, view⟩

/-- The original state, prepared place and actual reached witness are exactly
 the indices requested by the genuine shape-diagnostic API. Both inclusions
 are derived internally from the concrete table-indexed relation. -/
theorem reached_interpretation
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {Records : Type v}
    {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
    {environment : Dynamic.Environment} {place : PlaceResolution}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {initialIndex : ProtectedStateTransition.Index} (initial : protocol.State initialIndex)
    (table : SourceCoreFaultSites.Table) :
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      checked registry functions protocol environment place prepared initial table (faults table) := by
  constructor
  · intro rawValue token diagnostic decoded error
    refine ⟨diagnostic, decoded, ?_⟩
    rw [error]
    exact .missing rawValue
  · intro reachedIndex reached location related witness diagnostic decoded error
    refine ⟨diagnostic, decoded, ?_⟩
    rw [error]
    exact .projectedUninitialized location

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedAssignmentFaults
