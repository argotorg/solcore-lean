import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBitNotStatementContracts

/-! The existing bare unary Head exposes the independent source trace and
the actual strict native continuation. No expression child is invented for
the administrative Unit RHS. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedBitNotStatementBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

open SourceSemantics.CoreLowering
open CompatibleBitNotStatements

variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include observations environments heaps locals agrees actualTyped in
/-- The actual Head selects the native continuation below the outer budget;
source reconstruction, heap receipts and seven slots stay in the same branch. -/
theorem header_continuation_below (errors : head.Errors faults) (budget : Nat)
    {next : Expr} {output : Ty} {value : Core.Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason after, SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source
      environment before assignment.target reason after) ∨
    (∃ sourceSize updated after written finalMap finalWorld slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      AdministrativePreserved mapping store finalMap written ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      remainingSize < budget ∧ EvaluationSize remainingSize (slots ++ actual) written
        (shift 7 (next.rename ξ)) value finalStore) := by
  cases Head.reflects_sized functions program evidence observations head environments heaps locals agrees actualTyped errors completed with
  | inl fault =>
    obtain ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, _rest⟩ := fault
    exact .inl ⟨sourceSize, reason, after, trace⟩
  | inr success =>
    obtain ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize, trace, heaps, maps, worlds,
      frame, metadata, count, typed, smaller, continuation⟩ := success
    exact .inr ⟨sourceSize, updated, after, written, finalMap, finalWorld, slots, remainingSize, trace, heaps, frame, count,
      typed, Nat.lt_of_lt_of_le smaller within, continuation⟩

end Tests.SourceCoreRecursiveNamedBitNotStatementBounds
