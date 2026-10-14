import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosureEntryApplicationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds

/-! The original positive closure association fixes both the selected body
packet and its complete captured environment for real parameter entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (Packet PacketFor SupportFor)
open SelectedCompilationStageClosureEntryLifting (EntryLiftsBelow)

section Schema
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry)

def PacketBelow (packet : Packet code stages) (budget : Nat) : Prop :=
  match packet with
  | .terminal terminal => EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages terminal.child budget
  | .branching branching => EntryLiftsBelow (headers := headers) (keys := keys) code inputs model stages branching.child budget

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def BelowFor
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys
      bodyRegistry semanticFaults mapping world function native bindings parameter result)
    (packet : PacketFor association stages) (budget : Nat) : Prop :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
  | .principal _ _ code _ support _ _ _ _ _ _ =>
    PacketBelow (headers := headers) (keys := keys) code support.body.toContext model stages packet budget
end Schema

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native bindings parameterCore resultCore)
  (packet : PacketFor association.original stages)
  (supported : SupportFor association.original stages packet)
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include physical supported raw represented heaps stable in
theorem application_lifts (budget : Nat)
    (bodies : BelowFor model stages association.original packet budget)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {callerEvidence callEvidence : Dynamic.EvidenceEnvironment}
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size context
      callerEvidence callEvidence before (.closure function) sources outcome after)
    (within : size ≤ budget) :
    Staging.Recursive.Lifting.ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context
      before (.closure function) sources outcome after := by
  rcases association with ⟨original, slots⟩
  cases original with
  | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed _provenance =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
        code.compilation.administrativePrefix capturedScope captured.canonical := by
      cases packet <;> rw [supported.prefix] <;> exact slots
    obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
        EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
      cases packet with
      | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
      | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
    exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
      captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
      carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
      selected budget body called within
  | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
        code.compilation.administrativePrefix capturedScope captured.canonical := by
      cases packet <;> rw [supported.prefix] <;> exact slots
    obtain ⟨child, selected, body⟩ : ∃ child, stages.Closure function child ∧
        EntryLiftsBelow (headers := headers) (keys := keys) code support.body.toContext model stages child budget := by
      cases packet with
      | terminal terminal => exact ⟨terminal.child, terminal.selected, bodies⟩
      | branching branching => exact ⟨branching.child, branching.selected, bodies⟩
    exact SelectedCompilationStageClosureEntryApplicationLifting.lifts_application
      captured code history support.body.toContext functions represented owner caller heaps raw.captures reference
      carried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) observed physical stable raw.heaps typed
      selected budget body called within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosurePacketLifting
