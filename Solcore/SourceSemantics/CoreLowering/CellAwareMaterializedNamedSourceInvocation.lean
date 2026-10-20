import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSupport
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedSourceBodyLifting

/-! Original Source bodies are lifted from the actual marked parameter entry.
The resulting public invocation includes the real earlier stage stop when a
guard rejects, retaining its reached heap and the saved caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan header.named.signature.key = .ok header.named.specialized)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = header.named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = header.named.specialized.function.solvedRequirements)
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) header.named invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named (diagnostics.reasonAt header.named.signature.key))
  (body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "instances" => GeneralizedLocalInstanceValues.model whole.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer support in
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  let original := CellAwareNativeBodyCertificateMap.map_body
    (fun _ _ _ _ receipt => CellAwareMaterializedBodyProducer.Certificate.ordinary receipt) body
  obtain ⟨stageSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    CellAwareNamedSourceInvocation.lift_selected profile receiver extension owner caller header capture generation record sameLayouts sameGlobals sameBindings
      sameSolved selected authority issuer original support stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨value, finalStore, finalMap, finalWorld, result, output, effect⟩ :=
    CellAwareMaterializedNamedInvocation.preserves_selected profile owner caller header capture generation record sameLayouts
      sameGlobals sameBindings sameBody sameSolved selected issuer body support stable heapTyped argumentsTyped
      represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, output, effect⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked whole.sourceProgram) size
      header.context invocation.evidence invocation.source environment bound header.function.body finalContext outcome after) :
    ∃ stagedContext stagedOutcome reached value finalStore finalMap finalWorld,
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) reached value finalStore finalMap finalWorld faults ∧
      CellAwareMaterializedOutput.OutcomeAt whole finalMap finalWorld owner.key.frameLocation
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result stagedOutcome) value ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedSourceInvocation
