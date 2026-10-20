import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch

/-! The whole indirect parent connects its literal callee, gates, ordered
arguments and actual materialized application in both directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  selectedBodies runtime covers actualFunctionType in
theorem preserves_selected (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  rcases CellAwareScopeIndirectSourcePrefixDispatch.preserves_fault_or_application
      bridge profile compiler prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
      environments heaps locals agrees typed initial admitted authority physical owner ownerFrame
      caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
      budget calleeMeaning children trace within with failed | applied
  · exact failed
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap, sources,
      _size, strict, child, accepted, arguments, called, prefixResult⟩ := applied
    exact CellAwareScopeIndirectApplicationDispatch.preserves_application_selected
      bridge profile compiler prepared sourceEq occurrence found locals initial authority physical owner ownerFrame
      guardFrame sourceParent tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType
      budget applicationMeaning child accepted arguments called strict prefixResult

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  selectedBodies runtime covers actualFunctionType in
theorem reflects_selected (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareScopeIndirectApplicationDispatch.ReflectedResult (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  rcases CellAwareScopeIndirectFaultDispatch.reflects_fault_or_application
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial owner view guardFrame
      profile calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted
      authority physical ownerFrame caller originalUnique sourceParent tree unique parentTyped
      budget calleeMeaning children completed within with failed | applied
  · obtain ⟨sourceSize, failure, after, token, finalMap, finalWorld, trace, valueEq,
      _evaluated, represented, rest⟩ := failed
    rw [valueEq]
    exact ⟨sourceSize, .fault failure, after, finalMap, finalWorld, trace, represented, rest⟩
  · exact CellAwareScopeIndirectApplicationDispatch.reflects_application_selected
      bridge profile compiler prepared sourceEq occurrence found sourceTyped locals initial admitted authority physical
      owner ownerFrame sourceParent tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType
      budget applicationMeaning completed applied

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  wellFormed runtime covers actualFunctionType in
theorem preserves (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (calleeCertificate := calleeCertificate) (calleeRecipe := calleeRecipe) (found := found) (sourceTyped := sourceTyped) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (caller := caller) (view := view) (originalUnique := originalUnique) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  wellFormed runtime covers actualFunctionType in
theorem reflects (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareScopeIndirectApplicationDispatch.ReflectedResult (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (calleeCertificate := calleeCertificate) (calleeRecipe := calleeRecipe) (found := found) (sourceTyped := sourceTyped) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (caller := caller) (view := view) (originalUnique := originalUnique) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
