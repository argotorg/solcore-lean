import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds

/-! The actual named compiler head supplies static call authority. Strong
read and materialized application leaves are joined internally at real states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port Point)
open CellAwareScopeExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {named : SourceCoreGeneralFunctions.Function}
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functionModel]
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include positive bridge receiver stagePrepared sourceEq profile selectedBodies runtime covers unique actualFunctionType in
theorem preserves_selected
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow bridge context model named stages invocation callFaults size)
    (children : PreservesBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow bridge context model named stages invocation callFaults size) :
    PreservesAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact CellAwareScopeIndirectBounds.preserves_selected
    bridge profile compiler port.prepared rfl occurrence calleeCertificate calleeRecipe port.calleeFound sourceTyped
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
    port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
    stagePrepared receiver selectedBodies runtime covers actualFunctionType
    size calleeMeaning children applicationMeaning trace (Nat.le_refl _)

include positive bridge receiver stagePrepared sourceEq profile selectedBodies runtime covers unique actualFunctionType in
theorem reflects_selected
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow bridge context model named stages invocation callFaults size)
    (children : ReflectsBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow bridge context model named stages invocation callFaults size) :
    ReflectsAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact CellAwareScopeIndirectBounds.reflects_selected
    bridge profile compiler port.prepared rfl occurrence calleeCertificate calleeRecipe port.calleeFound sourceTyped
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
    port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
    stagePrepared receiver selectedBodies runtime covers actualFunctionType
    size calleeMeaning children applicationMeaning completed (Nat.le_refl _)

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique actualFunctionType in
theorem preserves
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow bridge context model named stages invocation callFaults size)
    (children : PreservesBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow bridge context model named stages invocation callFaults size) :
    PreservesAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (sourceEq := sourceEq) (profile := profile) (runtime := runtime) (covers := covers) (unique := unique) (actualFunctionType := actualFunctionType) <;> assumption

include positive bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique actualFunctionType in
theorem reflects
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow bridge context model named stages invocation callFaults size)
    (children : ReflectsBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow bridge context model named stages invocation callFaults size) :
    ReflectsAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (sourceEq := sourceEq) (profile := profile) (runtime := runtime) (covers := covers) (unique := unique) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
