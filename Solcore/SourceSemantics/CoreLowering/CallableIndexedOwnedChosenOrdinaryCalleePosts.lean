import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCalleePost
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues

/-! Strict callee children retain their actual chosen function representation.
Selection is derived at that same reached state, preserving every prior branch.
Faults use the same child post and stop before argument evaluation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)


variable
  {rootCaller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed rootCaller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) rootCaller.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


variable (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
  (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) mapping world before store)

/-- Selection inspects the complete representation of this exact callee post.
Every General prior branch and the positive chosen constructor remain present. -/
theorem selected_at_value_post
    {function : Dynamic.Closure} {after : Dynamic.Heap} {value : Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
      (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.closure function) after value finalStore finalMap finalWorld) :
    CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
      (function := function) (native := value) (type := compiler.calleeCode.type) root expressionSyntax :=
  CallableIndexedOwnedChosenOrdinaryLambdaValues.selected_of_value root expressionSyntax profile post.2.1

section SourceValue
include certified found sourceTyped environments heaps locals agrees typed admitted
/-- The strict Source child produces both the whole real post and its selection.
No callee value, reached state or provenance qualifier is supplied separately. -/
theorem source_closure_at_callee (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {function : Dynamic.Closure} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee (.closure function) after)
    (smaller : size < budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost
        (registry := registry) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.closure function) after value finalStore finalMap finalWorld ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := value) (type := compiler.calleeCode.type) root expressionSyntax := by
  obtain ⟨value, finalStore, finalMap, finalWorld, post⟩ :=
    CallableIndexedOwnedStoredIndirectCalleePost.ForModel.preserves_callee_value
      (bridge := bridge) (functionModel := (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) (compiler := compiler)
      (certified := certified) (found := found) (sourceTyped := sourceTyped)
      (environments := environments) (modelHeaps := heaps) (locals := locals)
      (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
      budget children trace smaller
  exact ⟨value, finalStore, finalMap, finalWorld, post,
    selected_at_value_post (root := root) (expressionSyntax := expressionSyntax)
      (profile := profile) (bridge := bridge) (compiler := compiler) (initial := initial) post⟩

end SourceValue

section SourceFault
include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted
/-- A callee fault stops at the same actual post before arguments or invocation. -/
theorem source_fault_at_callee (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) context evidence source certificate faults size)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (fault : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) size
      context evidence source environment before callee reason after)
    (smaller : size < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) compiler initial (.fault reason) after
        (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld :=
  CallableIndexedOwnedStoredIndirectCalleePost.ForModel.preserves_callee_fault
    (bridge := bridge) (functionModel := (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)) (compiler := compiler) (prepared := prepared)
    (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
    (environments := environments) (modelHeaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children fault smaller

end SourceFault
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCalleePosts
