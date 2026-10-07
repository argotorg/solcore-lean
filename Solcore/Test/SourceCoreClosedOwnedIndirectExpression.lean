import Solcore.Test.SourceCoreClosedOwnedAnonymousInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters

/-! Complete indirect expressions close their literal/read children and their
actual anonymous body internally. The same concrete returned pool supplies all
record observations. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedIndirectExpression
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedLambdaValues
open CallableIndexedOwnedLambdaInvocationBounds ProtectedStateTransition
open Tests.SourceCoreClosedOwnedAnonymousInvocation

universe u v
/-- Static certificate replacement changes no field of the concrete entry. -/
private def entry_for_empty {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {Records : Type v} (protocol : Protocol.{u, v} Records) (gate : Location → NativeFrame → Prop)
    (original : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults)
    (emptyBody : original.function.body = []) (unitResult : original.function.resultType = .unit)
    (functions : FunctionModel values.checked.catalog ambient)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol gate original functions) :
    CallableRuntimeBodyOrigins.Stateful.Entry protocol gate (emptyOrigin original emptyBody unitResult) functions where
  mapping := entry.mapping
  world := entry.world
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := entry.heap
  store := entry.store
  embedding := entry.embedding
  actualContext := entry.actualContext
  frameLocation := entry.frameLocation
  native := entry.native
  environments := entry.environments
  heaps := entry.heaps
  locals := entry.locals
  lookups := entry.lookups
  actualTyped := entry.actualTyped
  reference := entry.reference
  read := entry.read
  unmapped := entry.unmapped
  initial := entry.initial
  gate := entry.gate

section OriginalBody
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyOrigin (program := program) code inputs registry faults)
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (layouts : body.origin.layouts = compiled.indexed.layouts)

include emptyBody unitResult extension faithful observations layouts in
/-- The original selected body receipt is closed by the actual empty-body
family; its full source, captured entry, code and reached state are identical. -/
theorem original_body_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin size := by
  intro entry outcome after trace
  let reindexed := entry_for_empty (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult) functions entry
  exact empty_preserves code inputs body emptyBody unitResult functions extension faithful observations layouts size
    reindexed trace

include emptyBody unitResult extension faithful observations functionTypes layouts in
/-- Native completion reconstructs the independent source grade at the same
original entry through the internally proved empty anonymous body family. -/
theorem original_body_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program body.origin size := by
  intro entry value finalStore completed
  let reindexed := entry_for_empty (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    body.origin (by simpa only [body.function_eq] using emptyBody)
    (by simpa only [body.function_eq] using unitResult) functions entry
  exact empty_reflects code inputs body emptyBody unitResult functions extension faithful observations functionTypes layouts size
    reindexed completed
end OriginalBody

section StaticChildren
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Embed an original product leaf through the existing builtin grammar. -/
private theorem product_child
    (child : CompatibleExpressionProducts.Tree.WithLiterals
      (fuel := fuel) (values := values) (source := source) (context := context)
      (solved := solved) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code) scope id lowered) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := child
  exact ⟨.fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product tree)))))),
    .fragment _ (.fragment _ (.fragment _ (.fragment _ (.fragment _ (.primitive _ (.product _ sites))))))⟩

/-- The authentic original local-read receipt supplies the callee leaf. -/
private theorem read_child
    (read : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id lowered :=
  product_child ⟨.read read, .read read⟩

/-- The genuine Boolean source node supplies the argument leaf, including
its full original empty metadata and runtime literal receipt. -/
private theorem bool_child {node : ExpressionNode} {name : String} (boolean : Bool)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean)) (type : node.type = .bool)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt scope id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ := by
  have original : CompatibleExpressionLiterals.Certificate solved source id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ :=
    ⟨node, found, .bool boolean form type requirements coercions⟩
  have runtime : CompatibleExpressionLiteralRuntime.Certificate solved source id
      ⟨.bool, LanguageResult.success (.bool boolean)⟩ :=
    ⟨node, found, .bool boolean form type requirements coercions, by intro literal resolution impossible; simp [form] at impossible⟩
  exact product_child ⟨.literal original, .literal original runtime⟩
/-- A real ordinary Source heap read constructs the callee execution; no
callee evaluation or execution meaning is assumed by this factory. -/
theorem actual_callee_read
    (readCode : CompatibleExpressionReads.Certificate fuel values source scope id (reasonAt id) lowered.expression)
    {program : SourceSemantics.Program} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.Closure}
    (lookup : Dynamic.Environment.LooksUp environment readCode.binder location)
    (read : Dynamic.Heap.Reads before location cell) (ordinary : cell.generalized = none)
    (stored : cell.value = some (.closure function)) :
    ∃ size, SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id
      (.closure function) before := by
  refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []],
    .intro (raw := .closure function) (middle := before) (lookupExpression?_sound readCode.metadata.found) ?_ ?_⟩
  · rw [readCode.form, readCode.metadata.requirements, readCode.metadata.coercions]
    exact .local rfl lookup read ordinary stored
  · rw [readCode.metadata.coercions]
    exact .nil
end StaticChildren

section Children
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations functionTypes sameLedger runtime unique uninitialized missing in
/-- Real read/literal certificates supply the finite child family. This
administrative lift applies only to the original builtin/data/read grammar. -/
private theorem children_preserve (size : Nat) :
    ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
      faults size := by
  apply ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed (ProtectedStateTransition.entry (protocol headers keys))
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes program evidence
        sameLedger runtime unique uninitialized missing)) size

include extension faithful observations functionTypes sameLedger runtime uninitialized missing in
/-- Original native read/literal completion reconstructs its own Source grade.
All child callbacks are proved here from static builtin certificates. -/
private theorem children_reflect (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
      faults size := by
  apply ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed (ProtectedStateTransition.entry (protocol headers keys))
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes program evidence
        sameLedger runtime uninitialized missing)) size
end Children

section SourceChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {name : String}

/-- Construct the actual ordered Boolean argument from its original node. -/
private theorem boolean_arguments (boolean : Bool)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinBoolean boolean))
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceExecutionSize.ExpressionsEvaluate program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []], SourceExecutionSize.stepSize []])
      context evidence source environment before [id] [.bool boolean] before := by
  refine .cons (.intro (raw := .bool boolean) (middle := before) (lookupExpression?_sound found) ?_ ?_) .nil
  · rw [form, requirements, coercions]
    exact .builtinBoolean rfl
  · rw [coercions]; exact .nil

/-- This real Source cell is appended after the callee/arguments heap. -/
def parameterHeap (before : Dynamic.Heap) (binder : TypedBinder) (boolean : Bool) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨binder.scheme.body, some (.bool boolean), none⟩]⟩

/-- A nonempty parameter allocation and an actual nil Unit body construct the
original closure application. No body trace or body meaning is a premise. -/
private theorem boolean_nil_call {function : Dynamic.Closure} (binder : TypedBinder) (boolean : Bool)
    (parameters : function.parameters = [binder]) (emptyBody : function.body = [])
    (unitResult : function.resultType = .unit) (frame : Dynamic.ClosureFrame program function)
    {callContext : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types callContext) :
    RecursiveNamedCallBounds.CallOutcome program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []])
      context evidence function.evidence before (.closure function) [.bool boolean] (.value .unit)
      (parameterHeap before binder boolean) := by
  have allocated : Dynamic.BindersAllocate function.captured before function.parameters [.bool boolean]
      ((binder.id, ⟨before.cells.length⟩) :: function.captured) (parameterHeap before binder boolean) := by
    rw [parameters]
    exact .cons .append (.nil _ _)
  have executed : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      callContext function.evidence function.source ((binder.id, ⟨before.cells.length⟩) :: function.captured)
      (parameterHeap before binder boolean) function.body callContext
      (.fallthrough ((binder.id, ⟨before.cells.length⟩) :: function.captured)) (parameterHeap before binder boolean) := by
    rw [emptyBody]; exact .nil
  exact .value (.closureUnit rfl frame unitResult extended allocated executed ⟨_, rfl⟩)
end SourceChildren

section ClosedParent
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee argument : ExpressionId} {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source scope
    id callee [argument] metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context) (unique : NodeOccurrencesUnique source)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  {binder : TypedBinder} (parameters : closure.code.receipt.loweredParameters = [(binder, .bool)])
  (emptyBody : function.body = []) (unitResult : function.resultType = .unit)
  (escaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = closure.code.receipt.resultCore)
  (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
  (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
  {boolean : Bool} {booleanNode : ExpressionNode} {booleanName : String}
  (booleanFound : source.lookupExpression? argument = some booleanNode)
  (booleanForm : booleanNode.form = .reference booleanName (.builtinBoolean boolean))
  (booleanType : booleanNode.type = .bool) (binderType : binder.scheme.body = .bool)
  (booleanRequirements : booleanNode.requirements = []) (booleanCoercions : booleanNode.coercions = [])
  (booleanTyped : ExpressionHasType source context argument .bool)
  (codes : compiler.codes = [⟨.bool, LanguageResult.success (.bool boolean)⟩])
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩) (stable : StableRows initial)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
  {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
  (readCode : CompatibleExpressionReads.Certificate fuel (.initial compiled.compatible.checked) source scope callee
    (reasonAt callee) compiler.calleeCode.expression)
  (ordinaryCode : compiler.calleeCode.expression = OptionalCell.read readCode.type (.var readCode.index) (reasonAt callee))
  {sourceLocation : Dynamic.Location} {sourceCell : Dynamic.Cell}
  (sourceLookup : Dynamic.Environment.LooksUp environment readCode.binder sourceLocation)
  (sourceRead : Dynamic.Heap.Reads before sourceLocation sourceCell)
  (ordinaryCell : sourceCell.generalized = none) (stored : sourceCell.value = some (.closure function))
  {nativeLocation : Location}
  (nativeLookup : actual[ξ readCode.index]? = some (.cellRef (OptionalCell.cellType readCode.type) nativeLocation))
  (nativeRead : store.read? nativeLocation = some (.inRight .unit carrier))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include ordinaryCode nativeLookup nativeRead in
/-- Exact ordinary native cell receipts construct the callee completion,
including its unchanged whole store. -/
private theorem native_callee : Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store := by
  rw [ordinaryCode]
  simpa only [OptionalCell.read, LanguageResult.success, LanguageResult.failure, Expr.rename,
    Renaming.lift] using OptionalCell.read_success (reasonAt callee) (.var nativeLookup) nativeRead

include parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes in
private theorem argument_tree : DataExpressionSequence.Tree source
    (CompatibleExpressionBuiltinRuntime.Certificate fuel (.initial compiled.compatible.checked) source context solved reasonAt)
    scope [argument] (closure.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes := by
  rw [parameters, codes]
  simpa only [List.map_cons, List.map_nil, binderType, booleanType] using
    (DataExpressionSequence.Tree.single booleanFound
      (bool_child (values := .initial compiled.compatible.checked) (context := context) (fuel := fuel)
        (scope := scope) (solved := solved) (reasonAt := reasonAt) boolean
        booleanFound booleanForm booleanType booleanRequirements booleanCoercions))

include parameters codes in
private theorem argument_types : compiler.codes.map (·.type) = closure.code.receipt.loweredParameters.map Prod.snd := by
  simp only [codes, parameters, List.map_cons, List.map_nil]

include booleanTyped parent in
private theorem source_arguments : ExpressionsHaveTypes source context [argument] [.bool] ∧ ([TypeSystem.Ty.bool] : List TypeSystem.Ty).length = metadata.argumentCount := by
  exact ⟨.cons booleanTyped (.nil _), parent.arity⟩

include parameters in
private theorem source_parameters : function.parameters = [binder] := by
  rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) closure.code, parameters]
  rfl

include parent parameters emptyBody unitResult escaped rawResult nativeResult stageAccepted arityAccepted
  booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions booleanTyped codes
  environments heaps locals agrees typed stable wellFormed runtime covers heapTyped sourceTyped
  ordinaryCode sourceLookup sourceRead ordinaryCell stored nativeLookup nativeRead
  extension faithful observations functionTypes sameLedger runtimeLedger unique uninitialized missing in
/-- This full accepted indirect parent is constructed from real read/literal
children and a genuine nonempty Source allocation. Its body and child meaning
families are closed internally; the returned pool is the actual restored post. -/
theorem parent_source_post :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id
        (.value .unit) (parameterHeap before binder boolean) ∧
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults (.value .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        finalMap finalWorld (parameterHeap before binder boolean) finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before (parameterHeap before binder boolean) ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, parameterHeap before binder boolean, finalStore, canonical⟩,
        Relates initial reached ∧ poolObservations initial reached := by
  obtain ⟨calleeSize, calleeTrace⟩ := actual_callee_read (context := context) readCode sourceLookup sourceRead ordinaryCell stored
  have calleeEvaluation := native_callee compiler readCode ordinaryCode nativeLookup nativeRead
  have captures := (CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped calleeTrace.sound).1
  have args := boolean_arguments (program := program) (context := context) (evidence := evidence)
    (environment := environment) (before := before) boolean booleanFound booleanForm booleanRequirements booleanCoercions
  have called := boolean_nil_call (program := program) (context := context) (evidence := evidence)
    (before := before) binder boolean (source_parameters closure parameters) emptyBody unitResult
    (closure.bodyOrigin escaped).frame closure.inputs.extended
  let argumentsSize := SourceExecutionSize.stepSize
    [SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [], SourceExecutionSize.stepSize []], SourceExecutionSize.stepSize []]
  let callSize := SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []]
  let budget := max argumentsSize callSize
  have sourceArgs := source_arguments compiler parent booleanTyped
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, original, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedIndirectSourceAdapters.preserves_bounded profile compiler prepared parent closure
      (argument_tree compiler closure parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes)
      (argument_types compiler closure parameters codes) escaped rawResult nativeResult
      environments heaps locals captures agrees typed initial stable wellFormed runtime covers heapTyped sourceArgs.1 sourceArgs.2
      budget
      (fun child _ => children_preserve (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes sameLedger runtimeLedger unique uninitialized missing child)
      (fun child _ => original_body_preserves closure.code closure.inputs (closure.bodyOrigin escaped)
        emptyBody unitResult (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations (by rfl) child)
      initial (Relates.refl initial) (.refl _) (.refl _) (AdministrativePreserved.refl _ _) (Dynamic.HeapMetadataExtend.refl _)
      calleeTrace calleeEvaluation stageAccepted arityAccepted
      (SourceSuffix.of_call args called) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, original, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, reached_pool_observations related⟩

include parent parameters emptyBody unitResult escaped rawResult nativeResult stageAccepted arityAccepted
  booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions booleanTyped codes
  environments heaps locals agrees typed stable wellFormed runtime covers heapTyped sourceTyped
  ordinaryCode sourceLookup sourceRead ordinaryCell stored nativeLookup nativeRead
  extension faithful observations functionTypes sameLedger runtimeLedger uninitialized missing in
/-- Original whole native completion reflects through the same accepted
parent and selected body. The Source size is independent, and every row is
observed on the actual restored final pool. -/
theorem parent_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧ poolObservations initial reached := by
  obtain ⟨calleeSize, calleeTrace⟩ := actual_callee_read (context := context) readCode sourceLookup sourceRead ordinaryCell stored
  have calleeEvaluation := native_callee compiler readCode ordinaryCode nativeLookup nativeRead
  have captures := (CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped calleeTrace.sound).1
  have sourceArgs := source_arguments compiler parent booleanTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    CallableIndexedOwnedIndirectSourceAdapters.reflects_bounded profile compiler prepared parent closure
      (argument_tree compiler closure parameters booleanFound booleanForm booleanType binderType booleanRequirements booleanCoercions codes)
      (argument_types compiler closure parameters codes) escaped rawResult nativeResult
      environments heaps locals captures agrees typed initial stable wellFormed runtime covers heapTyped sourceArgs.1 sourceArgs.2
      size
      (fun child _ => children_reflect (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes sameLedger runtimeLedger uninitialized missing child)
      (fun child _ => original_body_reflects closure.code closure.inputs (closure.bodyOrigin escaped)
        emptyBody unitResult (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        extension faithful observations functionTypes (by rfl) child)
      initial (Relates.refl initial) (.refl _) (.refl _) (AdministrativePreserved.refl _ _) (Dynamic.HeapMetadataExtend.refl _)
      calleeTrace calleeEvaluation stageAccepted arityAccepted completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, reached_pool_observations related⟩

end ClosedParent

end Tests.SourceCoreClosedOwnedIndirectExpression
