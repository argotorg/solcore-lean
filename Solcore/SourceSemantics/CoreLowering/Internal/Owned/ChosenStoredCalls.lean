import Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState

/-!
# Owned callables: chosen stored calls

Stored calls from chosen ordinary rows: parents, posts, allocation state and arity diagnostics.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
/-! The existing exact issued Compilation and receiving diagnostic table also
retain original bit-not entries. No additional issuance field is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
open Core Frontend SourceInference
open GenericAssignmentUnaryDiagnostics
open CallableIndexedOwnedPublicFaultReceiverTables
open RecursiveNamedPublicSpecializationMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}

theorem receiver_unary (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {own : SourceCoreProgramFaultSites.Function} (member : own ∈ issued.program.base.functions)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  cases reason <;> simp only [UnaryRep] at represented
  next operator =>
    cases operator <;> simp only at represented
    next =>
      obtain ⟨diagnostic, decoded, error⟩ := represented
      apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
      refine ⟨diagnostic, CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_assignment_diagnostic
        compiled receiver present member decoded, ?_⟩
      rw [error]
      exact .unary

theorem prepared_unary {row : SourceSpecialization.SpecializedFunction}
    (prepared : Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep prepared.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ :=
    CallableIndexedOwnedPublicAssignmentDiagnostics.prepared_member prepared receipt
  exact receiver_unary compiled receiver present member represented

theorem cached_unary {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (receipt : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep cached.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := CallableIndexedOwnedAssignmentProvenance.cached_member cached receipt
  exact receiver_unary compiled receiver present member represented

/-- A closure's same retained Compilation supplies the original unary table. -/
theorem compilation_unary {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
    (receipt : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : UnaryRep compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ :=
    CallableIndexedOwnedIssuedAssignmentRecipes.compilation_member compilation receipt
  exact receiver_unary compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
/-! Accepted stored parents consume the actual chosen callee and current
argument tuple. The body continuation is built internally; the original
invocation restores once and the caller protocol receives that same pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs
open CallableIndexedOwnedChosenOrdinaryFormedMembers (FactoryMember)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt extendIndex)
open CallableIndexedOwnedChosenOrdinaryLambdaInvocation (ChosenFor Validity)
open CallableIndexedOwnedChosenOrdinarySelectedCallReceipts (ArgumentAt)
open RecursiveNamedCatalogInvocationBounds (Below)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {owning : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : Compilation compiled.indexed owning.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) owning.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

variable (i : OrdinaryIndex compiled) (history : History i.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : ChosenFor (headers := headers) root expressionSyntax owner i history)

include member in
/-- Only proof facets extend; the same known owner, Code, factory and history remain. -/
theorem extend_chosen {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ChosenFor (headers := headers) root expressionSyntax owner (extendIndex i maps worlds) history := by
  obtain ⟨factory, origin, prefixContext, globals, referenceIndex, typed⟩ := member
  exact ⟨FactoryMember.extend root expressionSyntax factory maps worlds,
    origin, prefixContext, globals, referenceIndex, typed.weaken worlds⟩

include member in
/-- This is the same positive constructor, with no relation or value inverse. -/
theorem chosen_at : ChosenAt root expressionSyntax headers keys registry faults i history :=
  .ordinary owner member.factory member.origin member.prefixContext member.globals member.referenceIndex member.typed

/-- Actual static domains and diagnostic policies of this literal selected Support. -/
structure RuntimeInputs where
  domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax i.support.body.readFuel context i.function.evidence childScope headers
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : owning.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (CallableIndexedNamedGeneration.source owning.named)
  extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) identities
  uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id)
  missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag)
  table : SourceCoreFaultSites.Table
  rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table
  operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token
  unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token
  interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner owning)
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) table

variable (inputs : RuntimeInputs (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i profile owner)

/-- Map/world extension retains these exact static inputs and their actual factory. -/
def RuntimeInputs.extend {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    RuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax (extendIndex i maps worlds) profile owner := {
  domains := inputs.domains, wellFormed := inputs.wellFormed, sameLayouts := inputs.sameLayouts
  complete := inputs.complete, globals := inputs.globals, slots := inputs.slots, prefixZero := inputs.prefixZero
  noIndirect := inputs.noIndirect, extension := inputs.extension, identities := inputs.identities, faithful := inputs.faithful
  observations := inputs.observations, uninitialized := inputs.uninitialized, missing := inputs.missing
  table := inputs.table, rebuilt := inputs.rebuilt, operandIncluded := inputs.operandIncluded
  unaryIncluded := inputs.unaryIncluded, interprets := inputs.interprets }

variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure i.function) calleeHeap)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)
    compiler initial (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)
  (sameNative : calleeNative = value i.code i.captured.embedding history.native i.capturedActual)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  {certificate : GenericExpressionMeaning.Certificate}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (admitted : Admission bridge context initial)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure i.function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (accepted : CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown)

include member post actualFunctionType sameNative in
/-- The actual native callable type fixes only the genuine parameter and result projections. -/
theorem native_bundle :
    SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = i.code.receipt.parameterCore ∧
    compiler.resultType = i.code.receipt.resultCore := by
  exact receiving_bundle (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile)) (genericPost := post)
    (member := member) (sameNative := sameNative) (actualFunctionType := actualFunctionType)
where
  receiving_bundle
      (receiving : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
      (genericPost : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
        receiving compiler initial (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)
      (member : ChosenFor (headers := headers) root expressionSyntax owner i history)
      (sameNative : calleeNative = value i.code i.captured.embedding history.native i.capturedActual)
      (actualFunctionType : policy.callables.functionType = CallableContract.functionType) :
      SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = i.code.receipt.parameterCore ∧
      compiler.resultType = i.code.receipt.resultCore := by
    have nativeTyped : RuntimeValueHasType i.world calleeNative
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
      rw [sameNative]
      exact member.typed
    have actualType := genericPost.2.1.runtime_hasType.type_eq
    have callableType := compiler.callableType
    rw [actualFunctionType] at callableType
    have fields := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
      (callableType.trans (actualType.symm.trans nativeTyped.type_eq))
    exact ⟨(CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans fields.1), fields.2⟩


/-- The same genuine static inputs at the receiving function model. -/
structure ModelRuntimeInputs
    (receiving : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) where
  domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax i.support.body.readFuel context i.function.evidence childScope headers
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : owning.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  noIndirect : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirect (CallableIndexedNamedGeneration.source owning.named)
  extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    receiving identities
  uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id)
  missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag)
  table : SourceCoreFaultSites.Table
  rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table
  operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token
  unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token
  interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner owning)
      receiving table

/-- Specialize the original authentic inputs without changing any field. -/
def RuntimeInputs.receiving_model :
    ModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax i owner (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) := {
  domains := inputs.domains,
  wellFormed := inputs.wellFormed,
  sameLayouts := inputs.sameLayouts,
  complete := inputs.complete,
  globals := inputs.globals,
  slots := inputs.slots,
  prefixZero := inputs.prefixZero,
  noIndirect := inputs.noIndirect,
  extension := inputs.extension,
  identities := inputs.identities,
  faithful := inputs.faithful,
  observations := inputs.observations,
  uninitialized := inputs.uninitialized,
  missing := inputs.missing,
  table := inputs.table,
  rebuilt := inputs.rebuilt,
  operandIncluded := inputs.operandIncluded,
  unaryIncluded := inputs.unaryIncluded,
  interprets := inputs.interprets }

variable
  (receiving : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (members : CallableIndexedOwnedChosenOrdinaryLambdaFormationHeads.Members
    (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    owning root expressionSyntax receiving)
  (functionTypes : FunctionRuntimeViews receiving)
  (genericInputs : ModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
    root expressionSyntax i owner receiving)

/-- Only map/world proof facets extend at the same literal static factory. -/
def ModelRuntimeInputs.extend_receiving {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax (extendIndex i maps worlds) owner receiving := {
  domains := genericInputs.domains,
  wellFormed := genericInputs.wellFormed,
  sameLayouts := genericInputs.sameLayouts,
  complete := genericInputs.complete,
  globals := genericInputs.globals,
  slots := genericInputs.slots,
  prefixZero := genericInputs.prefixZero,
  noIndirect := genericInputs.noIndirect,
  extension := genericInputs.extension,
  identities := genericInputs.identities,
  faithful := genericInputs.faithful,
  observations := genericInputs.observations,
  uninitialized := genericInputs.uninitialized,
  missing := genericInputs.missing,
  table := genericInputs.table,
  rebuilt := genericInputs.rebuilt,
  operandIncluded := genericInputs.operandIncluded,
  unaryIncluded := genericInputs.unaryIncluded,
  interprets := genericInputs.interprets }


/-- Genuine static inputs exclude indirect calls only at supported body expressions. -/
structure ScopedModelRuntimeInputs
    (receiving : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) where
  domains : ∀ context, Validity i context → ∀ childScope,
    DomainAt root expressionSyntax i.support.body.readFuel context i.function.evidence childScope headers
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers
  globals : owning.globals = compiled.indexed.base.globals.length
  slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length
  prefixZero : owner.key.capturePrefix = 0
  noIndirectOn : CallableIndexedOwnedPreparedMixedBodyRuntimeBounds.NoIndirectOn
    (CallableIndexedNamedGeneration.source owning.named) (expressionSyntax (CallableIndexedNamedGeneration.source owning.named))
  extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    receiving identities
  uninitialized : ∀ id location, faults (.uninitializedLocation location) (rootReasonAt id)
  missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((rootReasonAt id).add tag)
  table : SourceCoreFaultSites.Table
  rebuilt : i.support.issued.diagnostics.tableForRegistry registry extension = .ok table
  operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep i.support.issued.assignments reason token → faults reason token
  unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep i.support.issued.assignments reason token → faults reason token
  interprets : ∀ context, Validity i context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := i.support.certificates i.support.body.readFuel i.function.source)
      (administrative := i.captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory i.support.diagnosticPolicy i.function.source i.support.issued.invalidOperand)
      (faults := faults) (registry := registry) i.support.issued
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner owning)
      receiving table

/-- A whole-Source exclusion supplies the supported-expression restriction. -/
def ModelRuntimeInputs.supported :
    ScopedModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax i owner receiving := {
  domains := genericInputs.domains,
  wellFormed := genericInputs.wellFormed,
  sameLayouts := genericInputs.sameLayouts,
  complete := genericInputs.complete,
  globals := genericInputs.globals,
  slots := genericInputs.slots,
  prefixZero := genericInputs.prefixZero,
  noIndirectOn := fun _allowed found => genericInputs.noIndirect found,
  extension := genericInputs.extension,
  identities := genericInputs.identities,
  faithful := genericInputs.faithful,
  observations := genericInputs.observations,
  uninitialized := genericInputs.uninitialized,
  missing := genericInputs.missing,
  table := genericInputs.table,
  rebuilt := genericInputs.rebuilt,
  operandIncluded := genericInputs.operandIncluded,
  unaryIncluded := genericInputs.unaryIncluded,
  interprets := genericInputs.interprets }

variable
  (scopedInputs : ScopedModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
    root expressionSyntax i owner receiving)

/-- Only map/world proof facets extend at the same literal static factory. -/
def ScopedModelRuntimeInputs.extend_supported {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends i.mapping futureMap) (worlds : WorldExtends i.world futureWorld) :
    ScopedModelRuntimeInputs (headers := headers) (registry := registry) (faults := faults)
      root expressionSyntax (extendIndex i maps worlds) owner receiving := {
  domains := scopedInputs.domains,
  wellFormed := scopedInputs.wellFormed,
  sameLayouts := scopedInputs.sameLayouts,
  complete := scopedInputs.complete,
  globals := scopedInputs.globals,
  slots := scopedInputs.slots,
  prefixZero := scopedInputs.prefixZero,
  noIndirectOn := scopedInputs.noIndirectOn,
  extension := scopedInputs.extension,
  identities := scopedInputs.identities,
  faithful := scopedInputs.faithful,
  observations := scopedInputs.observations,
  uninitialized := scopedInputs.uninitialized,
  missing := scopedInputs.missing,
  table := scopedInputs.table,
  rebuilt := scopedInputs.rebuilt,
  operandIncluded := scopedInputs.operandIncluded,
  unaryIncluded := scopedInputs.unaryIncluded,
  interprets := scopedInputs.interprets }


variable
  (genericPost : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge
    receiving compiler initial (.closure i.function) calleeHeap calleeNative calleeStore i.mapping i.world)



include calleeTrace parentTyped tree unique runtime covers locals admitted in
/-- The independently typed Source row supplies this exact original parameter bundle. -/
theorem ForModel.source_bundle_at_program
    (wellFormedAt : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) := by
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
  have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      i.function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  exact CallableIndexedOwnedStoredSourceBundleReceipts.source_bundle_of_trace
    unique compiler.found compiler.originalForm parentTyped tree compiler.argumentCoercions
    wellFormedAt runtime covers locals admitted.heap calleeTrace sourceBinders

include calleeTrace parentTyped tree unique runtime covers locals admitted genericInputs in
/-- The independently typed Source row supplies this exact original parameter bundle. -/
theorem ForModel.source_bundle_for_model :
    TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) := by
  exact ForModel.source_bundle_at_program (wellFormedAt := genericInputs.wellFormed) (i := i) (bridge := bridge) (compiler := compiler) (initial := initial)
    (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
    (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (tree := tree)


include calleeTrace parentTyped tree unique runtime covers locals admitted inputs in
/-- The independently typed Source row supplies this exact original parameter bundle. -/
theorem source_bundle :
    TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) := by
  exact ForModel.source_bundle_for_model (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (genericInputs := RuntimeInputs.receiving_model root expressionSyntax i profile owner inputs)
    (root := root) (expressionSyntax := expressionSyntax) (i := i)
      (owner := owner) (bridge := bridge) (compiler := compiler) (initial := initial)
    (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
    (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (tree := tree)

include calleeTrace parentTyped unique runtime covers locals admitted parent in
/-- Empty original output coercions preserve the real Source result type. -/
theorem ForModel.raw_result_at_program
    (wellFormedAt : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType i.function.resultType := by
  exact congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormedAt runtime covers locals admitted.heap calleeTrace)

include calleeTrace parentTyped unique runtime covers locals admitted genericInputs parent in
/-- Empty original output coercions preserve the real Source result type. -/
theorem ForModel.raw_result_for_model : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType i.function.resultType :=
  ForModel.raw_result_at_program (wellFormedAt := genericInputs.wellFormed) (i := i) (bridge := bridge) (compiler := compiler) (initial := initial)
    (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
    (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (parent := parent)


include calleeTrace parentTyped unique runtime covers locals admitted inputs parent in
/-- Empty original output coercions preserve the real Source result type. -/
theorem raw_result : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType i.function.resultType := by
  exact ForModel.raw_result_for_model (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (genericInputs := RuntimeInputs.receiving_model root expressionSyntax i profile owner inputs)
    (root := root) (expressionSyntax := expressionSyntax) (i := i)
      (owner := owner) (bridge := bridge) (compiler := compiler) (initial := initial)
    (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
    (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (parent := parent)

local notation "functions" => CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : ∀ context, Validity i context → RequirementIdsUnique context)

include profile receiving members functionTypes member scopedInputs calleeTrace genericPost sameNative parentTyped tree unique runtime covers locals admitted
  actualFunctionType accepted owners idsUnique in
/-- The parent core supplies its actual argument state. This finite leaf
constructs raw arguments and the chosen continuation internally at that state. -/
theorem ForModel.application_preserves_on (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge receiving compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := by
  have nativeFields := native_bundle.receiving_bundle (receiving := receiving) (genericPost := genericPost)
      (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
      (owner := owner) (member := member) (bridge := bridge) (compiler := compiler) (initial := initial)
      (sameNative := sameNative) (actualFunctionType := actualFunctionType)
  have rawBundle := ForModel.source_bundle_at_program (wellFormedAt := scopedInputs.wellFormed)
      (i := i) (bridge := bridge) (compiler := compiler) (initial := initial)
      (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
      (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (tree := tree)
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) i.code
  have sourceBinders : i.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
      i.function.parameters.map (fun binding => binding.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binding : TypedBinder => binding.scheme.body)) parameters).symm
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState argumentAdmission maps worlds frame metadata calleeTyped heapExtension represented argumentHeaps
    rawTyped packing bundle argumentsSize callSize outcome after argumentsTrace called _calledSuffix callWithin
  have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans accepted.physical.symm
  have arity : arguments.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
  let future := extendIndex i maps worlds
  have futureMember := extend_chosen root expressionSyntax i history owner member maps worlds
  have actualArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    future.captured future.code future.support future.prepared receiving profile represented arity.symm
    (by simpa only [sourceBinders, future, extendIndex] using rawBundle) nativeFields.1
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
    (calleeTyped.mono heapExtension) argumentAdmission.heap rawTyped packing bundle arity
  have actualRaw : Dynamic.ValuesHaveTypes i.function.context middle arguments i.support.body.types := by
    simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq i.support.body.extended] using raw.arguments
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultRep, finalHeaps,
    lastMaps, lastWorlds, lastFrame, lastMetadata, baseReached, baseRelated⟩ :=
    CallableIndexedOwnedChosenOrdinaryLambdaInvocation.ForModel.application_preserves_on
      («functions» := receiving) (members := members) (noIndirectOn := scopedInputs.noIndirectOn) (functionTypes := functionTypes)
      (observationsGeneric := scopedInputs.observations) (interpretsGeneric := scopedInputs.interprets)
      root expressionSyntax future history profile owner futureMember
      scopedInputs.domains scopedInputs.wellFormed scopedInputs.sameLayouts owners idsUnique scopedInputs.complete scopedInputs.globals scopedInputs.slots
      scopedInputs.prefixZero scopedInputs.extension scopedInputs.faithful scopedInputs.uninitialized scopedInputs.missing
      scopedInputs.rebuilt scopedInputs.operandIncluded scopedInputs.unaryIncluded
      (bridge.pool argumentState) raw.heaps actualRaw argumentAdmission.rows actualArguments argumentHeaps raw.captures
      outer budget withinOuter ih called callWithin
  obtain ⟨returned, _samePool, related⟩ := bridge.restore argumentState baseReached lastMaps lastWorlds lastFrame lastMetadata baseRelated
  refine ⟨value, finalStore, finalMap, finalWorld, accepted.beforeApplication, ?_, resultRep, finalHeaps,
    lastMaps, lastWorlds, lastFrame, lastMetadata, returned, related⟩
  simpa only [future, extendIndex, Captures.extend, sameNative] using application

include profile receiving members functionTypes member genericInputs calleeTrace genericPost sameNative parentTyped tree unique runtime covers locals admitted
  actualFunctionType accepted owners idsUnique in
/-- The parent core supplies its actual argument state. This finite leaf
constructs raw arguments and the chosen continuation internally at that state. -/
theorem ForModel.application_preserves_for_model (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge receiving compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := by
  exact ForModel.application_preserves_on (receiving := receiving)
    (scopedInputs := ModelRuntimeInputs.supported root expressionSyntax i owner receiving genericInputs)
    (genericPost := genericPost)
    (members := members)
    (functionTypes := functionTypes)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (owners := owners) (idsUnique := idsUnique) outer budget withinOuter ih suffix


include member inputs calleeTrace post sameNative parentTyped tree unique runtime covers locals admitted
  actualFunctionType accepted owners idsUnique in
/-- The parent core supplies its actual argument state. This finite leaf
constructs raw arguments and the chosen continuation internally at that state. -/
theorem application_preserves (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge functions compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := by
  exact ForModel.application_preserves_for_model (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (genericInputs := RuntimeInputs.receiving_model root expressionSyntax i profile owner inputs)
    (genericPost := post)
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (owners := owners) (idsUnique := idsUnique) outer budget withinOuter ih suffix

variable
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)

include profile receiving members functionTypes member scopedInputs calleeTrace genericPost sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType selected accepted owners idsUnique environments agrees typed in
/-- Ordered arguments and the whole Source parent use the original core once;
the chosen application leaf is constructed internally rather than supplied. -/
theorem ForModel.preserves_accepted_on (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge receiving compiler initial outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeState, calleeRelated, calleeAdmission⟩ := genericPost.2.2.2.2.2.2.2
  have calleeHeaps := genericPost.2.2.1
  have calleeMaps := genericPost.2.2.2.1
  have calleeWorlds := genericPost.2.2.2.2.1
  have calleeFrame := genericPost.2.2.2.2.2.1
  have calleeMetadata := genericPost.2.2.2.2.2.2.1
  have nativeTyped : RuntimeValueHasType i.world calleeNative
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) compiled.indexed.layouts.definitions := by
    rw [sameNative]; exact member.typed
  have rawResult := ForModel.raw_result_at_program (wellFormedAt := scopedInputs.wellFormed)
      (i := i) (bridge := bridge) (compiler := compiler) (initial := initial)
      (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
      (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (parent := parent)
  have nativeFields := native_bundle.receiving_bundle (receiving := receiving) (genericPost := genericPost)
      (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
      (owner := owner) (member := member) (bridge := bridge) (compiler := compiler) (initial := initial)
      (sameNative := sameNative) (actualFunctionType := actualFunctionType)
  have leaf : CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ApplicationPreserves (registry := registry) (faults := faults)
      bridge receiving compiler prepared (native := native) (context := context) (evidence := evidence)
      (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := i.mapping) (world := i.world) (store := calleeStore) (function := i.function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := i.code.receipt.resultCore)
      (dispatch := dispatch) budget suffix := ForModel.application_preserves_on
    (receiving := receiving) (members := members) (functionTypes := functionTypes)
    (scopedInputs := scopedInputs) (genericPost := genericPost)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (owners := owners) (idsUnique := idsUnique)
    outer budget withinOuter ih suffix
  exact CallableIndexedOwnedStoredIndirectCallBounds.ForModel.preserves_selected_with_application
    bridge receiving compiler prepared parent tree unique parentTyped scopedInputs.wellFormed runtime covers environments locals agrees typed
    initial admitted calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata nativeTyped calleeHeaps
    rawResult nativeFields.2 dispatch accepted.stage calleeTrace genericPost.1 selected budget children suffix argumentsWithin callWithin leaf

include profile receiving members functionTypes member genericInputs calleeTrace genericPost sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType selected accepted owners idsUnique environments agrees typed in
/-- Ordered arguments and the whole Source parent use the original core once;
the chosen application leaf is constructed internally rather than supplied. -/
theorem ForModel.preserves_accepted_for_model (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge receiving compiler initial outcome after value finalStore finalMap finalWorld := by
  exact ForModel.preserves_accepted_on (receiving := receiving)
    (scopedInputs := ModelRuntimeInputs.supported root expressionSyntax i owner receiving genericInputs)
    (genericPost := genericPost)
    (members := members)
    (functionTypes := functionTypes)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (owners := owners) (idsUnique := idsUnique) (parent := parent) (selected := selected)
    (environments := environments) (agrees := agrees) (typed := typed)
    outer budget withinOuter ih children suffix argumentsWithin callWithin


include member inputs calleeTrace post sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType selected accepted owners idsUnique environments agrees typed in
/-- Ordered arguments and the whole Source parent use the original core once;
the chosen application leaf is constructed internally rather than supplied. -/
theorem preserves_accepted (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial outcome after value finalStore finalMap finalWorld := by
  exact ForModel.preserves_accepted_for_model (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (genericInputs := RuntimeInputs.receiving_model root expressionSyntax i profile owner inputs)
    (genericPost := post)
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (owners := owners) (idsUnique := idsUnique) (parent := parent) (selected := selected)
    (environments := environments) (agrees := agrees) (typed := typed)
    outer budget withinOuter ih children suffix argumentsWithin callWithin

/-- The complete original accepted application receipts remain alongside the
independent Source grade, staged outcome and exact returned caller pool. -/
def ReflectedAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  CallableIndexedOwnedPreparedStoredIndirectApplication.ResultAt
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    (calleeMap := i.mapping) (calleeWorld := i.world) (sidecar := sidecar)
    bridge profile compiler prepared initial dispatch budget value finalStore

/-- The original whole fourth bind and caller tuple at the receiving model. -/
def ForModel.ReflectedResultAt (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge receiving compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge receiving compiler prepared initial budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
        context evidence source environment before id callee ids metadata (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults) (context := context)
        bridge receiving compiler initial outcome after value finalStore finalMap finalWorld


include profile receiving members functionTypes member scopedInputs calleeTrace genericPost sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType accepted in
/-- Reflection consumes the authentic whole fourth bind at its own argument
store, then the same chosen application and finite caller-pool lift once. -/
theorem ForModel.reflects_accepted_on (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge receiving compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge receiving compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ForModel.ReflectedResultAt (receiving := receiving) (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      i bridge compiler prepared initial dispatch budget value finalStore := by
  obtain ⟨_original, _step, _passed, qualified⟩ :=
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.ForModel.at_argument_post
      («functions» := receiving) (faults := faults) (genericPost := genericPost)
      root expressionSyntax bridge profile compiler prepared initial i history dispatch
      (chosen_at (faults := faults) root expressionSyntax i history owner member) calleeTrace sameNative parentTyped tree unique
      scopedInputs.wellFormed runtime covers locals admitted actualFunctionType budget original step passed
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, represented, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    maps, worlds, frame, metadataExtended, argumentState, related, argumentAdmission,
    remainingSize, remaining, remainingStrict, argumentReceipt⟩ := qualified
  cases argumentReceipt with
  | ordinary _owner _factory _origin _prefixContext _globals _referenceIndex _typed actualArguments _heaps raw actualRaw stable _reference _currentMetadata _currentCarried _allowed =>
    have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
        (.second (.var 2)) (.word dispatch.contract) argumentStore :=
      .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
    have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
      dispatch.contract dispatch.row dispatch.found read
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed.2.1] at gate
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed failed _strict =>
      have same := (evaluation_deterministic failed.sound gate).1
      cases same
    | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
      cases same
      subst stores
      have payloadTrace := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
      rw [sameNative] at payloadTrace
      let future := extendIndex i stepMaps stepWorlds
      have futureMember := extend_chosen root expressionSyntax i history owner member stepMaps stepWorlds
      obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
        lastMaps, lastWorlds, lastFrame, lastMetadata, baseReached, baseRelated⟩ :=
        CallableIndexedOwnedChosenOrdinaryLambdaInvocation.ForModel.application_reflects_on
          («functions» := receiving) (members := members) (noIndirectOn := scopedInputs.noIndirectOn) (functionTypes := functionTypes)
          (observationsGeneric := scopedInputs.observations) (interpretsGeneric := scopedInputs.interprets)
          root expressionSyntax future history profile owner futureMember
          scopedInputs.domains scopedInputs.wellFormed scopedInputs.sameLayouts scopedInputs.complete scopedInputs.globals scopedInputs.slots
          scopedInputs.prefixZero scopedInputs.extension scopedInputs.faithful scopedInputs.uninitialized scopedInputs.missing
          scopedInputs.rebuilt scopedInputs.operandIncluded scopedInputs.unaryIncluded
          (bridge.pool argumentState) raw.heaps actualRaw stable actualArguments argumentHeaps raw.captures
          outer budget withinOuter ih payloadTrace (Nat.le_of_lt applicationStrict)
      obtain ⟨returned, _samePool, lastRelated⟩ := bridge.restore argumentState baseReached
        lastMaps lastWorlds lastFrame lastMetadata baseRelated
      have nativeCount : (compiler.codes.map (·.type)).length = i.function.parameters.length := by
        simpa only [List.length_map] using compiler.ordered_children.1.symm.trans passed.1.symm
      have arity : arguments.length = i.function.parameters.length := represented.length.1.symm.trans nativeCount
      obtain ⟨parameter, sourceResult, rawTypes, _calleeTyping, argumentsTyping, application,
        _calleeTyped, calleeHeapTyped, _calleeExtension, calleeLocals, _rawTyped, _argumentHeapTyped,
        _heapExtension, _argumentLocals, _fullExtension, _rawArity, packed, packing, _packedTyped, _raw⟩ :=
        CallableIndexedOwnedStoredCallSourcePrefix.from_admission_with_arity bridge initial scopedInputs.wellFormed runtime covers locals admitted
          unique compiler.found compiler.originalForm parentTyped compiler.argumentCoercions arity
          calleeTrace argumentsTrace
      have count : rawTypes.length = metadata.argumentCount := by
        cases application with | intro count _ _ _ => exact count.symm
      have argumentsCount := arguments_count_of_source_admission scopedInputs.wellFormed runtime covers calleeLocals calleeHeapTyped
        argumentsTyping count argumentsTrace
      obtain ⟨sourceSize, sourceParent⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm
        parent.requirements parent.coercions compiler.argumentCoercions parent.arity scopedInputs.wellFormed runtime covers
        calleeLocals calleeHeapTyped argumentsTyping count calleeTrace (SourceSuffix.called argumentsTrace called)
      have coercions : Dynamic.CoercionPathExecutes (Program.ofChecked compiled.sourceProgram) context evidence
          middle metadata.argumentCoercions packed packed middle := by
        rw [compiler.argumentCoercions]; exact .nil
      have staged : Staging.CallBoundary.Executes (Program.ofChecked compiled.sourceProgram) (CallableLedger.frame sidecar)
          context evidence source environment before id callee ids metadata
          (CallableIndexedOwnedPreparedStoredIndirectApplication.boundaryOutcome outcome) after := by
        cases called with
        | value applied =>
          exact .applied calleeTrace.sound (by simpa only [prepared.call] using accepted.stage)
            argumentsTrace.sound packing coercions packing parent.arity argumentsCount applied.sound
        | fault failed =>
          exact .applicationFault calleeTrace.sound (by simpa only [prepared.call] using accepted.stage)
            argumentsTrace.sound packing coercions packing parent.arity argumentsCount failed.sound
      have rawResult := ForModel.raw_result_at_program (wellFormedAt := scopedInputs.wellFormed)
          (i := i) (bridge := bridge) (compiler := compiler) (initial := initial)
          (calleeTrace := calleeTrace) (parentTyped := parentTyped) (unique := unique)
          (runtime := runtime) (covers := covers) (locals := locals) (admitted := admitted) (parent := parent)
      have nativeFields := native_bundle.receiving_bundle (receiving := receiving) (genericPost := genericPost)
          (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
          (owner := owner) (member := member) (bridge := bridge) (compiler := compiler) (initial := initial)
          (sameNative := sameNative) (actualFunctionType := actualFunctionType)
      have parentRep := CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result
        receiving compiler rawResult nativeFields.2 resultRep
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceParent, staged, parentRep, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadataExtended.trans lastMetadata,
        returned, callerProtocol.trans related lastRelated,
        after_expression_sized initial returned admitted scopedInputs.wellFormed runtime covers locals parentTyped sourceParent
          (frame.trans lastFrame)⟩

include profile receiving members functionTypes member genericInputs calleeTrace genericPost sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType accepted in
/-- Reflection consumes the authentic whole fourth bind at its own argument
store, then the same chosen application and finite caller-pool lift once. -/
theorem ForModel.reflects_accepted_for_model (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) receiving owner index))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge receiving compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge receiving compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ForModel.ReflectedResultAt (receiving := receiving) (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      i bridge compiler prepared initial dispatch budget value finalStore := by
  exact ForModel.reflects_accepted_on (receiving := receiving)
    (scopedInputs := ModelRuntimeInputs.supported root expressionSyntax i owner receiving genericInputs)
    (genericPost := genericPost)
    (members := members)
    (functionTypes := functionTypes)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (parent := parent) outer budget withinOuter ih original step passed


include member inputs calleeTrace post sameNative parentTyped tree unique parent runtime covers locals admitted
  actualFunctionType accepted in
/-- Reflection consumes the authentic whole fourth bind at its own argument
store, then the same chosen application and finite caller-pool lift once. -/
theorem reflects_accepted (outer budget : Nat) (withinOuter : budget ≤ outer)
    (ih : ∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index))
    {value : Value} {finalStore : Store}
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared initial budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      (calleeMap := i.mapping) (calleeWorld := i.world)
      bridge functions compiler prepared initial budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    ReflectedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
      i profile bridge compiler prepared initial dispatch budget value finalStore := by
  exact ForModel.reflects_accepted_for_model (receiving := (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile))
    (genericInputs := RuntimeInputs.receiving_model root expressionSyntax i profile owner inputs)
    (genericPost := post)
    (members := fun _i _history member => member.formed.represents)
    (functionTypes := CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys registry faults profile)
    (root := root) (expressionSyntax := expressionSyntax) (i := i) (history := history)
    (profile := profile) (owner := owner) (member := member) (bridge := bridge) (compiler := compiler)
    (prepared := prepared) (initial := initial) (calleeTrace := calleeTrace) (sameNative := sameNative)
    (parentTyped := parentTyped) (tree := tree) (unique := unique) (runtime := runtime)
    (covers := covers) (locals := locals) (admitted := admitted) (actualFunctionType := actualFunctionType)
    (dispatch := dispatch) (accepted := accepted) (parent := parent) outer budget withinOuter ih original step passed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryIndirectExpressionBounds
/-! A strict child produces the actual callee post before any chosen route is
used. Genuine positive members can close the accepted parent at that same
post; prior and unclassified values remain in the original selection/prefix.
No whole callee, body or expression meaning is supplied to these ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryIndirectExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedChosenOrdinaryLambdaInvocation (ChosenFor)
open RecursiveNamedCatalogInvocationBounds (Below)
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
  {owning : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {rootCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed owning.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) owning.named diagnostics namedCode rootCompilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


variable (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
  (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile) mapping world before store)


local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)

section Source
variable {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeSize : Nat}

/-- Only static route receipts, a genuine positive member and the actual Source
suffix are supplied after the strict child has produced this literal post. -/
def SourceAcceptedOn (outer budget : Nat) (calleeNative : Value) (_calleeStore : Store)
    (calleeMap : LocationMap) (calleeWorld : StoreTyping) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ScopedModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    (∀ context, CallableIndexedOwnedChosenOrdinaryLambdaInvocation.Validity i context → RequirementIdsUnique context) →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after → argumentsSize ≤ budget → callSize ≤ budget →
    ∃ sourceSize result finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) result finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial outcome after result finalStore finalMap finalWorld

/-- Only static route receipts, a genuine positive member and the actual Source
suffix are supplied after the strict child has produced this literal post. -/
def SourceAcceptedAt (outer budget : Nat) (calleeNative : Value) (_calleeStore : Store)
    (calleeMap : LocationMap) (calleeWorld : StoreTyping) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    (∀ context, CallableIndexedOwnedChosenOrdinaryLambdaInvocation.Validity i context → RequirementIdsUnique context) →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids i.function
      argumentsSize callSize outcome after → argumentsSize ≤ budget → callSize ≤ budget →
    ∃ sourceSize result finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual store (lowered.expression.rename ξ) result finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial outcome after result finalStore finalMap finalWorld

include certified found sourceTyped parentTyped runtime covers environments heaps locals agrees typed admitted
  tree unique parent actualFunctionType owners in
/-- Construct the callee post once from the actual strict child. Its complete
selection keeps prior alternatives. The positive accepted continuation derives
its own body and ordered argument producer through the existing parent core. -/
theorem preserves_closure_parent_on (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (smaller : calleeSize < budget) :
    ∃ calleeNative calleeStore calleeMap calleeWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := calleeMap) (world := calleeWorld) (raw := calleeNode.type)
        (function := function) (native := calleeNative) (type := compiler.calleeCode.type) root expressionSyntax ∧
      SourceAcceptedOn (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar) (function := function) (calleeHeap := calleeHeap)
        (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
        (compiler := compiler) (prepared := prepared) (initial := initial) outer budget calleeNative calleeStore calleeMap calleeWorld := by
  obtain ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection⟩ :=
    CallableIndexedOwnedChosenOrdinaryCalleePosts.source_closure_at_callee
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile) (compiler := compiler)
      (certified := certified) (found := found) (sourceTyped := sourceTyped) (environments := environments)
      (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
      budget children trace smaller
  refine ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection, ?_⟩
  intro i history owner member sameFunction sameMap sameWorld sameNative inputs bodyIds dispatch selected accepted ih
    argumentsSize callSize outcome after suffix argumentsWithin callWithin
  cases sameFunction
  cases sameMap
  cases sameWorld
  exact CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.preserves_accepted_on
    (receiving := functions)
    (members := CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads.members owning root expressionSyntax profile)
    (functionTypes := CallableIndexedOwnedChosenOrdinaryLambdaValues.runtime_views
      (root := root) (expressionSyntax := expressionSyntax) headers keys registry faults profile)
    (scopedInputs := inputs) (genericPost := post) (root := root) (expressionSyntax := expressionSyntax)
    (i := i) (history := history) (profile := profile) (owner := owner) (member := member)
    (bridge := bridge) (compiler := compiler) (prepared := prepared) (initial := initial)
    (calleeTrace := trace) (sameNative := sameNative) (parentTyped := parentTyped) (tree := tree)
    (unique := unique) (parent := parent) (runtime := runtime) (covers := covers) (locals := locals)
    (admitted := admitted) (actualFunctionType := actualFunctionType) (dispatch := dispatch)
    (selected := selected) (accepted := accepted) (owners := owners) (idsUnique := bodyIds)
    (environments := environments) (agrees := agrees) (typed := typed)
    outer budget within ih children suffix argumentsWithin callWithin

include certified found sourceTyped parentTyped runtime covers environments heaps locals agrees typed admitted
  tree unique parent actualFunctionType owners in
/-- Construct the callee post once from the actual strict child. Its complete
selection keeps prior alternatives. The positive accepted continuation derives
its own body and ordered argument producer through the existing parent core. -/
theorem preserves_closure_parent (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (smaller : calleeSize < budget) :
    ∃ calleeNative calleeStore calleeMap calleeWorld,
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld ∧
      CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := calleeMap) (world := calleeWorld) (raw := calleeNode.type)
        (function := function) (native := calleeNative) (type := compiler.calleeCode.type) root expressionSyntax ∧
      SourceAcceptedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar) (function := function) (calleeHeap := calleeHeap)
        (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
        (compiler := compiler) (prepared := prepared) (initial := initial) outer budget calleeNative calleeStore calleeMap calleeWorld := by
  obtain ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection, resolve⟩ :=
    preserves_closure_parent_on
    (bridge := bridge) (profile := profile) (root := root) (expressionSyntax := expressionSyntax)
    (compiler := compiler) (prepared := prepared) (certified := certified) (found := found)
    (sourceTyped := sourceTyped) (parentTyped := parentTyped) (runtime := runtime) (covers := covers)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed)
    (initial := initial) (admitted := admitted) (tree := tree) (unique := unique) (parent := parent)
    (actualFunctionType := actualFunctionType)
    (owners := owners) outer budget within children trace smaller
  refine ⟨calleeNative, calleeStore, calleeMap, calleeWorld, post, selection, ?_⟩
  intro i history owner member sameFunction sameMap sameWorld sameNative inputs bodyIds dispatch selected accepted ih
    argumentsSize callSize outcome after suffix argumentsWithin callWithin
  exact resolve i history owner member sameFunction sameMap sameWorld sameNative
    (CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs.supported
      root expressionSyntax i owner functions inputs) bodyIds dispatch selected accepted ih
    suffix argumentsWithin callWithin

include prepared certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed admitted in
/-- A genuine strict callee fault closes the semantic parent before arguments.
It requires no selected positive member or callable body receipt. -/
theorem preserves_fault_parent (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionFaults (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee reason after)
    (smaller : calleeSize < budget) :
    ∃ sourceSize token finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id (.fault reason) after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge functions compiler initial (.fault reason) after
        (.inLeft lowered.type (.word token)) finalStore finalMap finalWorld :=
  CallableIndexedOwnedChosenOrdinaryCalleePosts.source_fault_at_callee
    (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
    (compiler := compiler) (prepared := prepared) (certified := certified) (found := found)
    (sourceTyped := sourceTyped) (parentTyped := parentTyped) (wellFormed := wellFormed)
    (runtime := runtime) (covers := covers) (environments := environments) (heaps := heaps)
    (locals := locals) (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    budget children failed smaller

end Source

section Native
variable {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}

/-- Original stage, argument and arity failures remain explicit. The accepted
positive branch now retains the completed body and actual full parent result. -/
def NativeChosenResult (i : OrdinaryIndex compiled)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
      (.closure i.function) calleeNative)
    (budget : Nat) (result : Value) (finalStore : Store) : Prop :=
  (∃ reason, result = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧
    CallableIndexedOwnedStoredIndirectStageBoundary.ForModel.ResultAt
      (registry := registry) (context := context) (evidence := evidence) (calleeNode := calleeNode)
      (mapping := i.mapping) (world := i.world) (calleeHeap := calleeHeap) (store := calleeStore)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
      bridge functions compiler prepared initial dispatch reason (dispatch.reason reason) finalStore) ∨
  CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.FaultPrefix
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    bridge functions compiler initial budget result finalStore ∨
  CallableIndexedOwnedStoredIndirectApplicationPrefix.ForModel.RejectedAt
    (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (sidecar := sidecar)
    bridge functions compiler prepared initial dispatch result finalStore ∨
  CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.ReflectedResultAt
    (receiving := functions) (registry := registry) (faults := faults) (context := context) (evidence := evidence)
    (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
    (calleeHeap := calleeHeap) (calleeNative := calleeNative) (calleeStore := calleeStore)
    i bridge compiler prepared initial dispatch budget result finalStore

/-- This is a finite static resolver at the actual callee tuple. It receives no
successful argument or application trace: the whole parent prefix derives both. -/
def NativeAcceptedOn (function : Dynamic.Closure) (outer budget : Nat)
    (calleeNative : Value) (calleeStore : Store) (calleeMap : LocationMap) (calleeWorld : StoreTyping)
    (result : Value) (finalStore : Store) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ScopedModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    NativeChosenResult (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
      (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap) (calleeStore := calleeStore)
      (calleeNative := calleeNative) (calleeSize := calleeSize)
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (prepared := prepared) (initial := initial) i dispatch budget result finalStore

/-- This is a finite static resolver at the actual callee tuple. It receives no
successful argument or application trace: the whole parent prefix derives both. -/
def NativeAcceptedAt (function : Dynamic.Closure) (outer budget : Nat)
    (calleeNative : Value) (calleeStore : Store) (calleeMap : LocationMap) (calleeWorld : StoreTyping)
    (result : Value) (finalStore : Store) : Prop :=
  ∀ (i : OrdinaryIndex compiled) (history : History i.code)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (_member : ChosenFor (headers := headers) root expressionSyntax owner i history),
    function = i.function → calleeMap = i.mapping → calleeWorld = i.world →
    calleeNative = value i.code i.captured.embedding history.native i.capturedActual →
    CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs
      (headers := headers) (registry := registry) (faults := faults) root expressionSyntax i owner functions →
    ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
        (.closure i.function) calleeNative),
    CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row →
    CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown →
    (∀ index, Below outer (CallableIndexedOwnedPublicPreparedNamedFamilyClosure.Family
      (headers := headers) (registry := registry) (faults := faults) functions owner index)) →
    NativeChosenResult (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
      (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap) (calleeStore := calleeStore)
      (calleeNative := calleeNative) (calleeSize := calleeSize)
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (prepared := prepared) (initial := initial) i dispatch budget result finalStore

include certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed admitted
  caller sidecarSource tree unique parent actualFunctionType in
/-- The original native parent prefix invokes the strict callee child once.
Its actual value retains all alternatives; only a genuine positive receipt at
that same tuple can enter the accepted body resolver. -/
theorem reflects_parent_on (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) result finalStore)
    (bounded : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
      bridge functions compiler initial budget result finalStore ∨
    ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
      EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      nativeSize < budget ∧
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize context evidence
        source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
      CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier result finalStore ∧
      ∀ function, sourceValue = .closure function →
        CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
          (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
          (function := function) (native := carrier) (type := compiler.calleeCode.type) root expressionSyntax ∧
        NativeAcceptedOn (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := after) (calleeSize := sourceSize)
          (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
          (compiler := compiler) (prepared := prepared) (initial := initial)
          function outer budget carrier calleeStore finalMap finalWorld result finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.reflects_parent_with_effects
      (bridge := bridge) (functionModel := functions) (compiler := compiler) (prepared := prepared)
      (certified := certified) (found := found) (sourceTyped := sourceTyped) (parentTyped := parentTyped)
      (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (environments := environments)
      (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (initial := initial)
      (admitted := admitted) (caller := caller) (sidecarSource := sidecarSource)
      (tree := tree) (unique := unique) (parent := parent) budget children completed bounded
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolve⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure
    cases sameClosure
    refine ⟨CallableIndexedOwnedChosenOrdinaryCalleePosts.selected_at_value_post
      (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
      (compiler := compiler) (initial := initial) post, ?_⟩
    intro i history owner member sameFunction sameMap sameWorld sameNative inputs dispatch selected accepted ih
    cases sameFunction
    cases sameMap
    cases sameWorld
    rcases resolve i.function rfl dispatch selected with rejected | ⟨_stage, arguments⟩
    · exact Or.inl rejected
    · rcases arguments with failed | ⟨original, step, rejected | passed⟩
      · exact Or.inr (Or.inl failed)
      · exact Or.inr (Or.inr (Or.inl rejected))
      · right; right; right
        exact CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ForModel.reflects_accepted_on
          (receiving := functions)
          (members := CallableIndexedOwnedChosenOrdinaryLambdaExpressionHeads.members owning root expressionSyntax profile)
          (functionTypes := CallableIndexedOwnedChosenOrdinaryLambdaValues.runtime_views
            (root := root) (expressionSyntax := expressionSyntax) headers keys registry faults profile)
          (scopedInputs := inputs) (genericPost := post) (root := root) (expressionSyntax := expressionSyntax)
          (i := i) (history := history) (profile := profile) (owner := owner) (member := member)
          (bridge := bridge) (compiler := compiler) (prepared := prepared) (initial := initial)
          (calleeTrace := trace) (sameNative := sameNative) (parentTyped := parentTyped) (tree := tree)
          (unique := unique) (parent := parent) (runtime := runtime) (covers := covers) (locals := locals)
          (admitted := admitted) (actualFunctionType := actualFunctionType) (dispatch := dispatch)
          (accepted := accepted) outer budget within ih original step passed

include certified found sourceTyped parentTyped wellFormed runtime covers environments heaps locals agrees typed admitted
  caller sidecarSource tree unique parent actualFunctionType in
/-- The original native parent prefix invokes the strict callee child once.
Its actual value retains all alternatives; only a genuine positive receipt at
that same tuple can enter the accepted body resolver. -/
theorem reflects_parent (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) result finalStore)
    (bounded : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (evidence := evidence)
      (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
      bridge functions compiler initial budget result finalStore ∨
    ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
      EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      nativeSize < budget ∧
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize context evidence
        source environment before callee sourceValue after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
        (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
        bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
      CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier result finalStore ∧
      ∀ function, sourceValue = .closure function →
        CallableIndexedOwnedChosenOrdinaryLambdaValues.Selected
          (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
          (function := function) (native := carrier) (type := compiler.calleeCode.type) root expressionSyntax ∧
        NativeAcceptedAt (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (sidecar := sidecar) (sourceTypes := sourceTypes) (calleeHeap := after) (calleeSize := sourceSize)
          (root := root) (expressionSyntax := expressionSyntax) (bridge := bridge) (profile := profile)
          (compiler := compiler) (prepared := prepared) (initial := initial)
          function outer budget carrier calleeStore finalMap finalWorld result finalStore) := by
  obtain ⟨sameCaller, sameSource, producedPrefix⟩ := reflects_parent_on
    (bridge := bridge) (profile := profile) (root := root) (expressionSyntax := expressionSyntax)
    (compiler := compiler) (prepared := prepared) (certified := certified) (found := found)
    (sourceTyped := sourceTyped) (parentTyped := parentTyped) (runtime := runtime) (covers := covers)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed)
    (initial := initial) (admitted := admitted) (tree := tree) (unique := unique) (parent := parent)
    (actualFunctionType := actualFunctionType)
    (wellFormed := wellFormed) (caller := caller) (sidecarSource := sidecarSource)
    outer budget within children completed bounded
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases producedPrefix with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolve⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure
    obtain ⟨selection, accepted⟩ := resolve function sameClosure
    refine ⟨selection, ?_⟩
    intro i history owner member sameFunction sameMap sameWorld sameNative inputs dispatch selected accepts ih
    exact accepted i history owner member sameFunction sameMap sameWorld sameNative
      (CallableIndexedOwnedChosenOrdinaryAcceptedStoredParent.ModelRuntimeInputs.supported
        root expressionSyntax i owner functions inputs) dispatch selected accepts ih

end Native
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryIndirectExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
/-! Actual initialized writes and allocations retain the chosen receiving model
and the same positive stored member. The generic producers run once; forward
forgetting of the function model is unnecessary at the heap boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt ChosenStoredAt extendIndex)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}

/-- The literal constructor supplies the payload relation in the chosen model. -/
theorem payload_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
  .function (.chosen_ordinary i history member)

/-- One actual write preserves the chosen heap relation and the known payload. -/
theorem written_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {heap after : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
    {target : Location} {cell : Dynamic.Cell}
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world heap store)
    (reference : ReferenceRepresents i.mapping i.world location target (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = (FunctionValues.sourceType i.function))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (written : Dynamic.Heap.Writes heap location (some (.closure i.function)) after) :
    ∃ updated, store.write? target (.inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)) = some updated ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        i.mapping i.world after updated ∧
      AdministrativePreserved i.mapping store i.mapping updated ∧
      Dynamic.HeapMetadataExtend heap after ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults i history after updated location := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world cell.type (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual)
      (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore) :=
    cellType.symm ▸ payload_member root expressionSyntax profile member
  obtain ⟨updated, writtenCore, finalHeaps, administrative⟩ :=
    GenericHeap.HeapRepresents.write_initialized heaps reference read represented written
  obtain ⟨old, oldValue, oldPayload, oldRead, _, _, oldRelated⟩ := heaps.cells reference.mapped
  have same := oldRead.functional read
  subst old
  have ordinary := oldRelated.ordinary
  obtain ⟨previous, previousRead, afterRead⟩ := written.reads_updated
  have same := previousRead.functional read
  subst previous
  have initialized : Dynamic.Heap.Reads after location
      ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩ := by
    simpa only [cellType, ordinary] using afterRead
  exact ⟨updated, writtenCore, finalHeaps, administrative, .of_write written,
    member, target, reference, initialized, Store.write?_reads_written writtenCore⟩

open CallableIndexedHistory CallableIndexedAllocationCompletion

theorem allocated_chosen_member
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {layout : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request)
    (same : annotation.original = allocation.expression)
    (definitions : layouts.definitions = compiled.indexed.layouts.definitions)
    (frameRegistered : layout.Registered compiled.indexed.layouts.definitions)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {contextLocation : Location}
    {frame : NativeFrame} {sourceLocation : Dynamic.Location}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout frame))
    (payloadAt : PayloadAt request actual (some (value i.code i.captured.embedding history.native i.capturedActual)))
    (payloadType : request.payloadType = (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore))
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    (allocated : Dynamic.Heap.Allocates before (FunctionValues.sourceType i.function) (some (.closure i.function)) sourceLocation after) :
    ∃ captured,
      Captures actual request.references request.scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
        (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ReferenceRepresents (i.mapping ++ [store.length + 2])
        (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved i.mapping store (i.mapping ++ [store.length + 2])
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) ∧
      ChosenStoredAt root expressionSyntax headers keys registry faults
        (extendIndex i (futureMap := i.mapping ++ [store.length + 2])
          (futureWorld := i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
          ⟨_, rfl⟩ ⟨_, rfl⟩) history after
        (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
  have represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile)
      i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) request.payloadType :=
    payloadType.symm ▸ payload_member root expressionSyntax profile member
  have cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root expressionSyntax headers keys registry faults profile))
      i.mapping i.world ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩
      (optionalValue request.payloadType (some (value i.code i.captured.embedding history.native i.capturedActual)))
      request.payloadType := .initialized represented
  obtain ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same definitions
      frameRegistered environments agrees heaps reference read payloadAt cell allocated
  have maps : LocationMap.Extends i.mapping (i.mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends i.world
      (i.world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType]) := ⟨_, rfl⟩
  have actualStored : ChosenStoredAt root expressionSyntax headers keys registry faults
      (extendIndex i maps worlds) history after
      (store ++ [SourceCoreCallableIndexedFrames.encode layout frame,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) sourceLocation := by
    refine ⟨ChosenAt.extend root expressionSyntax member maps worlds,
      store.length + 2, ?_, allocated.reads_new, ?_⟩
    · exact payloadType ▸ finalReference
    · simp [Store.read?] <;> rfl
  exact ⟨captured, selected, typed, evaluated, finalHeaps, finalReference, administrative, actualStored⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredPosts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
/-! One actual initialized marked allocation retains its complete reached caller
state and positively attaches the known chosen closure to the new optional cell.
Raw Source value typing and the compiler binder/payload equations stay explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt ChosenStoredAt extendIndex)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedAllocationCompletion TypedLexicalControl
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {i : OrdinaryIndex compiled} {history : History i.code}


variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}

local notation "receiving" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model
  root expressionSyntax headers keys registry faults profile

/-- The positive constructor supplies the payload relation, and the original
stateful producer runs once. Every output belongs to its same allocation tuple. -/
theorem allocate_initialized
    (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry receiving))
    {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    (binderType : binder.scheme.body = FunctionValues.sourceType i.function)
    (payloadType : payload = CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)
    (member : ChosenAt root expressionSyntax headers keys registry faults i history)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (valueTyped : Dynamic.ValueHasType context before (.closure i.function) binder.scheme.body)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      i.mapping i.world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving i.mapping i.world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes i.world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some (.closure i.function)) location after)
    (initial : callerProtocol.State ⟨scope, i.mapping, i.world, before, store, canonical⟩)
    (ready : producer.Ready initial contextLocation native)
    (admitted : Admission bridge context initial) :
    ∃ captured,
      Captures (value i.code i.captured.embedding history.native i.capturedActual :: canonical)
        (initializedRequest source scope binder payload).references scope captured ∧
      RuntimeValueHasType i.world captured (SourceCoreSourceCells.captureType scope)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      let closureValue := value i.code i.captured.embedding history.native i.capturedActual
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit closureValue]
      let nextWorld := i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := i.mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (closureValue :: actual) store (annotation.expression.rename ξ.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) nextMap nextWorld administrative
        ((binder.id, payload) :: scope) ((binder.id, location) :: environment) (nextRef :: canonical)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry receiving nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift (nextRef :: canonical) (nextRef :: closureValue :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: closureValue :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext)
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved i.mapping store nextMap nextStore ∧
      ∃ (maps : LocationMap.Extends i.mapping nextMap) (worlds : WorldExtends i.world nextWorld),
        Dynamic.HeapMetadataExtend before after ∧
        ReferenceRepresents nextMap nextWorld location (store.length + 2) payload ∧
        ChosenStoredAt root expressionSyntax headers keys registry faults
          (extendIndex i maps worlds) history after nextStore location ∧
        ∃ reached : callerProtocol.State
            ⟨(binder.id, payload) :: scope, nextMap, nextWorld, after, nextStore, nextRef :: canonical⟩,
          callerProtocol.Relates initial reached ∧
          Relates (bridge.pool initial) (bridge.pool reached) ∧
          Admission bridge nextContext reached := by
  have represented : ValueRep compiled.compatible.checked registry receiving i.mapping i.world
      binder.scheme.body (.closure i.function)
      (value i.code i.captured.embedding history.native i.capturedActual) payload := by
    rw [binderType, payloadType]
    exact CallableIndexedOwnedChosenOrdinaryStoredPosts.payload_member root expressionSyntax profile member
  obtain ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, related, nextAdmission⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge receiving definitions registered
      producer.toOrdinary mono extended ordinary allocation annotation same valueTyped represented
      environments heaps locals agrees actualTyped reference read allocated initial ready admitted
  have maps : LocationMap.Extends i.mapping (i.mapping ++ [store.length + 2]) := ⟨_, rfl⟩
  have worlds : WorldExtends i.world
      (i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have freshReference : ReferenceRepresents (i.mapping ++ [store.length + 2])
      (i.world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload])
      location (store.length + 2) payload := by
    refine ⟨?_, ?_⟩
    · rw [allocated.location_fresh, ← heaps.length_eq]
      simp
    · cases nextTyped with
      | cons typed _ =>
        cases typed with
        | cellRef found => exact found
  have stored : ChosenStoredAt root expressionSyntax headers keys registry faults
      (extendIndex i maps worlds) history after
      (store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (value i.code i.captured.embedding history.native i.capturedActual)]) location := by
    refine ⟨ChosenAt.extend root expressionSyntax member maps worlds, store.length + 2,
      payloadType ▸ freshReference, ?_, ?_⟩
    · change after.Reads location ⟨FunctionValues.sourceType i.function, some (.closure i.function), none⟩
      simpa only [binderType] using allocated.reads_new
    · simp [Store.read?] <;> rfl
  exact ⟨captured, captures, capturedTyped, evaluated, nextEnvironments, nextHeaps,
    nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation,
    maps, worlds, .of_allocation allocated, freshReference, stored,
    reached, related, bridge.related related, nextAdmission⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
/-! The original public fresh bootstrap and the public root startup share one
actual native state, including sessions extended by handle issuance. Successful
bootstrap identifies its exact initialized store/world, and startup retains those same indices. Any finite sequence of
actual bootstrap suspensions may precede completion. The proof does not replay
native execution or assume an initial owned pool, source heap or argument relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- The facade runtime-preservation receipt ties bootstrap completion to the native
StartAt used by the public root consumer. The completion is returned for the
owned initialization producer, rather than replaced by a hypothetical store. -/
theorem at_started {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
    {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
    {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
    {nativeArtifact : Artifact} {nativeSession : Session nativeArtifact}
    {nativeCheckpoint : Checkpoint nativeArtifact} {root : Root recipe.compiled}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {inputFuel bootstrapFuel : Nat}
    {world : StoreTyping} {store : Store} {payloads : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
    (fresh : publicBootstrap.FreshAt)
    (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
    (sameRuntime : bootstrapSession.SameRuntime publicSession)
    (atSession : publicSession.IndexedAt nativeSession)
    (started : StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
      world store payloads encodedValues) :
    ∃ value,
      runStateful bootstrapFuel (.initial recipe.bootstrap [] []) =
        .done value (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      world = (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type ∧
      store = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      nativeSession.NativeAt
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      nativeSession.RegistryAt compiled.compatible.checked.staticRegistry ∧
      StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        (RecursiveNamedCatalogPreparedInitialization.store compiled) payloads encodedValues := by
  obtain ⟨indexedBootstrap, indexedSession, value, finalStore, _atBootstrap, initial, sessionAt, completed, booted⟩ :=
    ready.indexed opened fresh
  have unchanged := sameRuntime.indexed sessionAt atSession
  have actualCompletion := initial.native_done completed
  have initialized := RecursiveNamedCatalogPreparedInitialization.completed_store prepared actualCompletion
  rw [initialized.2] at actualCompletion
  have nativeAt := unchanged.native_at booted.native_at
  rw [initialized.2] at nativeAt
  have registryAt := unchanged.registry_at (booted.registry_at initial)
  rw [Recipe.prepare_compiled prepared] at registryAt
  have sameState :
      world = (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type ∧
      store = RecursiveNamedCatalogPreparedInitialization.store compiled := by
    cases nativeSession
    exact ⟨started.state.1.symm.trans nativeAt.1, started.state.2.symm.trans nativeAt.2⟩
  have initializedStart : StartAt nativeSession key publicArguments inputFuel nativeCheckpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) payloads encodedValues := by
    simpa only [sameState.1, sameState.2] using started
  exact ⟨value, actualCompletion, sameState.1, sameState.2, nativeAt, registryAt, initializedStart⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicStoredClosureArityDiagnostics
/-! Actual public native presence retains the original callable diagnostic
factory internally. The selected row, physical mismatch and same runtime result
remain authentic receipts; no decoder or factory acceptance is an external law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicStoredClosureArityDiagnostics
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {sidecar : SourceCoreStageContracts.Sidecar} {function : Dynamic.Closure} {calleeNative : Value}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (different : function.parameters.length ≠ ids.length)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)

include selected different stages in
/-- The public sealed compiler provides the same actual callable diagnostic factory. -/
theorem arity_diagnostic :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id .beforeApplication
          (.argumentArityMismatch function.parameters.length ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  exact CallableIndexedOwnedStoredClosureArityDiagnostics.arity_diagnostic compiler prepared dispatch selected different generated

variable {context : SourceSemantics.Context}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)

include selected different stages in
/-- Public diagnostic provenance adds the exact table observation beside the
unchanged complete runtime result, including its real reached pool and effects. -/
theorem decoded_result {reason : Dynamic.SemanticFault} {after : Dynamic.Heap} {token : Word} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld) :
    CallableIndexedOwnedStoredClosureArityBoundary.ResultAt (registry := registry) (faults := faults)
      (context := context) bridge profile compiler prepared initial dispatch reason after token finalStore finalMap finalWorld ∧
    (faults reason token ∨ ∃ diagnostic,
      reason = .argumentArityMismatch function.parameters.length ids.length ∧
      native.diagnostics.rootTable.diagnostic? token = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch function.parameters.length ids.length) := by
  obtain ⟨_diagnostics, _cached, _callableCached, generated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  exact CallableIndexedOwnedStoredClosureArityDiagnostics.decoded_result bridge profile compiler prepared dispatch selected
    different generated initial result

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicStoredClosureArityDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds
/-! Actual pure stored-call prefixes retain the original whole fourth bind.
The real initialized callee post closes the first child by determinism; the
attached accepted row closes both guards. One original admitted sequence
produces the ordered arguments at that same caller state. Source argument
fault exclusion is an independent finite fact at this actual input heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes originalTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (argumentsTyped : ExpressionsHaveTypes source context ids originalTypes)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include tree unique argumentsTyped in
/-- Reflect the actual ordered arguments once. The same finite Source fault
exclusion applies to the returned trace, and its genuine post admits the next
original bind without a whole-program typing theorem. -/
theorem reflects_arguments (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {before : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (noFault : ∀ size reason after, SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram)
      size context evidence source environment before ids reason after → False)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) value finalStore)
    (strict : size < budget) :
    ∃ sourceSize sources values after finalMap finalWorld,
      value = .inRight .word (DataPatternValues.packValues values) ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before ids sources after ∧
      DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyped children
      environments heaps locals agrees typed initial admitted completed strict
  cases represented with
  | values represented =>
    cases trace with
    | values evaluated =>
      exact ⟨sourceSize, _, _, after, finalMap, finalWorld, rfl, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post.at_values⟩
  | fault matched =>
    cases trace with
    | fault failed => exact False.elim (noFault sourceSize _ after failed)

section Parent
variable {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming} {calleeNode : ExpressionNode}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {function : Dynamic.Closure} {calleeHeap : Dynamic.Heap} {calleeStore : Store} {calleeNative : Value}
  {calleeMap : LocationMap} {calleeWorld : StoreTyping} {calleeSize : Nat}
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
    bridge functions compiler first (.closure function) calleeHeap calleeNative calleeStore calleeMap calleeWorld)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original dispatch.row)
  (accepted : CallableIndexedOwnedChosenOrdinarySelectedCallReceipts.AcceptedAt dispatch native.diagnostics.unknown)
  (noFault : ∀ size reason after, SourceExecutionSize.ExpressionsFault (Program.ofChecked compiled.sourceProgram)
    size context evidence source environment calleeHeap ids reason after → False)

include post environments locals agrees typed tree unique argumentsTyped selected accepted noFault in
/-- The whole actual parent completion yields the original full successful
prefix, intermediate and cumulative effects, and entire fourth bind. The body
is left as its genuine measured application child; no invocation runs here. -/
theorem reflects_parent
    (_calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee (.closure function) calleeHeap)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap)
      (calleeNative := calleeNative) (calleeStore := calleeStore)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := context) (evidence := evidence) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeHeap := calleeHeap)
      (calleeNative := calleeNative) (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore := by
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child _strict =>
    have impossible := (evaluation_deterministic child.sound post.1).1
    cases impossible
  | continued child remaining _childStrict remainingStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic child.sound post.1
    cases same
    rw [stores] at remaining
    have read : Evaluates (calleeNative :: actual) calleeStore (.second (.var 0)) (.word dispatch.contract) calleeStore :=
      .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
    have gate := prepared.site.dispatch_known .beforeArguments native.diagnostics.unknown dispatch.contract dispatch.row dispatch.found read
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments accepted.first] at gate
    cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
    | failed failed _gateStrict =>
      have impossible := (evaluation_deterministic failed.sound gate).1
      cases impossible
    | continued gateTrace suffix _gateStrict suffixStrict =>
      obtain ⟨same, stores⟩ := evaluation_deterministic gateTrace.sound gate
      cases same
      rw [stores] at suffix
      obtain ⟨_calleeEvaluation, calleeRepresentation, calleeHeaps, calleeMaps, calleeWorlds,
        calleeFrame, calleeMetadata, calleeReached, calleeRelated, calleePost⟩ := post
      have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))
          canonical (.unit :: calleeNative :: actual) :=
        GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
      have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
        (RuntimeEnvironmentHasTypes.cons calleeRepresentation.runtime_hasType (typed.weaken calleeWorlds))
      cases CallableIndirectCallBounds.bind_completed suffix (Nat.le_of_lt suffixStrict) with
      | failed argumentTrace argumentStrict =>
        rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
        obtain ⟨_, _, _, _, _, _, impossible, _⟩ :=
          reflects_arguments bridge functions compiler tree unique argumentsTyped budget children
            (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
            calleeReached calleePost.at_value.2 noFault argumentTrace argumentStrict
        cases impossible
      | @continued argumentSize remainderSize argumentInput payload argumentStore _ _ argumentTrace remaining argumentStrict remainingStrict =>
        have originalArguments := argumentTrace
        rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentTrace
        obtain ⟨sourceSize, sources, values, after, finalMap, finalWorld, sameValue, evaluated, represented,
          finalHeaps, maps, worlds, frame, heapMetadata, reached, related, argumentAdmission⟩ :=
          reflects_arguments bridge functions compiler tree unique argumentsTyped budget children
            (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
            calleeReached calleePost.at_value.2 noFault argumentTrace argumentStrict
        cases sameValue
        have applicationPrefix : CallableIndexedOwnedStoredIndirectArgumentPrefix.ApplicationPrefix budget prepared.site
            native.diagnostics.unknown compiler.resultType actual argumentStore calleeNative (DataPatternValues.packValues values) value finalStore := by
          cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
          | failed failed strict => exact .failed failed strict
          | continued passed application gateStrict applicationStrict => exact .passed passed application gateStrict applicationStrict
        rcases CallableIndexedOwnedStoredIndirectApplicationPrefix.resolve_application dispatch selected applicationPrefix with rejected | succeeded
        · exact False.elim (rejected.1 accepted.physical)
        · obtain ⟨physical, fourth, applicationSize, application, applicationStrict⟩ := succeeded
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨_, sourceSize, sources, values, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
              evaluated, represented, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
              calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
              ⟨reached, callerProtocol.trans calleeRelated related, argumentAdmission⟩,
              ⟨_, remaining, remainingStrict, applicationPrefix⟩⟩
          · exact ⟨_, sourceSize, sources, values, after, _, finalMap, finalWorld, originalArguments, argumentStrict,
              evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata,
              calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
              ⟨reached, callerProtocol.trans calleeRelated related, argumentAdmission⟩,
              ⟨_, remaining, remainingStrict⟩⟩
          · exact ⟨physical, fourth, values, _, _, applicationSize, remaining, remainingStrict, application, applicationStrict⟩

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectResultSuccess
/-! The actual successful Source callee trace and genuine empty output
coercions identify the Source parent result internally. Four finite adapters
reuse the frozen same-Site continuation, preserving the actual callee post,
returned pool and independent Source/native grades. Physical binder count,
authentic contextual binder policy, strong ordinary/principal provenance and
accepted stage gates remain explicit. Rejection, nonempty coercions and other
origin branches remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectResultSuccess
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredIndirectCalleePost (ValuePost)
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
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  {named : CallableIndexedNamedGeneration.Named} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {sourceEvidence : Dynamic.EvidenceEnvironment}
  {capturedEnvironment : Dynamic.Environment} {captureScope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (captured : Captures compiled.indexed mapping world captureScope capturedEnvironment capturedActual)
  (site : Site compiled.indexed named parameters result statements sourceContext sourceEvidence capturedEnvironment
    captureScope captured.administrative)
  (history : History site.code)
  (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key [])
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

section Ordinary
variable (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support site.code registry faults)
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (referenceIndex : site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named) (support.expressionSyntax (CallableIndexedNamedGeneration.source named))
    support.body.context (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = site.code.receipt.loweredParameters.length)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete ordinary receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.preserves_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- Native ordinary continuation keeps the real callee store and complete
application bound, then reflects an independently sized Source parent. -/
theorem reflects_ordinary (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.reflects_ordinary
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin prefixContext observed referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below completed within

end Ordinary

section Principal
variable (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults)
  (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 captureScope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
  (referenceIndex : site.code.referenceIndex = captureScope.length + 1 + compiled.indexed.base.globals.length)
  (nativeTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)
  (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named) (support.expressionSyntax (CallableIndexedNamedGeneration.source named))
    support.body.context (.statements true statements) result)
  (post : ValuePost (registry := registry) (faults := faults) (actual := actual) (ξ := ξ)
    (calleeNode := calleeNode) (context := context) bridge profile compiler first
    (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual) store mapping world)
  (binderCount : ids.length = site.code.receipt.loweredParameters.length)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) (CallableIndexedLambdaValues.value site.code captured.embedding history.native capturedActual))
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)) calleeHeap)

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- The concrete principal receipt continues at exactly the strict child's
returned pool; the original argument and body bounds are unchanged. -/
theorem preserves_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids (closure named parameters result statements sourceContext sourceEvidence capturedEnvironment)
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.preserves_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below suffix argumentsWithin callWithin

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex nativeTyped escaped syntaxTree post
  binderCount stages caller sidecarSource dispatch accepted calleeTrace in
/-- Native principal continuation keeps the real callee store and complete
application bound, then reflects an independently sized Source parent. -/
theorem reflects_principal (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have rawResult := congrArg SourceCoreRawMetadata.runtimeType
    (CallableIndexedOwnedStoredSourceResultReceipts.source_result_of_trace
      unique compiler.found compiler.originalForm parentTyped parent.coercions
      wellFormed runtime covers locals firstAdmission.heap calleeTrace)
  exact CallableIndexedOwnedStoredIndirectSiteSuccess.reflects_principal
    bridge profile compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed
    first firstAdmission owner captured site history binderPolicy actualFunctionType support origin observed leading referenceIndex
    nativeTyped escaped syntaxTree post binderCount rawResult stages caller sidecarSource dispatch accepted calleeTrace
    budget children below completed within

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectResultSuccess
end
