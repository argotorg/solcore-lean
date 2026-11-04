import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ImperativeTrees
import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedBodies

/-!
# Cell-aware bodies: the imperative family

Named imperative bodies: body meaning and receipts, program profiles, Source body lifting and the named invocation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
/-! The selected named body obtains its bounded mixed-cell tree from its
original accepted compiler action. All row checks inspect the unchanged local
catalog; native child typing comes from the enclosing actual body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

def policy : SourceCoreLoops.Policy :=
  AcceptedNamedBodyFlow.namedPolicy prepared named diagnostics compiled.parents compiled.own

def scope (named : SourceCoreGeneralFunctions.Function) : SourceCoreLocalCell.Scope :=
  named.inputs.reverse.map fun binding => (binding.1.id, binding.2)

structure StaticProfile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) : Type where
  initializers : CellAwareNamedInitializerProfiles.Rows prepared named prepared.base.locals.bindings
  scan : CellAwareImperativeSourceBodyAdmission.Scan prepared.base.locals named.signature.key [] (source named)
    approved expected true statements

def staticProfile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    Option (StaticProfile prepared named statements approved expected) := do
  let ⟨initializers⟩ ← CellAwareNamedInitializerProfiles.rows? prepared named prepared.base.locals.bindings
  let ⟨scan⟩ ← CellAwareImperativeSourceBodyAdmission.scan? prepared.base.locals named.signature.key []
    (source named) expression expected prepared.fuel true statements
  pure ⟨initializers, scan⟩

structure Body (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (sourceContext : SourceSemantics.Context) (expected : TypeSystem.Ty) where
  flow : Expr
  tree : CellAwareImperativeTree.Tree prepared named compiled certificates administrative
    (diagnostics.reasonAt named.signature.key) sourceContext (scope named) true compiled.statements
    expected named.signature.resultType flow
  emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
    compiled.own.fellThroughReason compiled.own.table.escapedReason

/-- The public-facing static producer consumes checker facts and actual native
body typing; terminal certificates remain static compiler receipts. -/
theorem of_static_compilation
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    {approved : ExpressionId → Prop} {expected : TypeSystem.Ty}
    (profile : StaticProfile prepared named compiled.statements approved expected)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {administrative : Core.Context}
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      (policy compiled).lowerExpression fuel (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) (scope named) sourceContext)
    (sourceSignatures : sourceContext.signatures = checked.signatures)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (Body compiled certificates administrative sourceContext expected) := by
  have accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy compiled) prepared.fuel (source named)
      (scope named) compiled.statements named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compiled.own.fellThroughReason compiled.own.table.escapedReason = .ok compiled.body := compiled.bodyCompiled
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := bind_ok accepted
  have emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
      compiled.own.fellThroughReason compiled.own.table.escapedReason := (Except.ok.inj emitted).symm
  rw [emitted] at nativeTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  have tree := CellAwareImperativeCollectors.collected compiled record unique assignmentsPrepared (by
    intro fuel scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl) rfl rfl (by
    intro scope binder mono
    simp only [policy, AcceptedNamedBodyFlow.namedPolicy, SourceCoreGeneralFunctions.contextualBinder,
      mono, List.isEmpty_nil, ↓reduceIte]
    rfl) rfl
    (CellAwareNamedInitializerProfiles.Rows.at_site compiled _ profile.initializers)
    (CellAwareNamedInitializerProfiles.Rows.bodies_at_site compiled _ profile.initializers)
    children (profile.scan.syntax unique result typed) declarations sourceSignatures generated flowTyped
  exact ⟨⟨flow, tree, emitted⟩⟩

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  StaticProfile prepared named statements (CellAwareNamedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  staticProfile? prepared named statements
    (CellAwareNamedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

abbrev Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  CellAwareNamedBodyProducer.Certificate compiled sourceContext

/-- Actual expression compiler receipts close every child certificate of the
common mixed body. Only the original static typing and accepted body remain. -/
theorem of_compilation
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) (scope named) sourceContext)
    (sourceSignatures : sourceContext.signatures = checked.signatures)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply of_static_compilation compiled record assignmentsPrepared profile ?_ unique result typed declarations sourceSignatures nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact CellAwareNamedBodyProducer.expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyMeaning
/-! The complete bounded named body uses only its authentic compiler tree.
All expression and call behavior is derived from actual receipts; the caller
supplies the real parameter state and original Source typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) named invocation)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages whole))
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "registry" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "program" => Program.ofChecked whole.sourceProgram

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile))
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)

include bindings transport record receiver extension authority selectedBodies registered in
theorem preserves_selected {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      compiled.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (compiled.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    finalContext outcome after trace
  rw [body.emitted]
  apply CellAwareScopeFlowFinish.preserves bridge producer
    (CellAwareImperativeTreeBounds.preserves bridge bindings transport functions extension compiled record producer registered
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
      (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
      (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
      (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
      (fun _ _ => CompatiblePayload.ValueRep.unit)
      (fun childContext childRuntime childCovers childLedger childSize _ =>
        CellAwareNamedExpressionMeaning.preserves_selected compiled bridge profile receiver extension authority sourceEq issuer record
          childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers childSize)
      sourceEq body.tree issuer)
    sourceEq sourceTyped depth projection _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready trace

include bindings transport record receiver extension authority selectedBodies registered in
theorem reflects_selected {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (compiled.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        compiled.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted lexical physical owner sameLocation ready
    value finalStore completed
  rw [body.emitted] at completed
  apply CellAwareScopeFlowFinish.reflects bridge producer
    (CellAwareImperativeTreeBounds.reflects bridge bindings transport functions extension compiled record producer registered
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
      (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
      (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
      (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
      (fun _ _ => CompatiblePayload.ValueRep.unit)
      (CellAwarePhysicalFunctionOrigins.runtime_views profile)
      (fun childContext childRuntime childCovers childLedger childSize _ =>
        CellAwareNamedExpressionMeaning.reflects_selected compiled bridge profile receiver extension authority sourceEq issuer record
          childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers childSize)
      sourceEq body.tree issuer)
    sourceEq sourceTyped depth projection _ _ within environments heaps locals agrees actualTyped runtime covers sameLedger typed
    initial admitted lexical physical owner sameLocation ready completed

/- Compatibility adapters for callers with a whole-program receipt. -/
include bindings transport record receiver extension authority wellFormed registered in
theorem preserves {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      compiled.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (compiled.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (transport := transport) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

include bindings transport record receiver extension authority wellFormed registered in
theorem reflects {budget : Nat}
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context}
    {context : SourceSemantics.Context}
    {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareImperativeBodyProducer.Certificate compiled)
      administrative context expected)
    {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}
    (sourceTyped : StatementsHaveType (source named) control context compiled.statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok named.signature.resultType)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative (CellAwareImperativeBodyProducer.scope named) environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context compiled.statements →
    ∀ initial : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context (CellAwareImperativeBodyProducer.scope named) canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (compiled.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        compiled.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected named.signature.resultType faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨CellAwareImperativeBodyProducer.scope named, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (transport := transport) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
/-! The actual public preparation and named header produce the bounded mixed
body certificate. Source typing, parameter declarations and native body typing
are recovered from their original receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
theorem of_header
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareImperativeBodyProducer.Body prepared.compilation
      (CellAwareImperativeBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  have resultEq : header.function.resultType = prepared.named.specialized.function.inferredBodyType := by
    rw [header.agreement.result, aligned.named]
  have record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed)
    (values := SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
    (prepared := whole.indexed.ancestry) (program := Program.ofChecked whole.sourceProgram) header
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [sourceEq, statementsEq] at typed
  apply CellAwareImperativeBodyProducer.of_compilation prepared.compilation record
    (CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared prepared.selected prepared.compilation
      (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic))
    (by simpa only [resultEq] using profile) (sourceEq ▸ header.unique) rfl typed
  · simpa only [sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope, aligned.bindings,
      CellAwareImperativeBodyProducer.scope] using declarations
  · exact RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header)
  · simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope,
      aligned.bindings, aligned.body, CellAwareImperativeBodyProducer.scope] using native

include aligned in
/-- Whole-program typing is one way to supply the actual selected certificate. -/
theorem of_program
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named
      prepared.compilation.statements prepared.named.specialized.function.inferredBodyType) :
    Nonempty (CellAwareImperativeBodyProducer.Body prepared.compilation
      (CellAwareImperativeBodyProducer.Certificate prepared.compilation)
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      header.context header.function.resultType) :=
  of_header prepared aligned ready diagnostic (RecursiveNamedHeaderSourceTyping.certificate header wellFormed) member profile

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedInvocation
/-! One genuine named invocation joins marked parameters, the actual bounded
compiler body and restoration of the saved physical caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedInvocation
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
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (body : CellAwareImperativeBodyProducer.Body generation (CellAwareImperativeBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok header.named.signature.resultType)
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

private theorem reindex_physical
    {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
    {first second : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    (physical : CellAwareScopePhysical.Physical whole named context first canonical mapping world before store environment)
    (same : first = second) :
    ∃ next : CellAwareScopePhysical.Physical whole named context second canonical mapping world before store environment,
      next.location = physical.location ∧ next.native = physical.native := by
  cases same
  exact ⟨physical, rfl, rfl⟩

private theorem statements : generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection support in
/-- The Source allocation and body trace are independent inputs. Every native
entry, body step and saved-caller restoration is constructed from the compiler. -/
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_,typingFinal,typingFacts,functionTyped⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  rw [← statements header generation] at trace
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareImperativeBodyProducer.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareImperativeNamedBodyMeaning.preserves_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body functionTyped rfl projection issuer issued (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareImperativeBodyProducer.scope, ← sameBindings] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using evaluated
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ⟨wrap evaluatedHeader, ?_⟩, restoredEffect⟩
  exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
    restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection support in
/-- Actual native completion is unwrapped through the same named entry. Its
independent Source grade and concrete saved-caller post are returned together. -/
theorem reflects_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : Evaluates entryActual entryStore (generation.body.rename entryEmbedding) value bodyStore := by
    simpa only [sameBody] using bodyEvaluation
  obtain ⟨nativeSize, nativeTrace⟩ := evaluation_has_size compiledEvaluation
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_,typingFinal,typingFacts,functionTyped⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareImperativeBodyProducer.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareImperativeNamedBodyMeaning.reflects_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys)
    generation record profile receiver extension authority support.registryBodies producer
    (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body functionTyped rfl projection issuer issued (Nat.le_refl nativeSize)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareImperativeBodyProducer.scope, ← sameBindings] at meaning
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady nativeTrace
  have fullEffect := prefixEffect.trans bodyEffect
  have bodyCaller : Relates caller bodyState := related.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps fullEffect.worlds
      (prefixFrame.trans bodyFrame) bodyCaller
  have restoredEffect := CellAwareOwnedBodyRestoration.restored_effect caller bodyState owner.position instances fullEffect
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨sourceSize, entryEnvironment, entryHeap, finalContext, outcome, after, finalMap, finalWorld,
    entryAllocated, ?_, matched, ?_, ?_⟩
  · simpa only [statements header generation] using trace
  · refine ⟨completed, ?_⟩
    rw [finalEq]
    exact ⟨by simpa only [header.resultType] using result, restoredHeaps, fullEffect.maps, fullEffect.worlds,
      restoredFrame, fullEffect.metadata, returned, restoredRelated, post⟩
  · rw [finalEq]
    exact restoredEffect

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection wellFormed in
theorem preserves
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) (issued := issued) (projection := projection) <;> assumption

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection wellFormed in
theorem reflects
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        functions cells owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after finalStore := by
  apply reflects_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) (issued := issued) (projection := projection) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt
/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

open CellAwareNamedPreparedReceipt (administrative cast_generation cast_generation_body)

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body generation (CellAwareImperativeBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareImperativeBodyProducer.Body (cast_generation same generation)
      (CellAwareImperativeBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
  cases same
  exact body

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers key header mapping world store)

structure Receipt where
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named prepared.diagnostics prepared.code
  emitted : header.body = generation.body
  body : CellAwareImperativeBodyProducer.Body generation (CellAwareImperativeBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative)
    header.context header.function.resultType
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok header.named.signature.resultType
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
    (prepared.diagnostics.reasonAt header.named.signature.key)
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed prepared.diagnostics

include aligned in
theorem of_header_selected {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies whole)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareImperativeNamedBodyReceipt.of_header prepared aligned ready diagnostic (SelectedCompilationHeaderCertificates.certified bodyTyping header) member profile
  let generation := cast_generation aligned.named.symm prepared.compilation
  have actual := cast_body aligned.named.symm prepared.compilation body
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, administrative capture, header.parameterType, List.cons_append]
  have issuer := CellAwareNamedDiagnosticIssuer.of_prepared prepared diagnostic aligned
  rw [aligned.reasonAt] at issuer
  have issuerAt : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
      (prepared.diagnostics.reasonAt header.named.signature.key) := by
    simpa only [aligned.named] using issuer
  exact ⟨⟨generation, aligned.body.trans (cast_generation_body aligned.named.symm prepared.compilation).symm,
    prefixEq ▸ actual, (by simpa only [← header.resultType] using aligned.projection), issuerAt, CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic⟩⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include aligned in
theorem of_header {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedProgramProfiles
/-! The complete ordered named cache receives finite compiler profiles.
Root extraction accepts only the actual statement-root action, and a selected
slot recovers its original profile without dropping any other cached row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedProgramProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)

def statements (named : SourceCoreGeneralFunctions.Function) :
    Except SourceCoreGeneralFunctions.Error (List StatementId) :=
  (source named).roots.mapM (fun
    | .statement id => pure id
    | .expression id => throw (.expectedStatementRoot id))

structure Entry {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) where
  roots : List StatementId
  extracted : statements named = .ok roots
  profile : CellAwareImperativeBodyProducer.Profile prepared named roots
    named.specialized.function.inferredBodyType

def entry? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) : Option (Entry prepared named) :=
  match extracted : statements named with
  | .error _ => none
  | .ok roots => do
    let profile ← CellAwareImperativeBodyProducer.profile? prepared named roots
      named.specialized.function.inferredBodyType
    pure ⟨roots, extracted, profile⟩

inductive Rows {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    List SourceCoreGeneralFunctions.Function → Type where
  | nil : Rows prepared []
  | cons {named rest} (entry : Entry prepared named) (tail : Rows prepared rest) :
      Rows prepared (named :: rest)

def rows? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    (named : List SourceCoreGeneralFunctions.Function) → Option (Rows prepared named)
  | [] => some .nil
  | named :: rest => do
    let entry ← entry? prepared named
    let tail ← rows? prepared rest
    pure (.cons entry tail)

abbrev Profile {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :=
  Rows prepared prepared.base.functions

def profile? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    Option (Profile prepared) := rows? prepared prepared.base.functions

theorem Rows.at_slot {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : List SourceCoreGeneralFunctions.Function} (rows : Rows prepared named)
    {index : Nat} {function : SourceCoreGeneralFunctions.Function}
    (selected : named[index]? = some function) : Nonempty (Entry prepared function) := by
  induction rows generalizing index with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons entry tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero] at selected
      cases selected
      exact ⟨entry⟩
    | succ index => exact ih selected

def Entry.for_compilation {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} (entry : Entry prepared named)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) :
    CellAwareImperativeBodyProducer.Profile prepared named compiled.statements
      named.specialized.function.inferredBodyType := by
  have same : entry.roots = compiled.statements := Except.ok.inj (entry.extracted.symm.trans compiled.roots)
  exact same ▸ entry.profile

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedProgramProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceBodyLifting
/-! The accepted body supplies all lifting evidence internally. Ordinary Source
execution may stop at an actual selected-stage rejection at its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) named invocation)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages whole))
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "program" => Program.ofChecked whole.sourceProgram

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile))
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)


include bindings transport record receiver extension authority selectedBodies registered in
theorem lifts_selected
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context
      (CellAwareImperativeBodyProducer.scope named) true compiled.statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime
  exact CellAwareImperativeSourceTreeLifting.lifts bridge bindings transport functions extension compiled record producer registered
    (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
    (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
    (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
    (fun related => CompatibleExpressionPrimitives.bool_fields related) (fun _ _ => .unit)
    (fun childContext childRuntime childCovers childLedger size =>
      CellAwareNamedExpressionSourceLifting.lifts_selected compiled bridge profile receiver extension authority sourceEq issuer
        record childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers size)
    (fun childContext childRuntime childCovers childLedger size =>
      CellAwareNamedExpressionMeaning.preserves_selected compiled bridge profile receiver extension authority sourceEq issuer
        record childLedger (by simpa only [sourceEq] using childRuntime) selectedBodies childCovers size)
    sourceEq body.tree issuer (size := size) environments heaps locals agrees actualTyped runtime

/- Compatibility adapters for callers with a whole-program receipt. -/
include bindings transport record receiver extension authority wellFormed registered in
theorem lifts
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context
      (CellAwareImperativeBodyProducer.scope named) true compiled.statements := by
  apply lifts_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bindings := bindings) (transport := transport) (record := record) (receiver := receiver) (extension := extension) (authority := authority) (registered := registered) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceBodyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceInvocation
/-! Original Source bodies are lifted from the actual marked parameter entry.
The resulting public invocation includes the real earlier stage stop when a
guard rejects, retaining its reached heap and the saved caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceInvocation
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
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (body : CellAwareImperativeBodyProducer.Body generation (CellAwareNamedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
    header.context header.function.resultType)
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok header.named.signature.resultType)
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

private theorem reindex_physical
    {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}
    {first second : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment}
    (physical : CellAwareScopePhysical.Physical whole named context first canonical mapping world before store environment)
    (same : first = second) :
    ∃ next : CellAwareScopePhysical.Physical whole named context second canonical mapping world before store environment,
      next.location = physical.location ∧ next.native = physical.native := by
  cases same
  exact ⟨physical, rfl, rfl⟩

private theorem statements : generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same


include body record receiver extension sameLayouts sameGlobals sameBindings sameSolved selected authority issuer issued support in
theorem lift_selected
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
    ∃ stagedSize stagedContext stagedOutcome reached,
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages stagedSize invocation
        header.context environment bound header.function.body stagedContext stagedOutcome reached ∧
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached := by
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      _prefixFrame, _prefixEffect, lexical, reached, _related, rows, physical, frameEq, _wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record (support.certified header)
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements := by
    exact header.valid.ledger.trans sameSolved
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements := by
    obtain ⟨final, facts, typed, _completes⟩ := sourceReceipt.bodyTyped
    exact ⟨_, final, facts, by simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source] using typed⟩
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys cells
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  rw [← statements header generation] at trace
  obtain ⟨bodyPhysical, sameLocation, sameNative⟩ := reindex_physical physical
    (show header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) =
      CellAwareImperativeBodyProducer.scope header.named by rw [sameBindings]; rfl)
  have bodyReady : ProtectedStateTransition.CellAllocation.ReadyAt producer bodyPhysical.location bodyPhysical.native := by
    intro index state read
    rw [sameLocation, sameNative] at read ⊢
    exact ready state read
  have meaning := CellAwareImperativeNamedSourceBodyLifting.lifts_selected bridge (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) generation record profile receiver extension authority
    support.registryBodies producer (CallableIndexedAmbient.frame_registered whole.indexed) sourceEq body issuer issued
    (size := size) (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  simp only [CellAwareImperativeBodyProducer.scope, ← sameBindings] at meaning
  obtain ⟨stagedContext, stagedOutcome, reachedHeap, lifted, adapted⟩ :=
    meaning environments entryHeaps sourceReceipt.locals agrees actualTyped runtime covers sameLedger typed
      reached ⟨sourceReceipt.heapTyped, rows⟩ lexical bodyPhysical owner (sameLocation.trans frameEq).symm bodyReady trace
  have actual : Staging.Recursive.Statements (Program.ofChecked whole.sourceProgram) stages invocation
      header.context environment bound header.function.body stagedContext stagedOutcome reachedHeap := by
    simpa only [sameEnvironment, sameHeap, statements header generation] using lifted
  obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Statements.of_trace actual
  exact ⟨stagedSize, stagedContext, stagedOutcome, reachedHeap, measured, adapted⟩

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection support in
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
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  obtain ⟨stageSize, stagedContext, stagedOutcome, reached, measured, adapted⟩ :=
    lift_selected profile receiver extension owner caller header capture generation record sameLayouts sameGlobals sameBindings
      sameSolved selected authority issuer issued body support stable heapTyped argumentsTyped represented heaps allocated trace
  obtain ⟨value, finalStore, finalMap, finalWorld, result, effect⟩ :=
    CellAwareImperativeNamedInvocation.preserves_selected profile receiver extension owner caller header capture generation record sameLayouts
      sameGlobals sameBindings sameBody sameSolved selected authority issuer issued body projection support stable heapTyped argumentsTyped
      represented heaps allocated measured
  exact ⟨stagedContext, stagedOutcome, reached, value, finalStore, finalMap, finalWorld, adapted, result, effect⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include body record receiver extension sameLayouts sameGlobals sameBindings sameSolved selected authority issuer issued wellFormed in
theorem lift
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
    ∃ stagedSize stagedContext stagedOutcome reached,
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages stagedSize invocation
        header.context environment bound header.function.body stagedContext stagedOutcome reached ∧
      SelectedCompilationStageBodyLiftBounds.BodyAdapted finalContext outcome after stagedContext stagedOutcome reached := by
  apply lift_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) (issued := issued) <;> assumption

include body record receiver extension sameLayouts sameGlobals sameBindings sameBody sameSolved selected authority issuer issued projection wellFormed in
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
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld reached finalStore := by
  apply preserves_selected (support := SelectedCompilationNamedSupport.Support.of_program wellFormed) (body := body) (record := record) (receiver := receiver) (extension := extension) (sameLayouts := sameLayouts) (sameGlobals := sameGlobals) (sameBindings := sameBindings) (sameBody := sameBody) (sameSolved := sameSolved) (selected := selected) (authority := authority) (issuer := issuer) (issued := issued) (projection := projection) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceInvocation
end
