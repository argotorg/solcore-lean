import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.PublicExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.SourceDiagnosticTypingOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction

/-!
# Owned callables: contextual lambdas

Producers, diagnostics, static receipts and prepared bounds of contextual lambdas, and receipts of typed closures.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedProducer
/-! The actual contextual producer retains its literal view and diagnostic
function together with the same Site and full compiler policy. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

theorem of_contextual_with_issued_recipe_exact {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt prepared diagnostics)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
        site.code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) ∧
        CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code ∧
        site.code.view = view ∧ site.code.reasonAt = reasonAt := by
  obtain ⟨policy, lowerBody, accepted, ⟨receipt⟩, allocationProfile, manifest, expressionProfile, callables, projector, binderPolicy, bodyRecipe, policyRecipe⟩ :=
    contextual_certificate_with_policy_recipe prepared compiled record found (form.trans sourceForm) owner requirements coercions ordinary read accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReasonAt, _sourceNode, _node, _receipt⟩ :=
    of_certificate prepared sourceContext evidence captured receipt accepted profile viewOfSource
      sourceFound sourceForm found form allocationProfile manifest expressionProfile callables projector
      (by rw [policyRecipe.snapshotLambda]) typed
  have actualBody : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compiled site.code :=
    sameBody.trans bodyRecipe
  have actualPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe
      compiled site.code.fuel site.code.policy := by
    rw [sameFuel, samePolicy]
    exact policyRecipe
  exact ⟨site, identifier, emitted,
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans binderPolicy,
    sameBody.trans bodyRecipe,
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes
      compiled issued actualBody actualPolicy site.compilation, sameView, sameReasonAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
/-! The owning Source and the actual diagnostic preparations remain separate
from a lambda's body context. Reached projected faults use the same prepared
head and table; no Header is reconstructed for the lambda. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces ProtectedPlaceReachedDiagnostics
universe u v

/-- Both preparations and the complete Source typing concern this literal
owner and Source. Collection membership retains the actual issuer occurrence. -/
structure IssuedSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : SourceSpecialization.SpecializationKey) (source : TypedSource) where
  first : Nat
  assignments : SourceCoreAssignmentFaultSites.Table
  assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignments
  typing : EmittedDiagnosticTokenPlan.UnaryTyped source ∧ AssignmentDiagnosticOrigins.OperandsTyped source
  plan : SourceCoreCompatibleDataPlaceFaultSites.Plan
  root : SourceCoreCompatibleDataPlaceFaultSites.Key
  extra : List (SourceCoreCompatibleDataPlaceFaultSites.Key × TypedSource)
  diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare (.initial compiled.compatible.checked)
    plan root extra = .ok diagnostics
  collected : (owner, source) ∈ plan.specializations.map (fun specialized =>
    (specialized.key, specialized.function.typedBody)) ++ extra

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {owner : SourceSpecialization.SpecializationKey} {source : TypedSource}

/-- The ordinary support stores the genuine owning Header and exact Source. -/
theorem ordinary_typing {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep}
    {code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    EmittedDiagnosticTokenPlan.UnaryTyped function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped function.source := by
  simpa only [support.source, support.caller.agreement.source, CallableIndexedNamedGeneration.source] using SourceDiagnosticTyping.header_diagnostic_typed support.caller wellFormed

/-- The principal's independent selector authenticates its complete Source. -/
theorem principal_typing {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep}
    {code : CallableIndexedLambdaValues.Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    EmittedDiagnosticTokenPlan.UnaryTyped function.source ∧ AssignmentDiagnosticOrigins.OperandsTyped function.source := by
  simpa only [support.source] using SourceDiagnosticTypingOrigins.principal support.principal wellFormed

namespace IssuedSource
variable (issued : IssuedSource compiled owner source)

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Syntax.ValueAssignOp) : Word :=
  GenericAssignmentDiagnostics.token issued.assignments site root operator

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  issued.assignments.reasonAt site root .bitNot

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  issued.diagnostics.program.placeReason owner site root none

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (valueType : TypeSystem.Ty) : Word :=
  issued.diagnostics.program.placeReason owner site root (some valueType)

/-- The real canonical preparation closes only this described target's gate. -/
theorem concrete {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures
      source site assignment = .ok route) :
    CompatiblePlaceMissingPreparationCoverage.concrete source assignment = true :=
  CompatiblePlaceConcretePreparation.describe_concrete
    (CallableIndexedOwnedPublicCatalogClosedSources.compiled_closed compiled) described

variable {registry : SourceCoreRawMetadata.Registry}
  {extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry}
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel compiled.compatible.checked.catalog ambient} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}

include rebuilt in
/-- The reached missing witness supplies its own raw root and terminal. -/
theorem missing {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {context : SourceSemantics.Context}
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {invalid : Word} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route invalid
      (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) = .ok prepared)
    (writable : WritableLocal context assignment.target.root prepared.route.rootSourceType)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compiled.compatible.checked.signatures)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {leaf : TypeSystem.Ty} {reason : Dynamic.SemanticFault} {token : Word}
    (witness : MissingWitness compiled.compatible.checked registry functions protocol source
      (.occurrence node.id.occurrence) assignment.target prepared leaf initial reached reason token) :
    ∃ rawValue diagnostic, reason = .missingMappingDefault rawValue ∧
      table.diagnostic? token = some diagnostic ∧ diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨type, placeTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed typed
  have projections := CallableIndexedOwnedPublicPlaceReachedDiagnostics.projections_at_root placeTyped writable
  obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have preparedRoute := (CompatibleMixedPreparation.of_prepare generated).1
  have sourceTyped : ∀ actualBinder, rootBinder source assignment.target.root = .ok actualBinder →
      SourceProjectionsHaveType source context actualBinder.scheme.body assignment.target.projections assignment.target.type := by
    intro actualBinder binding
    have binders := Except.ok.inj (binding.symm.trans description.binding)
    subst actualBinder
    simpa only [preparedRoute, description.rootSource] using projections
  obtain ⟨phaseIndex, phase, location, locationNative, cell, optional, root, value, path,
    _relatedIn, _relatedOut, _scope, _canonical, _index, _worlds, _frame, _read, rootType, terminal⟩ := witness.terminal
  have rootView : SourceCoreRawMetadata.runtimeType cell.type =
      SourceCoreRawMetadata.runtimeType route.rootSourceType :=
    congrArg SourceCoreRawMetadata.runtimeType (rootType.trans (congrArg Route.rootSourceType preparedRoute))
  exact CompatiblePlaceMissingTerminalDiagnostics.terminal_diagnostic issued.prepared issued.collected
    statement target (concrete described) described generated unique signatures sourceTyped rootView rebuilt terminal

include rebuilt in
/-- An uninitialized projected root retains its actual location and witness.
The fixed diagnostic belongs to the same accepted description. -/
theorem uninitialized {node : StatementNode} (statement : .statement node ∈ source.nodes)
    {assignment : AssignmentResolution}
    (target : assignment ∈ CompatiblePlaceMissingPreparationCoverage.targets node)
    {route : Route}
    (described : describe (.initial compiled.compatible.checked) compiled.compatible.checked.signatures source
      (.occurrence node.id.occurrence) assignment = .ok route)
    {fuel : Nat} {prepared : Prepared}
    (generated : prepare (.initial compiled.compatible.checked) fuel route
      (issued.invalidProjection (.occurrence node.id.occurrence) assignment.target.root)
      (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) = .ok prepared)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
    {environment : Dynamic.Environment} {location : Dynamic.Location}
    (witness : UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location) :
    UninitializedWitness compiled.compatible.checked registry functions protocol environment
      assignment.target prepared initial reached location ∧
    ∃ diagnostic, table.diagnostic? prepared.invalidProjection = some diagnostic ∧ diagnostic.error = .invalidPlaceProjection := by
  have actual := CompatibleMixedPreparation.of_prepare generated
  have projected : prepared.steps ≠ [] := by
    obtain ⟨_phaseIndex, _phase, _target, _cell, _optional, _sources, _resolved,
      _in, _out, _scope, _canonical, _index, _world, _frame, _lookup, _read,
      _reference, _storeRead, _cellRep, _cellType, _empty, _notMapping, nonempty, _values, _resolvedNonempty⟩ := witness
    exact nonempty
  have nonempty : route.steps ≠ [] := by
    intro empty
    have steps := actual.2.2
    rw [empty] at steps
    have only_nil : ∀ {outputs keys}, CompatibleMixedPreparation.Steps compiled.compatible.checked fuel
        (issued.missingDefault (.occurrence node.id.occurrence) assignment.target.root) [] 0 outputs keys → outputs = [] := by
      intro outputs keys path
      cases path
      rfl
    exact projected (only_nil steps)
  obtain ⟨entry, member, kind, _first, reason⟩ :=
    CompatiblePlaceProjectionDiagnosticCoverage.prepare_coverage issued.prepared issued.collected
      statement target (concrete described) described nonempty
  obtain ⟨decoded, error⟩ := CompatiblePlaceProjectionDiagnosticPreparation.table_diagnostic
    issued.prepared member kind rebuilt
  have same : prepared.invalidProjection = entry.reason := actual.2.1.trans reason
  exact ⟨witness, entry.diagnostic, by simpa only [same] using decoded, error⟩

include rebuilt in
/-- The interpretation is used after the same head's real table observation. -/
theorem shape_errors {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      certificate scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) {faults : FunctionCalls.FaultRep}
    (projected : assignment.target.projections ≠ []) {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs) {fuel : Nat}
    (retained : head.PreparedAt site fuel (issued.invalidProjection site assignment.target.root)
      (issued.missingDefault site assignment.target.root))
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compiled.compatible.checked.signatures)
    (interprets : CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions protocol environment assignment.target head.prepared initial table faults) :
    ShapeErrors (.initial compiled.compatible.checked) registry functions protocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape := by
  obtain ⟨node, statement, sameSite, target⟩ := CallableIndexedOwnedPublicPreparedShapeDiagnostics.owning_target origin
  subst site
  cases retained with
  | bare empty => exact False.elim (projected empty)
  | projected route layout ordinary shape described preparedBy =>
    rw [shape]
    apply ShapeErrors.projected (layout := layout) (ordinary := ordinary)
    · intro reachedIndex reason token reached related witness
      obtain ⟨rawValue, diagnostic, sameReason, decoded, error⟩ :=
        issued.missing rebuilt statement target typed described preparedBy head.writable unique signatures witness
      rw [sameReason]
      exact interprets.missing decoded error
    · intro reachedIndex location reached related witness
      obtain ⟨actualWitness, diagnostic, decoded, error⟩ :=
        issued.uninitialized rebuilt statement target described preparedBy witness
      exact interprets.uninitialized reached related actualWitness decoded error

end IssuedSource
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
/-! The actual contextual body recipe and one view extraction supply the same
canonical flow and its prepared structural payload. Source syntax and static
child/compiler evidence remain independent genuine receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability CallableLambdaViewStaticTyping
open GenericImperativeMatch

/-- This constructible static factory retains owning occurrences. Its legacy
error package remains residual and is unused by the prepared structural route. -/
def trackedFactory (diagnosticPolicy : AssignmentDiagnosticPolicy) (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word) :
    AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand :=
  ⟨fun head registry faults => head.ErrorsFor diagnosticPolicy registry faults,
   fun _ _ _ _ _ _ given => given⟩

section Transport
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {administrative : Core.Context}
  {beforeSyntax afterSyntax : ExpressionId → Prop}
  {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (syntaxTransport : ∀ id, Reaches source roots (.expression id) → beforeSyntax id → afterSyntax id)
  (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
    before context scope id lowered → after context scope id lowered)
  {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {targetFactory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy view invalidOperand}
include edited avoids unique expressions

/-- The mapped post tree and its plan are chosen together by the shared core. -/
theorem header_prepared {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {type : Ty} {code : Expr}
    {tree : GenericForHeader.Tree layouts owner active frame globals onError values source before definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code}
    (receipt : Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code,
      Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree := by
  obtain ⟨plan, coupled, tokens⟩ := receipt
  exact CallableLambdaViewMatchRuntimeCertificates.header_payload_with edited avoids expressions
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
    (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
    (fun tree => CallableLambdaViewPreparedStaticTransport.Header.PreparedPacket (factory := targetFactory)
      (invalidProjection := invalidProjection) (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    CallableLambdaViewPreparedStaticTransport.Header.prepared_algebra
    (fun head reached receipt => CallableLambdaViewMatchRuntimeCertificates.assignment_payload edited avoids
      expressions unique receipt reached)
    (fun head receipt => CallableLambdaViewMatchRuntimeCertificates.unary_payload edited receipt)
    (GenericForHeader.Structural.of_coupled coupled tokens) reached

include syntaxTransport in
/-- One actual position extraction crosses the view with its chosen heads and
post trees. The target structural receipt uses that same canonical tree. -/
theorem transport_prepared {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (receipt : Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := beforeSyntax) (certificates := before) (definitions := definitions) (administrative := administrative)
      (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context)
      context scope (.statements mode statements) expected type code)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    ∃ _tree : Tree layouts owner active frame globals onError values view afterSyntax after definitions administrative
      context scope (.statements mode statements) expected type code,
      Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
        (globals := globals) (onError := onError) (values := values) (source := view)
        (expressionSyntax := afterSyntax) (certificates := after) (definitions := definitions) (administrative := administrative)
        (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
        (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
        (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
          (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
        (fun compilation context => Tree.MatchContextFields compilation context)
        context scope (.statements mode statements) expected type code := by
  exact CallableLambdaViewMatchRuntimeCertificates.transport_payload_with edited avoids unique syntaxTransport expressions
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
    (fun tree => Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
    (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    (fun {context scope position expected type code} tree => Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := view)
      (expressionSyntax := afterSyntax) (certificates := after) (definitions := definitions) (administrative := administrative)
      (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context)
      context scope position expected type code)
    (CallableLambdaViewPreparedStaticTransport.Match.structural_algebra
      (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context))
    (fun head reached receipt => CallableLambdaViewMatchRuntimeCertificates.assignment_payload edited avoids
      expressions unique receipt reached)
    (fun head receipt => CallableLambdaViewMatchRuntimeCertificates.unary_payload edited receipt)
    (fun _ receipt reached => header_prepared edited avoids unique expressions receipt reached)
    (fun _ _ receipt => receipt) receipt reached

end Transport
section Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Static policy and child evidence is for the actual supplied body lowerer.
The residual factory contains no required legacy error interpretation. -/
structure ExtractionInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
    source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
    ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

/-- The original collector runs once at the actual accepted view flow. -/
theorem ExtractionInputs.extract {residualMode : Bool} {policy : SourceCoreLoops.Policy}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (inputs : ExtractionInputs (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (reasonAt := reasonAt)
      (definitions := definitions) (administrative := administrative) (invalidOperand := invalidOperand)
      (invalidUnary := invalidUnary) (invalidProjection := invalidProjection) (missingDefault := missingDefault)
      residualMode policy context scope)
    (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {position : Position} {expected : TypeSystem.Ty} {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor true policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
      (trackedFactory diagnosticPolicy source invalidOperand) invalidUnary invalidProjection missingDefault expressionSyntax certificates
      definitions administrative inputs.matchCompilation.solvedRequirements context scope position expected type code) := by
  exact extraction_of_typed_position_with_catalog_coupled residualMode diagnosticPolicy
    (trackedFactory diagnosticPolicy source invalidOperand) inputs.matchPolicy inputs.matchValues inputs.matchDefinitions
    inputs.matchAllocator inputs.matchChildStatic inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy
    inputs.expressions inputs.assignments inputs.unaries unique inputs.assignmentExpressions syntaxTree
    inputs.closed inputs.residual inputs.sourceSignatures inputs.declarations projection accepted nativeTyped

end Extraction

section Site
open CallableIndexedLambdaValues
open CallableIndexedLambdaGeneration
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

/-- The body recipe is the literal equation retained by the contextual producer. -/
def BodyRecipe {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : Prop :=
  code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements namedCompilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.locals named.signature.key [])

/-- This is the actual recipe's policy applied to its own recursive children. -/
def bodyPolicy {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : SourceCoreLoops.Policy :=
  let representation := (CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key []
  {representation.loopsWithSourceCells representation.expressions.sourceCells
    (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements namedCompilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed named).owner
    (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) with
    sourceCells := representation.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation compiled.indexed.base.locals named.signature.key []}

theorem callback_of_recipe {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative} (recipe : BodyRecipe namedCompilation code) :
    code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy (bodyPolicy namedCompilation code) := by
  dsimp only [bodyPolicy]
  rw [recipe]
  rfl

/-- This receipt has the actual view extraction and the canonical prepared
eliminator at the same flow. It contains no body execution callback. -/
structure JointBody {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    extends CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates where
  recipe : BodyRecipe namedCompilation code
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (bodyPolicy namedCompilation code) code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  actual : CatalogCoupledExtractionFor diagnosticPolicy compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) code.view (trackedFactory diagnosticPolicy code.view invalidOperand)
    invalidUnary invalidProjection missingDefault (expressionSyntax code.view) (certificates readFuel code.view)
    compiled.indexed.layouts.definitions administrative context.solvedRequirements context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  prepared : Structural.Eliminates (layouts := compiled.indexed.layouts) (owner := code.compilation.owner)
    (active := code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (onError := code.allocationError) (values := .initial compiled.compatible.checked) (source := function.source)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates readFuel function.source)
    (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
    (fun head => GenericForHeader.Structural.PreparedAssignment (trackedFactory diagnosticPolicy function.source invalidOperand)
      invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true function.source invalidUnary head)
    (fun postTree => Structural.PreparedHeader (factory := trackedFactory diagnosticPolicy function.source invalidOperand)
      (invalidProjection := invalidProjection) (missingDefault := missingDefault) (invalidUnary := invalidUnary) postTree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow

/-- The authentic chosen Site supplies its body recipe. The existing collector
runs at that accepted view, and the shared transport returns its canonical flow. -/
theorem at_site {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {captured : Dynamic.Environment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site compiled.indexed named parameters result statements sourceContext evidence captured scope administrative)
    (recipe : BodyRecipe namedCompilation site.code)
    (program : Program) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code)
    (frame : Dynamic.ClosureFrame program (CallableIndexedLambdaGeneration.closure named parameters result statements sourceContext evidence captured))
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (readFuel : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {changed : List ExpressionId}
    (edited : LocalView (CallableIndexedNamedGeneration.source named) site.code.view changed)
    (avoids : Avoids (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
    (sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements)
    (syntaxTransport : ∀ id, Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      expressionSyntax site.code.view id → expressionSyntax (CallableIndexedNamedGeneration.source named) id)
    (expressions : ∀ context scope id lowered,
      Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      certificates readFuel site.code.view context scope id lowered →
      certificates readFuel (CallableIndexedNamedGeneration.source named) context scope id lowered)
    (syntaxTree : Syntax (CallableIndexedNamedGeneration.source named)
      (expressionSyntax (CallableIndexedNamedGeneration.source named)) inputs.context (.statements true statements) result)
    (viewSyntax : Syntax site.code.view (expressionSyntax site.code.view) inputs.context (.statements true statements) result)
    (projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore)
    {residualMode : Bool}
    (static : ExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (onError := site.code.allocationError) (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view) (certificates := certificates readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := invalidOperand) (invalidUnary := invalidUnary) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) residualMode (bodyPolicy namedCompilation site.code) inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope))
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ∃ body : JointBody namedCompilation site.code program expressionSyntax certificates diagnosticPolicy
        invalidOperand invalidUnary invalidProjection missingDefault,
      body.toBody.toContext = inputs ∧ body.readFuel = readFuel := by
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked) site.code (bodyPolicy namedCompilation site.code)
    (callback_of_recipe namedCompilation recipe)
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : site.code.receipt.body = CompatibleStatements.finish site.code.receipt.resultCore flow
      site.code.compilation.internalReason site.code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨nativeFlowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow (emitted ▸ nativeTyped)
  obtain ⟨actual⟩ := static.extract diagnosticPolicy (edited.metadata.unique unique) viewSyntax projection generated flowTyped
  have reverse : LocalView site.code.view (CallableIndexedNamedGeneration.source named) changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  obtain ⟨canonical, prepared⟩ := transport_prepared reverse (avoids.view edited.metadata)
    (edited.metadata.unique unique)
    (fun id reached receipt => syntaxTransport id (reached.metadata edited.metadata.symm) receipt)
    (fun context scope id lowered reached receipt => expressions context scope id lowered
      (reached.metadata edited.metadata.symm) receipt)
    (targetFactory := trackedFactory diagnosticPolicy (CallableIndexedNamedGeneration.source named) invalidOperand)
    (actual.eliminate static.ledger) (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have actualLedger : static.matchCompilation.solvedRequirements = inputs.context.solvedRequirements := static.ledger.symm
  exact ⟨{
    toBody := {
      toContext := inputs, frame := frame, readFuel := readFuel, flow := flow,
      projection := projection, emitted := emitted, tree := canonical,
      valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) site.code inputs frame sameLedger,
      unique := unique, syntaxTree := syntaxTree },
    recipe := recipe, generated := generated,
    actual := actualLedger ▸ actual,
    prepared := prepared }, rfl, rfl⟩

end Site

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
/-! The selected lambda assignment packet supplies its actual owning Source
occurrence and compiler preparation. Only precise reached table interpretation
and strict expression children are requested at the current admitted state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {owner : SourceSpecialization.SpecializationKey} {source : TypedSource}
  (issued : IssuedSource compiled owner source)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source issued.invalidOperand}

/-- The interpretation concerns one actual projected packet at its real input. -/
def ReachedInterpretations (table : SourceCoreFaultSites.Table) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {environment : Dynamic.Environment} {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index), Admission bridge context initial →
    GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head →
    assignment.target.projections ≠ [] →
    CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
      compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults

private theorem operand_law {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) source context
      (certificates context) scope administrative ambient.definitions assignment operator rhs)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (same : head.invalid = issued.invalidOperand site assignment.target.root operator)
    (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid := by
  exact same.symm ▸ origin.prepared issued.typing.2 issued.assignmentsPrepared included

variable {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : ReachedInterpretations issued bridge functions table)
  (included : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (signatures : context.signatures = compiled.compatible.checked.signatures)

include extension transport faithful observations unique wellFormed issued rebuilt interprets included signatures in
theorem assignment_fault (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        source (certificates context) faults size)) :
    AssignmentFaultPreservesWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload reason after size trace bounded next output
  have payload' := payload
  cases payload with
  | intro site origin same sourceTyped rightTyped profile fuel prepared =>
    by_cases bare : assignment.target.projections = []
    · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.preserves_fault_with_operands
        (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence observations head bare environments heaps locals agrees actualTyped initial admitted unique typed
        budget meaning (operand_law issued head origin same included) trace bounded next output
    · exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.preserves_fault_with_diagnostics
        (values := .initial compiled.compatible.checked) (ambient := ambient)
        bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped
        initial admitted unique typed wellFormed runtime covers budget meaning
        (issued.shape_errors rebuilt head initial bare origin prepared typed unique signatures
          (interprets head initial admitted payload' bare)) trace bounded next output

include extension transport faithful observations unique wellFormed issued rebuilt interprets included signatures in
theorem assignment_reflection (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence
        source (certificates context) faults size)) :
    AssignmentReflectsWithPayloadAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (ambient := ambient) functions (registry := registry)
      (Program.ofChecked compiled.sourceProgram) evidence source (certificates context) context administrative faults budget
      (fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head) := by
  intro scope assignment operator rhs head typed mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted payload next output value finalStore size evaluated bounded
  have payload' := payload
  have result : CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions
      context evidence source faults scope (head.writtenContext actualContext) assignment operator rhs
      environment canonical actual before store mapping world initial (next.rename ξ) output value finalStore := by
    cases payload with
    | intro site origin same sourceTyped rightTyped profile fuel prepared =>
      by_cases bare : assignment.target.projections = []
      · exact CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads.reflects_with_operands
          (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted
          unique typed wellFormed runtime covers budget meaning (operand_law issued head origin same included) evaluated bounded
      · exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.reflects_with_diagnostics
          (values := .initial compiled.compatible.checked) (ambient := ambient)
          bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped
          initial admitted unique typed wellFormed runtime covers budget meaning functionTypes
          (issued.shape_errors rebuilt head initial bare origin prepared typed unique signatures
            (interprets head initial admitted payload' bare)) evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
/-! Genuine Source sites and the actual prepared eliminator supply all finite
head and loop operations internally. The only runtime children are strict
members of the same admitted expression family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {owner : SourceSpecialization.SpecializationKey}
  (issued : IssuedSource compiled owner source)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source issued.invalidOperand}
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)

/-- The lambda's complete ledger travels with independent Source validity. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid solved context evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source

theorem validity_extend {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : Validity (compiled := compiled) (source := source) (solved := solved) evidence context)
    (extended : BinderExtends source.owner context binder next) :
    Validity (compiled := compiled) (source := source) (solved := solved) evidence next :=
  ⟨valid.1.extend extended, valid.2.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩

theorem signatures {context : SourceSemantics.Context}
    (valid : Validity (compiled := compiled) (source := source) (solved := solved) evidence context) :
    context.signatures = compiled.compatible.checked.signatures :=
  valid.2.signatures.trans (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm

include unique in
private theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (SourceAssignmentHasType source) (SourceBitNotAssignmentValid source) source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form


variable (interprets : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
  CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
    (context := context) (certificates := certificates) (administrative := administrative)
    (factory := factory) (faults := faults) (registry := registry) issued bridge functions table)

include definitions registered extension faithful observations producer acquire transport bindings wellFormed unique rebuilt operandIncluded unaryIncluded interprets in
theorem preserves_flow (budget : Nat) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (meaning : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedHeaderContracts.AtMost budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size))
    (eliminator : GenericImperativeMatch.Structural.Eliminates
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) context scope position expected type flow) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
      functions (Program.ofChecked compiled.sourceProgram) evidence (Validity (compiled := compiled) (source := source) (solved := solved) evidence) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      context scope position expected type flow := by
  have below : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size) :=
    fun context valid child smaller => meaning context valid child (Nat.le_of_lt smaller)
  let assignments : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt protocol (readiness bridge)
        (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (ambient := ambient) functions (registry := registry) (Program.ofChecked compiled.sourceProgram)
        evidence source (certificates context) context administrative faults budget ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) := by
    intro context valid
    exact CallableIndexedOwnedContextualLambdaAssignmentReadiness.assignment_fault
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (registry := registry) (faults := faults)
      issued bridge functions extension evidence transport faithful observations unique wellFormed
      rebuilt (interprets context valid) operandIncluded (signatures evidence valid)
      valid.2 valid.1.covers budget (below context valid)
  exact RecursiveNamedImperativeFor.Stateful.WithReady.preservesAt_match_with_eliminator
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
    (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
    (administrative := administrative) (functions := functions)
    (definitions := definitions) (registered := registered) (program := Program.ofChecked compiled.sourceProgram)
    (evidence := evidence) (protocol := protocol) (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
    (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := (Validity (compiled := compiled) (source := source) (solved := solved) evidence)) (extend := fun valid extended => validity_extend evidence valid extended)
    (budget := budget)
    (sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram) evidence runtime.graph)
    (assignmentSites := assignment_sites unique)
    (initializerSites := ProtectedStateImperativeInitializerSourceSites.sites)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed (Validity (compiled := compiled) (source := source) (solved := solved) evidence)
      (fun _ valid => valid.2) (fun _ valid => valid.1.covers))

    (assignments := fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (certificate := certificates context) (administrative := administrative) (faults := faults)
      bridge functions extension evidence transport faithful observations unique wellFormed
      valid.2 valid.1.covers budget (below context valid))
    (meaningMost := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning context valid child within))
    ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head))) (ProtectedStateImperativeCatalogPayload.structural_header_algebra ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
    (fun {context scope assignment} {head} receipt => GenericForHeader.Structural.PreparedUnary.errors receipt issued.typing.1 issued.assignmentsPrepared unaryIncluded)
    (fun _ _ fields => ⟨CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed, fields⟩)
    assignments unique
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence faithful observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy (fun _ valid => valid.1) issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence faithful observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    eliminator

include definitions registered extension faithful observations producer acquire transport bindings wellFormed unique rebuilt operandIncluded unaryIncluded interprets in
theorem reflects_flow (budget : Nat) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (functionTypes : FunctionRuntimeViews functions)
    (meaning : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size))
    (eliminator : GenericImperativeMatch.Structural.Eliminates
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) context scope position expected type flow) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
      functions (Program.ofChecked compiled.sourceProgram) evidence (Validity (compiled := compiled) (source := source) (solved := solved) evidence) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      context scope position expected type flow := by
  have below := meaning
  let assignments : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt protocol (readiness bridge)
        (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (ambient := ambient) functions (registry := registry) (Program.ofChecked compiled.sourceProgram)
        evidence source (certificates context) context administrative faults budget ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) := by
    intro context valid
    exact CallableIndexedOwnedContextualLambdaAssignmentReadiness.assignment_reflection
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (registry := registry) (faults := faults)
      issued bridge functions extension evidence transport faithful observations unique wellFormed
      rebuilt (interprets context valid) operandIncluded (signatures evidence valid)
      valid.2 valid.1.covers budget functionTypes (below context valid)
  exact RecursiveNamedImperativeFor.Stateful.WithReady.reflectsAt_match_with_eliminator
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
    (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
    (administrative := administrative) (functions := functions)
    (definitions := definitions) (registered := registered) (program := Program.ofChecked compiled.sourceProgram)
    (evidence := evidence) (protocol := protocol) (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
    (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := (Validity (compiled := compiled) (source := source) (solved := solved) evidence)) (extend := fun valid extended => validity_extend evidence valid extended)
    (budget := budget)
    (sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram) evidence runtime.graph)
    (assignmentSites := assignment_sites unique)
    (initializerSites := ProtectedStateImperativeInitializerSourceSites.sites)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed (Validity (compiled := compiled) (source := source) (solved := solved) evidence)
      (fun _ valid => valid.2) (fun _ valid => valid.1.covers))

    (reflection := fun context valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning context valid child smaller))
    ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head))) (ProtectedStateImperativeCatalogPayload.structural_header_algebra ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
    (fun {context scope assignment} {head} receipt => GenericForHeader.Structural.PreparedUnary.errors receipt issued.typing.1 issued.assignmentsPrepared unaryIncluded)
    (fun _ _ fields => ⟨CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed, fields⟩)
    assignments unique
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy (fun _ valid => valid.1) issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered evidence condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    eliminator

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
/-! The actual joint body and owning Source issuance produce strict flow
members internally. Typed finish consumes them at the genuine parameter
entries, preserving the original reached exit and caller restoration. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody trackedFactory)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (issued : IssuedSource compiled code.compilation.owner function.source)
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := certificates body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
      (faults := faults) (registry := registry) issued (bridge (headers := headers) (keys := keys)) functions table)

private def producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
    compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (keys := keys) (registry := registry) functions).toOrdinary location native := by
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
    (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- All head and loop recipes come from this same prepared body. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured code body.toBody functions (registry := registry) (faults := faults)
        (headers := headers) (keys := keys)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.preserves_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (bridge (headers := headers) (keys := keys)) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer (headers := headers) (keys := keys) (registry := registry) functions)
    (acquire (headers := headers) (keys := keys) (registry := registry) functions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 meaning body.prepared

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Native children keep their strict grades; the Source grade remains independent. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    Below budget (FlowReflects captured code body.toBody functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys)) := by
  exact CallableIndexedOwnedContextualLambdaPreparedFlowBounds.reflects_flow
    (active := code.active) (onError := code.allocationError)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates body.readFuel function.source)
    (administrative := captured.administrative) (registry := registry) (faults := faults)
    (factory := trackedFactory diagnosticPolicy function.source issued.invalidOperand)
    issued (bridge (headers := headers) (keys := keys)) functions rfl
    (CallableIndexedAmbient.frame_registered compiled.indexed) extension function.evidence faithful observations
    (CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (producer (headers := headers) (keys := keys) (registry := registry) functions)
    (acquire (headers := headers) (keys := keys) (registry := registry) functions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    body.unique wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters body.frame body.extended).1 functionTypes reflection body.prepared

variable (history : History code) (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The strict expression family yields the local flow family and typed Source
finish at the actual parameter entry; no completed body premise is supplied. -/
theorem source_continuation (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.SourceContinuation
      (registry := registry) (faults := faults) (arguments := arguments) (nativeArguments := nativeArguments)
      captured code history body.toBody.toContext functions owner caller budget := by
  apply CallableIndexedOwnedTypedLambdaBodyContinuations.source_continuation
    captured code history body.toBody functions owner caller beforeTyped argumentsTyped stable wellFormed budget
  intro child strict
  exact preserves_flow namedCompilation captured code issued body functions extension faithful observations wellFormed
    rebuilt operandIncluded unaryIncluded interprets child
    (fun context valid size within => meaning context valid size (Nat.lt_of_le_of_lt within strict)) child (Nat.le_refl child)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets beforeTyped argumentsTyped stable in
/-- The native flow and typed finish are derived from the same strict family. -/
theorem native_continuation (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (certificates body.readFuel function.source context) faults size)) :
    CallableIndexedOwnedLambdaEntryBodyContracts.NativeContinuation
      (registry := registry) (faults := faults) (arguments := arguments)
      captured code history body.toBody.toContext functions owner caller budget := by
  exact CallableIndexedOwnedTypedLambdaBodyContinuations.native_continuation
    captured code history body.toBody functions owner caller beforeTyped argumentsTyped stable wellFormed budget
    (reflects_flow namedCompilation captured code issued body functions extension faithful observations wellFormed
      rebuilt operandIncluded unaryIncluded interprets budget functionTypes reflection)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
/-! The actual contextual Site supplies its selected binder projection row.
The complete same-Code Source projection also determines its parameter and
result projections. Concrete ordinary and principal associations retain all
capture, history and Source-origin fields at this same Site. Raw Source bundle
equality, genuine arity and call-site stage facts remain separate receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaGeneration
open CallableIndexedOwnedStoredNativePackReceipts

/-- A complete genuine Source function projection retains both native
endpoints. This finite inversion recovers no Source facts from native values. -/
theorem Code.source_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative)
    (profile : checked.catalog.callableContracts = true) :
    checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) =
      .ok code.receipt.parameterCore ∧
    checked.catalog.project function.resultType = .ok code.receipt.resultCore := by
  have projected := code.projection
  change (do pure (checked.catalog.functionType
    (← checked.catalog.project (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))))
    (← checked.catalog.project function.resultType))) = _ at projected
  cases parameterEq : checked.catalog.project
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder : TypedBinder => binder.scheme.body))) with
  | error error =>
    simp only [parameterEq, bind, Except.bind] at projected
    cases projected
  | ok parameter =>
    cases resultEq : checked.catalog.project function.resultType with
    | error error =>
      simp only [parameterEq, resultEq, bind, Except.bind] at projected
      cases projected
    | ok result =>
      simp only [parameterEq, resultEq, bind, Except.bind, pure, Except.pure,
        SourceCoreCompatibleCatalog.Catalog.functionType, profile, ↓reduceIte, Except.ok.injEq] at projected
      obtain ⟨parameterSame, resultSame⟩ := callable_parameters projected
      cases parameterSame
      cases resultSame
      exact ⟨rfl, rfl⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The actual producer's retained binder policy and genuine Source extension
close the packed binder type for this same returned Site. -/
theorem Site.binding_pack
    (site : Site compiled.indexed named parameters result statements sourceContext evidence environment scope administrative)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.locals named.signature.key [])
    {types : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    (extended : MonoBindersExtend (CallableIndexedNamedGeneration.source named).owner
      sourceContext parameters types bodyContext) :
    site.code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) :=
  code_binding_pack site.code profile
    (CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy extended)
    (Code.source_projections site.code profile).2

section Compiler
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (site : Site compiled.indexed named parameters result statements sourceContext evidence environment
    scope captured.administrative)
  (history : History site.code)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (binderPolicy : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key [])
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {callerScope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {rawType : TypeSystem.Ty}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : ValueRep compiled.compatible.checked registry functions mapping world rawType
    (.closure (closure named parameters result statements sourceContext evidence environment))
    (value site.code captured.embedding history.native actual) receipt.calleeCode.type)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (referenceIndex : site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (typed : RuntimeValueHasType world (value site.code captured.embedding history.native actual)
    (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore)
    compiled.indexed.layouts.definitions)
  (escaped : faults .controlEscapedFunction site.code.compilation.internalReason)

include profile binderPolicy actualFunctionType represented owner observed referenceIndex typed escaped

/-- The ordinary association is constructed from the exact Site Code and its
complete actual Source origin, so its selected row is the producer's row. -/
theorem compiler_binding_pack_of_ordinary_site
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support site.code registry faults)
    (sourceOrigin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial compiled.compatible.checked) support.caller)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
      (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
      (.statements true statements) result) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) := by
  have association : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext evidence environment)
      (value site.code captured.embedding history.native actual) site.code.receipt.loweredParameters
      site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.ordinary
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext evidence environment)
      (scope := scope) (actual := actual)
      owner captured site.code history support sourceOrigin prefixContext observed referenceIndex typed escaped syntaxTree
  exact (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (Site.binding_pack site profile binderPolicy support.body.extended)

/-- The principal association keeps its authentic leading bundle and full
Source origin beside this same actual Site and selected binder row. -/
theorem compiler_binding_pack_of_principal_site
    (support : CallableIndexedOwnedMethodLambdaSupport.Support site.code registry faults)
    (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
    (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
    (syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source named)
      (support.expressionSyntax (CallableIndexedNamedGeneration.source named)) support.body.context
      (.statements true statements) result) :
    SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (site.code.receipt.loweredParameters.map Prod.snd) := by
  have association : CallableIndexedOwnedStoredClosureInvocation.Association headers keys registry faults mapping world
      (closure named parameters result statements sourceContext evidence environment)
      (value site.code captured.embedding history.native actual) site.code.receipt.loweredParameters
      site.code.receipt.parameterCore site.code.receipt.resultCore :=
    CallableIndexedOwnedStoredClosureInvocation.Association.principal
      (headers := headers) (registry := registry) (faults := faults) (mapping := mapping) (world := world)
      (function := closure named parameters result statements sourceContext evidence environment)
      (scope := scope) (actual := actual)
      owner captured site.code history support sourceOrigin observed leading referenceIndex typed escaped syntaxTree
  exact (compiler_parameter_pack receipt actualFunctionType association represented).trans
    (Site.binding_pack site profile binderPolicy support.body.extended)

end Compiler
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
/-! Contextual receipts keep the exact selected Code and independent body
Syntax. These static projections construct a typed finish receipt in a proof
goal and retain the original ordered binder projections. No execution or
classification of legacy function alternatives is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}

/-- The explicit same-Code support supplies all data; only its independent
Syntax proof is obtained from the retained contextual packet. -/
theorem ordinary_typed_body
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support) :
    ∃ body : CallableIndexedOwnedTypedLambdaStaticBody.Body code
        (Program.ofChecked compiled.sourceProgram) support.expressionSyntax support.certificates,
      body.toContext = support.body.toContext ∧ body.readFuel = support.body.readFuel ∧
      body.flow = support.body.flow ∧ HEq body.tree support.body.tree := by
  exact ⟨CallableIndexedOwnedTypedLambdaStaticBody.Body.of_body_with
    support.body provenance.syntax, rfl, rfl, rfl, HEq.rfl⟩

/-- The principal keeps its own complete support and dictionary at the same
Code. No ordinary Header is introduced. -/
theorem principal_typed_body
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support) :
    ∃ body : CallableIndexedOwnedTypedLambdaStaticBody.Body code
        (Program.ofChecked compiled.sourceProgram) support.expressionSyntax support.certificates,
      body.toContext = support.body.toContext ∧ body.readFuel = support.body.readFuel ∧
      body.flow = support.body.flow ∧ HEq body.tree support.body.tree := by
  exact ⟨CallableIndexedOwnedTypedLambdaStaticBody.Body.of_body_with
    support.body provenance.syntax, rfl, rfl, rfl, HEq.rfl⟩

/-- Genuine seed metadata and the actual producer's binder equation fix the
same ordered binder projection row after recapture. -/
theorem ordinary_projected_bindings
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases provenance with
  | recaptured caller site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView bodyReasons declarations syntaxTree environment _globals _callerReceipt =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings
      site binderPolicy body.extended

/-- The principal binder row belongs to its actual Source context and seed. -/
theorem principal_projected_bindings
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases provenance with
  | recaptured principal site expressionSyntax certificates body binderPolicy recipe compilerPolicy issuedRecipe bodyView syntaxTree environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings
      site binderPolicy body.extended

/-- Native packing is determined by the genuine binder and result
projections. Raw Source argument counts remain independent. -/
theorem ordinary_binding_pack
    {support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults}
    (provenance : OrdinaryAt code support)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :=
  CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
    (ordinary_projected_bindings provenance) support.body.projection

/-- The same principal Code determines its native binder pack. -/
theorem principal_binding_pack
    {support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults}
    (provenance : PrincipalAt code support)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    code.receipt.parameterCore =
      SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :=
  CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
    (principal_projected_bindings provenance) support.body.projection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedLambdaReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
/-! Retained contextual static receipts provide genuine owner, Code, captures,
history and Syntax independently of an escaped-control diagnostic. Their typed
invocations use the original SourceReceipt/no-escape finish core and actual
saved-frame restoration. StaticMember is the Prop-facing witness factor for
the existing positive-cell backend; no General representation is inverted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt PrincipalAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The exact ordinary/principal static receipt is retained before erasure.
Its real factory fields determine the typed body; no diagnostic row is added. -/
inductive Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code registry faults) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : OrdinaryAt code support) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : PrincipalAt code support) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Forward selection keeps the genuine contextual branch and all its fields. -/
theorem Association.selection
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact .contextual_ordinary_lambda owner captured code history support origin prefixContext globals referenceIndex typed provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact .contextual_principal_lambda owner captured code history support origin globals leading referenceIndex typed provenance

/-- Only forward projection to the exact general relation is needed. -/
theorem Association.represents
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

/-- Actual map/world growth changes only capture and runtime typing indices.
The original code, owner, history and same-body syntax stay the same. -/
def Association.extend
    (member : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact .principal owner (captured.extend maps worlds) code history support origin globals leading
      referenceIndex (typed.weaken worlds) provenance

/-- Model leaves retain a real typed association under Prop, without exposing
an operational Code getter or recovering authority from representation. -/
abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameterCore resultCore)

theorem StaticMember.selection
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  obtain ⟨association⟩ := member
  exact association.selection

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

/-- The original Source support authenticates the actual native carrier.
No escaped-control row is used by this static stage observation. -/
theorem Association.stage_origin
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases association with
  | ordinary _owner captured code history support _origin _prefix _globals _reference _typed _provenance =>
    exact CallableIndexedOwnedOrdinaryLambdaSupport.Support.stage_origin captured code support history
  | principal _owner captured code history support _origin _globals _leading _reference _typed _provenance =>
    exact CallableIndexedOwnedMethodLambdaSupport.Support.stage_origin captured code support history

theorem StaticMember.stage_origin
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  obtain ⟨association⟩ := member
  exact association.stage_origin

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. The member is
the formed closure over the copies of its captured cells. -/
theorem formation_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.formation captured code support owner initial packet
      profile prefixContext observed provenance functions inclusion heaps copied ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨formed, sourceTrace, nativeTrace, related, determined,
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

end Formation

section PrincipalFormation
variable {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)

include packet profile provenance inclusion in
/-- One original contextual principal formation retains its genuine leading
bundle, owner and history with the exact static member. No escaped-control
diagnostic is required. The member is the formed closure over the copies of its
captured cells. -/
theorem principal_formation_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.formation captured code support owner initial packet
      profile functions inclusion provenance heaps copied ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld
      (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
        formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace, related, determined,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
        (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

end PrincipalFormation

section Invocation
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedTypedLambdaStaticBody (Body)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

/-- The strict flow child is indexed by this receipt's real retained Code.
An old BodyOrigin child cannot be substituted for this typed flow contract. -/
def Association.FlowPreserves
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (size : Nat) : Prop :=
  match association with
  | .ordinary _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowPreserves captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size
  | .principal _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowPreserves captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size

def Association.FlowReflects
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (size : Nat) : Prop :=
  match association with
  | .ordinary _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowReflects captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size
  | .principal _ captured code _ support _ _ _ _ _ provenance =>
    CallableIndexedOwnedTypedLambdaBodyContinuations.FlowReflects captured code
      (Body.of_body_with support.body provenance.syntax) functions (registry := registry) (faults := faults)
      (headers := headers) (keys := keys) size

variable (functions : FunctionModel compiled.compatible.checked.catalog
  (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

variable {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
/-- The actual typed flow callback, parameter action and saved-frame restore
run through their original cores. The final pool comes from that transition. -/
theorem preserves_at (budget : Nat)
    (below : Below budget (association.FlowPreserves functions))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_preserves_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_preserves_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

include represented heaps beforeTyped argumentsTyped locals stable wellFormed in
theorem reflects_at (budget : Nat)
    (below : Below budget (association.FlowReflects functions))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.ResultAt (registry := registry) (faults := faults)
        functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support _origin _prefixContext globals referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_reflects_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed provenance =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨_currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    obtain ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
        frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedTypedLambdaInvocationBounds.application_reflects_bounded
        captured code history (Body.of_body_with support.body provenance.syntax) functions represented owner
        initial heaps locals reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        beforeTyped raw stable wellFormed budget below completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds, frame,
      metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Invocation
/-- The actual Code's accepted parameter compilation retains the ordered raw
Source binders. Packing or native tags do not determine this Source row. -/
theorem Association.source_binders
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases association with
  | ordinary _owner _captured code _history _support _origin _prefix _globals _reference _typed _provenance =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _owner _captured code _history _support _origin _globals _leading _reference _typed _provenance =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

/-- Runtime typing already retained by the same Association fixes only its
native carrier type. Its genuine Source binder row is a separate projection. -/
theorem Association.native_type
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference typed _provenance =>
    exact typed.type_eq
  | principal _owner _captured _code _history _support _origin _globals _leading _reference typed _provenance =>
    exact typed.type_eq

/-- Genuine contextual provenance retains the canonical projection of every
ordered binder, for both ordinary and principal static receipts. -/
theorem Association.projected_bindings
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.ordinary_projected_bindings provenance
  | principal _owner _captured _code _history _support _origin _globals _leading _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.principal_projected_bindings provenance

/-- The real binder projections and same typed body's result projection fix
this Code's packed native parameter type. No diagnostic receipt is used. -/
theorem Association.parameter_core
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases association with
  | ordinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.ordinary_binding_pack provenance profile
  | principal _owner _captured _code _history _support _origin _globals _leading _reference _typed provenance =>
    exact CallableIndexedOwnedContextualTypedLambdaReceipts.principal_binding_pack provenance profile

/-- Prop-facing projections eliminate the actual retained Association only
inside the proof; no operational Code getter or classical choice is introduced. -/
theorem StaticMember.source_binders
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.native_type
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    native.type = CallableContract.functionType parameterCore resultCore := by
  obtain ⟨association⟩ := member
  exact association.native_type

theorem StaticMember.projected_bindings
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameterCore = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
/-! Positive contextual ordinary and principal members retain the actual formed code,
owner, captured history and same-body syntax through storage-independent
map/world extension. The original accepted call's escaped-control diagnostic
belongs to this same code. Projection supplies the existing strict joint
invocation association; no representation inverse or body meaning is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedOrdinaryLambdaSupport (Support SourceOrigin)
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt PrincipalAt)
open CallableIndexedOwnedStoredClosureInvocation (Association)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- This is the actual positive contextual constructor with its generated
escaped-control row. Arbitrary prior representations supply no such member. -/
inductive Member
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Prop where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code registry faults) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : OrdinaryAt code support)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
      Member headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (origin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (provenance : PrincipalAt code support)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
      Member headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Forward selection keeps the genuine contextual branch and all its fields. -/
theorem Member.selection
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance _escaped =>
    exact .contextual_ordinary_lambda owner captured code history support origin prefixContext globals referenceIndex typed provenance
  | principal owner captured code history support origin globals leading referenceIndex typed provenance _escaped =>
    exact .contextual_principal_lambda owner captured code history support origin globals leading referenceIndex typed provenance

/-- Only forward projection to the exact general relation is needed. -/
theorem Member.represents
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) :=
  CallableIndexedOwnedGeneralFunctionSelection.represents member.selection

/-- The retained provenance supplies syntax for this exact body context.
The authentic escaped-control row remains an independent compiler receipt. -/
theorem Member.association
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    Association headers keys registry faults mapping world function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance escaped =>
    exact .ordinary owner captured code history support origin prefixContext globals referenceIndex typed escaped provenance.syntax
  | principal owner captured code history support origin globals leading referenceIndex typed provenance escaped =>
    exact .principal owner captured code history support origin globals leading referenceIndex typed escaped provenance.syntax

/-- Actual map/world growth changes only capture and runtime typing indices.
The original code, owner, history, syntax and diagnostic row stay the same. -/
theorem Member.extend
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Member headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance escaped =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) provenance escaped
  | principal owner captured code history support origin globals leading referenceIndex typed provenance escaped =>
    exact .principal owner (captured.extend maps worlds) code history support origin globals leading
      referenceIndex (typed.weaken worlds) provenance escaped

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : OrdinaryAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

include profile prefixContext observed provenance inclusion escaped in
/-- One original contextual formation retains its complete traces and
represented value, plus the same positive member for later initialized reads.
The escaped row is supplied by the actual accepted compiler selection. The
member is the formed closure over the copies of its captured cells. -/
theorem formation_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.formation captured code support owner initial packet
      profile prefixContext observed provenance functions inclusion heaps copied ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  exact ⟨formed, sourceTrace, nativeTrace, related, determined,
    .ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)
      escaped⟩

end Formation

section PrincipalFormation
variable {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (provenance : PrincipalAt code support)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)

include packet profile provenance inclusion escaped in
/-- One original contextual principal formation retains its genuine leading
bundle, owner and history with the exact positive member. The accepted code's
escaped-control diagnostic stays an independent compiler input. The member is
the formed closure over the copies of its captured cells. -/
theorem principal_formation_member
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys registry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding
          (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
          formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, related, determined⟩ :=
    CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.formation captured code support owner initial packet
      profile functions inclusion provenance heaps copied ordinary coercions
  have typed : RuntimeValueHasType formed.finalWorld
      (value code formed.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native
        formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions := functions.runtime_hasType (registry := registry) related
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code support owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace, related, determined,
    .principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin
        (CallableIndexedOwnedMethodLambdaFormationReceipts.source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)
      escaped⟩

end PrincipalFormation
/-- Legacy members project forward to the diagnostic-free static witness.
This does not reconstruct the original diagnostic from a typed member. -/
theorem Member.to_static
    (member : Member headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember
      headers keys registry faults mapping world function native bindings parameterCore resultCore := by
  cases member with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance _escaped =>
    exact ⟨.ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance _escaped =>
    exact ⟨.principal owner captured code history support origin globals leading referenceIndex typed provenance⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredClosureAssociationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
/-! The accepted original contextual producer chooses one Site and retains
its actual binder policy and production recipe. Later static body receipts are indexed by that same
Site; this packet has no execution callback. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

structure Produced (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (statements : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : Site compiled.indexed named parameters result statements context evidence [] scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binderPolicy : BinderPolicy named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code

/-- The policy proof is attached to the same already selected producer Site. -/
structure ProducedWithPolicy (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (statements : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  produced : Produced (compiled := compiled) named parameters result statements context evidence
    scope administrative id lowered
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named produced.site.code

/-- One real outer bind produces the Site and all correlated policy/body fields. -/
theorem of_contextual_with_policy
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (ProducedWithPolicy (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, issuedRecipe, _view, _reason⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact
      compiled.indexed compilation issued record sourceContext evidence [] profile viewOfSource
      sourceFound sourceForm found form owner requirements coercions ordinary read accepted typed
  let produced : Produced (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  exact ⟨{ produced := produced, policyRecipe := issuedRecipe.policy_recipe }⟩

/-- The original producer interface now retains its actual expression policy. -/
theorem of_contextual
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (Produced (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨produced⟩ := of_contextual_with_policy compilation issued record sourceContext evidence
    profile viewOfSource sourceFound sourceForm found form owner requirements coercions
    ordinary read accepted typed
  exact ⟨produced.produced⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaExactProducer
/-! The actual contextual producer retains its literal view and diagnostic
function together with the same Site and full compiler policy. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

theorem of_contextual_with_policy_recipe_exact {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered ∧
        site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
          ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key [] ∧
        site.code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
          ((representation prepared).atContext named.signature.key [])
          (context prepared named).solvedRequirements compiled.own.assignments diagnostics
          (context prepared named).owner
          (SourceCoreGeneralFunctions.contextualBinder
            ((representation prepared).atContext named.signature.key []) prepared.base.locals named.signature.key []) ∧
        CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code ∧
        site.code.view = view ∧ site.code.reasonAt = reasonAt := by
  obtain ⟨policy, lowerBody, accepted, ⟨receipt⟩, allocationProfile, manifest, expressionProfile, callables, projector, binderPolicy, bodyRecipe, policyRecipe⟩ :=
    contextual_certificate_with_policy_recipe prepared compiled record found (form.trans sourceForm) owner requirements coercions ordinary read accepted
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, sameFuel, sameView, sameReasonAt, _sourceNode, _node, _receipt⟩ :=
    of_certificate prepared sourceContext evidence captured receipt accepted profile viewOfSource
      sourceFound sourceForm found form allocationProfile manifest expressionProfile callables projector
      (by rw [policyRecipe.snapshotLambda]) typed
  have actualBody : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compiled site.code :=
    sameBody.trans bodyRecipe
  have actualPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe
      compiled site.code.fuel site.code.policy := by
    rw [sameFuel, samePolicy]
    exact policyRecipe
  exact ⟨site, identifier, emitted,
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans binderPolicy,
    sameBody.trans bodyRecipe,
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained.of_recipes
      compiled actualBody actualPolicy site.compilation, sameView, sameReasonAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
end
