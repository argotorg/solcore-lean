import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicContextualMissingDiagnosticObservations
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexFaultPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerPolicies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBodyViewEdits
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Staging.RecursiveTrace
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexTerminal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds

/-!
# Staged bounds: index expressions

Index heads and outcomes, the authority and producers of index diagnostics, and the general body view's syntax and read policy.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
/-! Exact index diagnostic ownership is static. The receiving table and its
raw metadata are supplied only when the reached lookup requests its missing
mapping default; old receiver tables need no rows for future metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPublicFaultReceiverTables

structure Port (compiled : SourceCoreUnifiedCompilation.Compiled)
    {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) (reason : Word) where
  owner : SourceSpecialization.SpecializationKey
  row : SourceSpecialization.SpecializedFunction
  record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row
  sourceEq : source = row.function.typedBody
  unique : NodeOccurrencesUnique source
  issuer : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)
  present : compiled.indexed.base.diagnostics = some issuer
  token : reason = issuer.program.reasonAt owner id

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}
  {header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
    source id base node baseNode layout comparison first second} {reason : Word}

/-- Static ownership decodes against the actual current registry. -/
theorem Port.missing (port : Port compiled header reason)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
    (functions : FunctionModel compiled.compatible.checked.catalog ambient)
    (_keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (mapping : LocationMap) (world : StoreTyping)
    (baseSource keySource : Dynamic.Value) (baseValue : Value) :
    CompatibleExpressionIndices.MissingPolicy (keyNode := keyNode)
      (registry := completion.result.context.registry) header functions mapping world
      baseSource keySource baseValue reason
      (fun error token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        completion.result.diagnostics (.semantic error) token) := by
  intro rawKey rawValue sources tag entries fallback witness
  have contains : ContainsExpression port.row.function.typedBody node.id node := by
    rw [← port.sourceEq, witness.contains.2]
    exact witness.contains
  have view : CompatiblePublicContextualMissingDiagnosticObservations.CanonicalMappingView
      port.row.function.typedBody base rawKey rawValue := by
    rw [← port.sourceEq]
    refine ⟨baseNode, lookupExpression?_complete port.unique witness.baseContains, ?_⟩
    rw [witness.sourceType, SourceCoreRawMetadata.runtimeType, witness.keyView, witness.valueView]
  have decoded := CompatiblePublicContextualMissingDiagnosticObservations.receiver_index_missing_diagnostic
    compiled receiver port.present port.record (port.sourceEq ▸ port.unique) contains form view witness.fields.metadata
  apply CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded (diagnostic := {
    error := .typeMismatch rawValue none
    site := .occurrence id.occurrence
    span := some node.span })
  · simpa only [← witness.contains.2, port.token] using decoded
  · exact .missing rawValue

/-- The finite certificate selects the actual diagnostic authority. -/
def IndexReady {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context reasonAt scope rootId lowered) : Prop :=
  ∀ {indexScope indexId base key node baseNode keyNode layout comparison first second}
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source indexId base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type),
    Indexes (indexScope := indexScope) indexed keyFound form sourceType root →
    Nonempty (Port compiled indexed (reasonAt indexId))

/-- A legacy tree needs no new diagnostic evidence. -/
theorem IndexReady.of_no_indexes {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context reasonAt scope rootId lowered} (none : NoIndexes root) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed found form sourceType path
  exact False.elim (none indexed found form sourceType path)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticProducers
/-! Actual named compilation and ordinary lambda provenance retain the exact
index issuer. Receivers are not selected here: each invocation later supplies
its current registry to the static authority. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}

/-- The authentic prepared header gives the issuer and original Source row. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (sameSource : source = header.function.source)
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (header.reasonAt id)) := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have original : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]; rfl
  refine ⟨{
    owner := prepared.named.signature.key
    row := prepared.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook
    sourceEq := sameSource.trans original
    unique := sameSource ▸ header.unique
    issuer := issued
    present := present
    token := ?_ }⟩
  rw [aligned.reasonAt, lowered]
  cases compiled.indexed.base.callableContext <;> rfl

/-- Every actual index in a named root has the same genuine source issuer. -/
theorem named_ready {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (sameSource : source = header.function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context header.reasonAt scope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ _
  exact of_prepared prepared diagnostic aligned sameSource indexed

/-- A reached ordinary lambda occurrence retains its original named issuer. -/
theorem of_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (code.reasonAt id)) := by
  obtain ⟨issued, present, token⟩ := reasons id reached
  exact ⟨{
    owner := support.caller.named.signature.key
    row := support.caller.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller
    sourceEq := sameSource.trans support.source
    unique := sameSource ▸ support.unique
    issuer := issued
    present := present
    token := token }⟩

/-- Actual certificate paths restrict the retained body issuer to used indices. -/
theorem ordinary_ready {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression rootId))
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context code.reasonAt rootScope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ path
  have actualReached := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.indexes_reached
    path (sameSource ▸ reached)
  exact of_ordinary support reasons sameSource (sameSource ▸ actualReached) indexed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
/-! General expression syntax follows actual unchanged body occurrences.
Declaration and builtin callees are static metadata; their ordered arguments
are the recursively evaluated children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor NativeMetadataOn)

export CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
  (RuntimeChild runtime_child_references syntax_found syntax_child)

variable {directSites : DeclarationInstantiation → Prop}

section Syntax
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- Recursive syntax crosses only actual reached, unedited occurrences. -/
theorem syntax_view {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax view id directSites := by
  revert reached
  induction tree with
  | leaf finite =>
      intro reached
      exact .leaf (CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.finite_syntax
        edited avoids finite reached)
  | proxy found form =>
      intro reached
      exact .proxy ((expression_lookup edited avoids reached).symm.trans found) form
  | @group id node inner found form child ih =>
      intro reached
      have innerReached : Reaches source roots (.expression inner) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .group ((expression_lookup edited avoids reached).symm.trans found) form (ih innerReached)
  | @tuple id node ids found form children ih =>
      intro reached
      exact .tuple ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @constructor id node instantiation ids found form ranges children ih =>
      intro reached
      exact .constructor ((expression_lookup edited avoids reached).symm.trans found) form ranges
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @builtin id node callee ids function found form children ih =>
      intro reached
      exact .builtin ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @direct id node callee ids instantiation found form monomorphic children ih =>
      intro reached
      exact .direct ((expression_lookup edited avoids reached).symm.trans found) form monomorphic
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @call id node callee ids metadata found form calleeTree children calleeIH childrenIH =>
      intro reached
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .call ((expression_lookup edited avoids reached).symm.trans found) form
        (calleeIH calleeReached)
        (fun child member => childrenIH child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @unary id node operator operand found form child ih =>
      intro reached
      exact .unary ((expression_lookup edited avoids reached).symm.trans found) form
        (ih (.expression reached found (by simp [form, ExpressionForm.references])))
  | @binary id node left operator right found form first second firstIH secondIH =>
      intro reached
      exact .binary ((expression_lookup edited avoids reached).symm.trans found) form
        (firstIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (secondIH (.expression reached found (by simp [form, ExpressionForm.references])))
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
      intro reached
      have baseReached : Reaches source roots (.expression base) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      have keyReached : Reaches source roots (.expression key) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .index ((expression_lookup edited avoids reached).symm.trans found) form
        ((expression_lookup edited avoids keyReached).symm.trans keyFound)
        (firstIH baseReached) (secondIH keyReached)
  | @conditional id node condition yes no found form test thenBranch elseBranch testIH thenIH elseIH =>
      intro reached
      exact .conditional ((expression_lookup edited avoids reached).symm.trans found) form
        (testIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (thenIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (elseIH (.expression reached found (by simp [form, ExpressionForm.references])))

/-- Reverse syntax uses the original body's authentic reachability path. -/
theorem syntax_original {id : ExpressionId} (tree : GeneralSyntax view id directSites)
    (reached : Reaches source roots (.expression id)) : GeneralSyntax source id directSites := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact syntax_view reverse (avoids.view edited.metadata) tree (reached.metadata edited.metadata)
end Syntax

theorem viewed_metadata_native {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (original : NativeMetadataFor compiled.indexed named function.source directSites) :
    NativeMetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) directSites := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have originalTree : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      GeneralSyntax code.view id directSites → GeneralSyntax function.source id directSites := fun id reached tree =>
    syntax_original edited avoids tree
      (reached.metadata code.viewOfSource.symm)
  have lookup : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      ∀ node, code.view.lookupExpression? id = some node → function.source.lookupExpression? id = some node :=
    fun id reached node found => (bodyView id (reached.metadata code.viewOfSource.symm)).trans found
  exact {
    requirements := fun id reached tree node found => original.requirements id (originalTree id reached tree) node (lookup id reached node found)
    coercions := fun id reached tree node found => original.coercions id (originalTree id reached tree) node (lookup id reached node found)
    initializer := fun id reached tree => original.initializer id (originalTree id reached tree)
    arguments := fun id reached tree node found => original.arguments id (originalTree id reached tree) node (lookup id reached node found)
    directCaller := fun id reached tree node found => original.directCaller id (originalTree id reached tree) node (lookup id reached node found)
    localRead := fun id reached tree node found => original.localRead id (originalTree id reached tree) node (lookup id reached node found) }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
/-! The retained contextual reader preserves the actual metadata lookup at
all unchanged body occurrences, including synthetic direct callees. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableLambdaViewEdits CallableLambdaBodyReachability LambdaMetadataViews
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

private inductive Selection : Option Node → Option Node → Prop where
  | none : Selection none none
  | some {before after : Node} (related : NodeView before after) : Selection (some before) (some after)

private theorem find_related {a b : List Node} (related : DataPatternValues.ListRel NodeView a b) (id : OccurrenceId) :
    Selection (a.find? fun node => decide (node.occurrenceId = id))
      (b.find? fun node => decide (node.occurrenceId = id)) := by
  induction related with
  | nil => exact .none
  | @cons before tail after rest head _ ih =>
    simp only [List.find?_cons, head.occurrence]
    split
    · exact .some head
    · exact ih

/-- Metadata views preserve node kind, so equal expression lookups also
preserve the exact missing-node versus statement-node diagnostic branch. -/
theorem lookup_node {source view : TypedSource} (metadata : MetadataView source view)
    {id : ExpressionId} (same : source.lookupExpression? id = view.lookupExpression? id) :
    source.lookupNode? id.occurrence = view.lookupNode? id.occurrence := by
  have selected := find_related metadata.nodes id.occurrence
  change Selection (source.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupExpression? at same
  cases left : source.lookupNode? id.occurrence <;>
    cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected same ⊢
  · cases selected
  · cases selected
  · cases selected with
    | some related =>
      cases related with
      | expression _ _ => exact congrArg (fun node => node.map Node.expression) same
      | statement => rfl

/-- The actual contextual reader skips normalization for these original
monomorphic local reads. Other references retain the same complete node. -/
theorem recipe_read_view {directSites : DeclarationInstantiation → Prop}
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode}
    {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor prepared named source directSites)
    (id : ExpressionId) (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  have same := expression_lookup edited avoids reached
  rw [recipe.readExpression]
  cases found : source.lookupExpression? id with
  | none =>
    have viewed := same.symm.trans found
    simp only [SourceCoreGeneralFunctions.contextualSource, found, viewed]
    rfl
  | some node =>
    have viewed := same.symm.trans found
    have contextual (current : TypedSource) (lookup : current.lookupExpression? id = some node) :
        SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
          (context prepared named).plan prepared.base.locals (context prepared named).owner none current id = .ok current := by
      simp only [SourceCoreGeneralFunctions.contextualSource, lookup, bind, Except.bind, pure, Except.pure]
      split
      · next name binder form =>
        have noLocal := metadata.localRead id (.leaf (.read found form)) node found name binder form
        simp only [noLocal, Bool.false_eq_true, ↓reduceIte]
      · rfl
    simp only [contextual source found, contextual view viewed, bind, Except.bind]
    change SourceCoreCompatibleDataExpressions.readExpression checked source id =
      SourceCoreCompatibleDataExpressions.readExpression checked view id
    exact CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.compatible_read_eq edited.metadata same

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
/-! Original index traces retain base-before-key execution, each strict child
grade, and the exact heap before the lookup decision. Staging and semantic faults stay distinct. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {base key : ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

inductive Children (program : Program) (registry : Registry) (size : Nat) (invocation : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (base key : ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | baseFault {firstSize failure after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.fault failure) after)
      (smaller : firstSize < size) : Children program registry size invocation context environment before base key (.fault failure) after
  | keyFault {firstSize secondSize value failure middle after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.value value) middle)
      (second : Size.Expression program registry secondSize invocation context environment middle key (.fault failure) after)
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size) :
      Children program registry size invocation context environment before base key (.fault failure) after
  | result {firstSize secondSize baseValue keyValue outcome middle after}
      (first : Size.Expression program registry firstSize invocation context environment before base (.value baseValue) middle)
      (second : Size.Expression program registry secondSize invocation context environment middle key (.value keyValue) after)
      (result : IndexOutcome baseValue keyValue outcome)
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size) :
      Children program registry size invocation context environment before base key outcome after

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .index base key)
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    Children program registry size invocation context environment before base key outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .index base key :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | indexBaseFault occurrence first =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .baseFault first (Size.child_lt_stepSize (by simp))
  | indexKeyFault occurrence first second =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .keyFault first second (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp))
  | indexResult occurrence first second result =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.index.inj (actual occurrence)
      exact .result first second result (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp))
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
/-! The existing mapping helper and independent staged Source lookup use the
same terminal decision after both argument heaps have been reached. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
open Core Frontend SourceInference Staging.Recursive

def liftOutcome : Dynamic.ExpressionOutcome → Outcome
  | .value value => .value value
  | .fault reason => .fault (.semantic reason)

theorem of_terminal {base key : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (terminal : CompatibleExpressionIndices.Terminal base key outcome) :
    IndexOutcome base key (liftOutcome outcome) := by
  cases terminal with
  | found shape located => exact .found shape located
  | default shape absent defaulted => exact .default shape absent defaulted
  | shape invalid => exact .shape invalid
  | keyType shape typed mismatch => exact .keyType shape typed mismatch
  | unavailable shape typed absent missing => exact .unavailable shape typed absent missing

theorem to_terminal {base key : Dynamic.Value} {outcome : Outcome}
    (result : IndexOutcome base key outcome) :
    ∃ plain, outcome = liftOutcome plain ∧ CompatibleExpressionIndices.Terminal base key plain := by
  cases result with
  | found shape located => exact ⟨_, rfl, .found shape located⟩
  | default shape absent defaulted => exact ⟨_, rfl, .default shape absent defaulted⟩
  | shape invalid => exact ⟨_, rfl, .shape invalid⟩
  | keyType shape typed mismatch => exact ⟨_, rfl, .keyType shape typed mismatch⟩
  | unavailable shape typed absent missing => exact ⟨_, rfl, .unavailable shape typed absent missing⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
/-! Recursive mapping lookup consumes the actual base and key child states in
order. The lookup suffix keeps their Source heap and transports the retained
caller through its real administrative allocations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionIndices CallableIndexedOwnedPreparedStagedIndexOutcomes
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem completed {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {environment : Environment} {store middleStore keyStore finalStore : Store}
    {baseValue keyValue result : Value} {ξ : Renaming} {reason : Word}
    (firstEval : Evaluates environment store (first.expression.rename ξ) (.inRight .word baseValue) middleStore)
    (secondEval : Evaluates (baseValue :: environment) middleStore (second.expression.rename ((Renaming.insertion 0).comp ξ)) (.inRight .word keyValue) keyStore)
    (lookup : Evaluates (keyValue :: baseValue :: environment) keyStore
      (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore) :
    Evaluates environment store
      ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason).rename ξ)
      result finalStore := by
  rw [index_rename comparison header.registered header.comparisonType]
  rw [rename_prefix] at secondEval
  apply SourceCoreCompatibleDataExpressions.index_completed layout reason firstEval secondEval
  simpa only [CompatibleMapping.Transport.expression_weaken] using lookup

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {compileRegistry : SourceCoreRawMetadata.Registry}
  {extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry compileRegistry}
  {scope : SourceCoreLocalCell.Scope} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr} {reason : Word}
  (header : Header ⟨compiled.compatible.checked, compileRegistry, extension⟩ invocation.source id base node baseNode layout comparison first second)
  (keyFound : invocation.source.lookupExpression? key = some keyNode)
  (form : node.form = .index base key)
  (sourceType : baseNode.type = .mapping keyNode.type node.type)
  (scalar : SourceScalar keyNode.type)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk layout.valueType
  (SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason)

include bridge functions faults unique wellFormed runtime covers header keyFound form sourceType scalar in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults size) :
    PreservesAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ header.baseMetadata.found
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found)
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ keyFound
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change key ∈ [base, key]; simp) keyFound)
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨current, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases CallableIndexedOwnedPreparedStagedIndexSourceInversion.children unique found form trace with
    | baseFault firstTrace smaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
        firstIH _ smaller environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | fault matched =>
        rw [header.baseType] at firstEval
        exact ⟨_, finalStore, finalMap, finalWorld, by
          rw [index_rename comparison header.registered header.comparisonType]
          exact SourceCoreCompatibleDataExpressions.index_base_failure layout reason firstEval,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
    | keyFault firstTrace secondTrace firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstIH _ firstSmaller environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          secondIH _ secondSmaller (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
        cases represented with
        | fault matched =>
          rw [rename_prefix, header.keyType] at secondEval
          exact ⟨_, finalStore, finalMap, finalWorld, by
            rw [index_rename comparison header.registered header.comparisonType]
            exact SourceCoreCompatibleDataExpressions.index_key_failure layout reason firstEval secondEval,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related⟩
    | result firstTrace secondTrace sourceResult firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstIH _ firstSmaller environments heaps locals agrees actualTyped initial admitted firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          secondIH _ secondSmaller (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
        cases represented with
        | value keyPayload =>
          obtain ⟨plain, result, finalStore, futureWorld, terminal, resultRep, lookup, finalHeaps, suffixWorlds, suffixFrame, functional⟩ :=
            header.finish_with_diagnostics sourceType scalar (payload.extend (.refl _) maps worlds) keyPayload
              (actualTyped.weaken (firstWorlds.trans worlds)) keyHeaps reason (missing _ _ _ _ _)
          obtain ⟨original, same, originalTerminal⟩ := to_terminal sourceResult
          have outcomeEq := (functional _ originalTerminal)
          subst original
          subst outcome
          let suffixPool : State headers keys ⟨current, keyMap, futureWorld, after, finalStore, canonical⟩ := (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
          obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
            (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
          refine ⟨result, finalStore, keyMap, futureWorld, completed header firstEval secondEval lookup, ?_,
            finalHeaps, firstMaps.trans maps, (firstWorlds.trans worlds).trans suffixWorlds,
            (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
            returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
          cases resultRep with
          | value represented => exact .value represented
          | fault matched => exact .fault matched
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩


include bridge functions faults unique wellFormed runtime covers header keyFound form sourceType scalar in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults size) :
    ReflectsAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ header.baseMetadata.found
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found)
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ keyFound
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change key ∈ [base, key]; simp) keyFound)
  have occurrence : Staging.Recursive.Occurrence invocation child (.index base key) :=
    ⟨_, lookupExpression?_sound header.metadata.found, form, header.metadata.requirements, header.metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before child outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨current, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      have firstShifted := firstEvaluation
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted firstShifted
      cases represented with
      | fault matched =>
        have failed := firstEvaluation.sound
        rw [header.baseType] at failed
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (SourceCoreCompatibleDataExpressions.index_base_failure layout reason failed)
        exact ⟨_, _, after, finalMap, finalWorld, .indexBaseFault occurrence firstTrace,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        cases branch with
        | caseLeft secondEvaluation lookup =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 shifted
          cases represented with
          | fault matched =>
            have failed := secondEvaluation.sound
            rw [header.keyType] at failed
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (SourceCoreCompatibleDataExpressions.index_key_failure layout reason firstEvaluation.sound failed)
            exact ⟨_, _, after, finalMap, finalWorld, .indexKeyFault occurrence firstTrace secondTrace,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation lookup =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 shifted
          cases represented with
          | value keyPayload =>
            obtain ⟨plain, result, lastStore, futureWorld, terminal, resultRep, suffix, finalHeaps, suffixWorlds, suffixFrame, _functional⟩ :=
              header.finish_with_diagnostics sourceType scalar (payload.extend (.refl _) maps worlds) keyPayload
                (actualTyped.weaken (firstWorlds.trans worlds)) keyHeaps reason (missing _ _ _ _ _)
            have combined := completed header firstEvaluation.sound shifted.sound suffix
            rw [index_rename comparison header.registered header.comparisonType] at combined
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            let suffixPool : State headers keys ⟨current, keyMap, futureWorld, after, finalStore, canonical⟩ :=
              (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
            obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
              (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
            refine ⟨_, liftOutcome plain, after, keyMap, futureWorld,
              .indexResult occurrence firstTrace secondTrace (of_terminal terminal), ?_, finalHeaps,
              firstMaps.trans maps, (firstWorlds.trans worlds).trans suffixWorlds,
              (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
              returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
            cases resultRep with
            | value represented => exact .value represented
            | fault matched => exact .fault matched
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
/-! A complete source with one local read and one lambda has only that read
in the recursive caller grammar. Exact preservation of its metadata supplies
the global original and compiler-view exclusions from actual node contents. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)

private theorem syntax_node {source : TypedSource} {id : ExpressionId}
    (tree : Syntax source id) : ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | leaf product => cases product <;> exact ⟨_, by assumption⟩
  | group found _ _ | tuple found _ _ | call found _ _ _ | constructor found _ _ _
  | unary found _ _ | binary found _ _ _ | conditional found _ _ _ _ =>
    exact ⟨_, found⟩

private theorem syntax_not_lambda {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) : False := by
  cases tree with
  | leaf product =>
    cases product with
    | literal other atomic =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at atomic
      cases atomic
    | read other shape | group other shape _ | pair other shape _ _ =>
      have same := Option.some.inj (other.symm.trans found)
      subst node
      rw [form] at shape
      cases shape
  | group other shape _ | tuple other shape _ | call other shape _ _ | constructor other shape _ _
  | unary other shape _ | binary other shape _ _ | conditional other shape _ _ _ =>
    have same := Option.some.inj (other.symm.trans found)
    subst node
    rw [form] at shape
    cases shape

/-- The original lookup is restricted by the complete retained occurrence list. -/
theorem expression_cases {source : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) : node = read ∨ node = lambda := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa using present

/-- Even a metadata view cannot turn the outer lambda into a supported read. -/
theorem syntax_read {source view : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    (viewRead : view.lookupExpression? read.id = some read)
    {id : ExpressionId} (tree : Syntax view id) :
    id = read.id ∧ view.lookupExpression? id = some read := by
  obtain ⟨actual, found⟩ := syntax_node tree
  obtain ⟨original, originalFound, _sameId, sameForm⟩ := metadata.expression found
  rcases expression_cases nodes originalFound with same | same
  · subst original
    have identity : id = read.id := (lookupExpression?_sound originalFound).2.symm
    exact ⟨identity, identity.symm ▸ viewRead⟩
  · subst original
    exact False.elim (syntax_not_lambda tree found (sameForm.symm.trans lambdaForm))

/-- Real local-read metadata and an empty local-polymorphism catalog provide
all global exclusions required by the retained compiler policy. -/
theorem metadata {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : CallableIndexedNamedGeneration.Named) {source view : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    {name : String} {binder : Resolved.LocalId}
    (viewOf : LambdaMetadataViews.MetadataView source view)
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    (viewRead : view.lookupExpression? read.id = some read)
    (readForm : read.form = .reference name (.local binder))
    (requirements : read.requirements = []) (coercions : read.coercions = [])
    (locals : prepared.base.locals.bindings = []) : MetadataFor prepared named view where
  requirements := by
    intro id tree node found
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    exact same.symm ▸ requirements
  coercions := by
    intro id tree node found
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    exact same.symm ▸ coercions
  initializer := by intro id tree; simp only [locals, List.find?_nil]
  arguments := by
    intro id tree node found callee ids actual form
    have same := Option.some.inj (found.symm.trans (syntax_read viewOf nodes lambdaForm viewRead tree).2)
    subst node
    rw [readForm] at form
    cases form
  localRead := by intro id tree node found name binder form; simp only [locals, List.any_nil]

/-- All actual references in this one-statement body lead to its local read. -/
theorem reached_node {source : TypedSource} {read : ExpressionNode} {statement : StatementNode}
    {name : String} {binder : Resolved.LocalId}
    (readFound : source.lookupExpression? read.id = some read)
    (readForm : read.form = .reference name (.local binder))
    (statementFound : source.lookupStatement? statement.id = some statement)
    (statementForm : statement.form = .returnStmt (some read.id))
    {id : NodeId}
    (reached : CallableLambdaBodyReachability.Reaches source [.statement statement.id] id) :
    id = .statement statement.id ∨ id = .expression read.id := by
  induction reached with
  | root member => exact Or.inl (List.mem_singleton.mp member)
  | expression parent found edge ih =>
      rcases ih with same | same
      · cases same
      · cases same
        have identical := Option.some.inj (found.symm.trans readFound)
        subst identical
        simp [readForm, ExpressionForm.references] at edge
  | statement parent found edge ih =>
      rcases ih with same | same
      · cases same
        have identical := Option.some.inj (found.symm.trans statementFound)
        subst identical
        exact Or.inr (by simpa [statementForm, StatementForm.references] using edge)
      · cases same

/-- The finite actual encoder receipt cannot refer to the unsupported lambda. -/
theorem lowered_read_id {source : TypedSource}
    {read lambda : ExpressionNode} {inner outer : StatementNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (nodes : source.nodes = [.expression read, .statement inner, .expression lambda, .statement outer])
    (lambdaForm : lambda.form = .lambda parameters result body)
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered) :
    id = read.id := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  rcases expression_cases nodes certificate.metadata.found with same | same
  · exact ((lookupExpression?_sound certificate.metadata.found).2.symm.trans (congrArg ExpressionNode.id same))
  · have form := certificate.form
    rw [same, lambdaForm] at form
    cases form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleCompilerReceipts
/-! The original accepted compiler action constructs a finite tuple certificate.
Its actual ordered mapM children are extracted by structural syntax descent.
Leaves retain the existing read/literal/group/pair tree and literal sites.
Static policy and raw typing are independent inputs; no child meaning is a
compiler premise. A group around a new arbitrary tuple is outside this syntax. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleCompilerReceipts
open Core Frontend SourceInference

/-- Only actual original source syntax is stored. The ordered child list may
contain repeated identifiers and any finite arity. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | leaf {id} (tree : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | tuple {id node ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id

/-- These are exact static policy results on the supported source occurrences.
They contain no runtime trace or desired certificate/meaning conclusion. -/
structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

private theorem product_policy {policy compilation readFuel values source scope reasonAt}
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt) :
    CompatibleExpressionProducts.PolicyFor policy compilation readFuel values source scope reasonAt :=
  ⟨fun id tree => policyFor.special id (.leaf tree),
   fun id tree => policyFor.read id (.leaf tree), policyFor.lower, policyFor.leaf⟩

/-- One genuine successful action constructs every reached child's static
receipt internally. The runtime fold consumes this same positive certificate. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
      node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedTupleTreeBounds.Certificate
      readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | leaf tree =>
      exact .leaf (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions
        unique declarations (product_policy policyFor)
        (fun id node tree found => coercions id node (.leaf tree) found)
        tree found typed accepted)
  | tuple originalFound form children ih =>
      cases fuel with
      | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      | succ fuel =>
          exact RecursiveStageTupleMeaning.of_functions_with_leaves
            (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate
              readFuel values source context compilation.solvedRequirements reasonAt)
            unique found (by
              have same := Option.some.inj (originalFound.symm.trans found)
              cases same
              exact form) typed
            (policyFor.special _ (.tuple originalFound form children))
            (policyFor.read _ (.tuple originalFound form children)) policyFor.leaf accepted
            (fun child member childNode code childFound childTyped childAccepted =>
              ih child member childFound childTyped childAccepted)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleCompilerReceipts
end
