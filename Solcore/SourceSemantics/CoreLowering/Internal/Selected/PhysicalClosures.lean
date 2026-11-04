import Solcore.SourceSemantics.SourceCompiledLocalDomainSeparation
import Solcore.SourceSemantics.SourceCompiledLocalLexicalAllocation
import Solcore.SourceSemantics.SourceCompiledLocalCanonicalReadOrder
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.MethodOrigins
import Solcore.SourceSemantics.CoreLowering.ResidualScopeReachability
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedScopedPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.DirectCalls

/-!
# Selected compilations: physical closures

Closures on the physical protocol: lambda formation, application, parent bounds and user dispatch of terminal and branching closures, with the local agreement and materialization facts they depend on.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement
/-! The actual saved scope and selected caller determine complete substitution
agreement on each reached node. The proof retains this equality before any
projection to a body view. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
open CallableLambdaBodyReachability CallableBodyMetadataViews

private theorem expression_node {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

private theorem initialized_of_origin {source : TypedSource}
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance) :
    ({ binder := localInstance.binding.binder,
       initializer := .expression localInstance.binding.initializer } : InitializedLetBinding) ∈
      initializedLetBindings source := by
  obtain ⟨statement, member, form⟩ := localLambdaBindings_statement_origin origin.binding_member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, member, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

private theorem outside_same {lexical current : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical current)
    {q : TypeVarId} (outside : q ∉ current.domain) :
    lexical.apply (.variable q) = current.apply (.variable q) := by
  have lexicalOutside : q ∉ lexical.domain := fun member =>
    outside (extension.domain q member)
  rw [Substitution.apply_variable_of_lookup?_eq_none
      ((Substitution.lookup?_eq_none_iff_not_mem_domain lexical q).mpr lexicalOutside),
    Substitution.apply_variable_of_lookup?_eq_none
      ((Substitution.lookup?_eq_none_iff_not_mem_domain current q).mpr outside)]

/-- A concrete caller allocated after this target cannot change the target's
own or nested quantifiers. Captured ancestors agree by the actual saved-context
extension. The conclusion compares only this exact lambda's reached initializer and body. -/
theorem nodes_at_later_caller
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    (before : target.binding.binder.id.binderIndex < caller.binding.binder.id.binderIndex)
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    ∀ node ∈ named.specialized.function.typedBody.nodes,
      Reaches named.specialized.function.typedBody
        (lambdaRoots target.binding.initializer body) node.id →
      node.applySubstitution lexical = node.applySubstitution caller.substitution := by
  have covered : ResidualEntryCovered named.specialized.function.typedBody
      (body.map NodeId.statement) (target.binding.binder.scheme.quantified ++ lexical.domain) :=
    captured.body (fun _ member => List.mem_append.mpr member) (expression_node found) form
  intro node member reached
  rcases reached.lambda_roots_cases found form with atRoot | bodyPath
  · obtain ⟨variables, scope, origins⟩ := captured
    have actualScope : ResidualScopePath named.specialized.function.typedBody node.id variables := by
      simpa only [atRoot] using scope
    obtain ⟨types, binders⟩ :=
      SelectedCompilationResidualScopes.row_path_support cached row member actualScope
    apply GeneralizedLocalResidualAgreement.node_of_scope types binders
    intro q occurs
    rcases origins q occurs with own | saved
    · apply outside_same extension
      exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
        (initialized_of_origin targetOrigin) before own
    · exact (extension.action q saved).symm
  obtain ⟨variables, scope, origins⟩ := ResidualScopeReachability.scope_of_reaches covered bodyPath
  obtain ⟨types, binders⟩ :=
    SelectedCompilationResidualScopes.row_path_support cached row member scope
  apply GeneralizedLocalResidualAgreement.node_of_scope types binders
  intro q occurs
  rcases origins q occurs with entry | nested
  · rcases List.mem_append.mp entry with own | saved
    · apply outside_same extension
      exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
        (initialized_of_origin targetOrigin) before own
    · exact (extension.action q saved).symm
  · obtain ⟨id, statement, binder, initializer, parent, statementFound, statementForm, owned⟩ := nested
    have contained := lookupStatement?_sound statementFound
    let binding : InitializedLetBinding :=
      { binder := binder, initializer := .expression initializer }
    have localMember : binding ∈ initializedLetBindings
        {named.specialized.function.typedBody with nodes := [.statement statement]} := by
      simp only [initializedLetBindings, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change _ ∈ statementInitializedLetBindings statement.form
      rw [statementForm]
      exact List.mem_singleton_self _
    have globalMember : binding ∈ initializedLetBindings named.specialized.function.typedBody := by
      apply List.mem_flatMap.mpr
      refine ⟨.statement statement, contained.1, ?_⟩
      simpa only [initializedLetBindings, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using localMember
    have descendant : Descends named.specialized.function.typedBody
        (.expression target.binding.initializer) (Node.statement statement).id := by
      simpa only [Node.id, contained.2] using parent.descends_from_lambda found form
    have allocated := selected.local_lambda_initialized_binder_le checked targetOrigin
      contained.1 descendant localMember
    apply outside_same extension
    exact selected.local_domain_excludes_earlier artifact checked position callerOrigin
      globalMember (Nat.lt_of_le_of_lt allocated before) owned

/-- The exact local read supplies the ordering used above. The saved-context
extension alone is never treated as a noninterference law. -/
theorem nodes_at_local_read
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    {read : ExpressionNode} {name : String}
    (readMember : Node.expression read ∈ named.specialized.function.typedBody.nodes)
    (readPath : Descends named.specialized.function.typedBody
      (.expression caller.binding.initializer) (.expression read.id))
    (readForm : read.form = .reference name (.local target.binding.binder.id))
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    ∀ node ∈ named.specialized.function.typedBody.nodes,
      Reaches named.specialized.function.typedBody
        (lambdaRoots target.binding.initializer body) node.id →
      node.applySubstitution lexical = node.applySubstitution caller.substitution :=
  nodes_at_later_caller selected artifact checked position row callerOrigin targetOrigin
    (selected.local_lambda_descendant_read_binder_lt checked callerOrigin readMember readPath readForm)
    extension captured found form

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalNodeAgreement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
/-! Compatibility body views are projections of the actual complete node agreement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
open Frontend SourceInference TypeSystem SourceSpecialization SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
open CallableLambdaBodyReachability CallableBodyMetadataViews

/-- A concrete caller allocated after this target cannot change the target's
own or nested quantifiers. Captured ancestors agree by the actual saved-context
extension. The conclusion compares only this exact lambda's reached initializer and body. -/
theorem body_view_at_later_caller
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    (before : target.binding.binder.id.binderIndex < caller.binding.binder.id.binderIndex)
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    BodyView (named.specialized.function.typedBody.applySubstitution lexical)
      (named.specialized.function.typedBody.applySubstitution caller.substitution)
      (lambdaRoots target.binding.initializer body) :=
  GeneralizedLocalResidualAgreement.body_view_of_nodes
    (SelectedCompilationLocalNodeAgreement.nodes_at_later_caller selected artifact checked
      position row callerOrigin targetOrigin before extension captured found form)

/-- The exact local read supplies the ordering used above. The saved-context
extension alone is never treated as a noninterference law. -/
theorem body_view_at_local_read
    {workspace : Workspace.RawWorkspace} {fuel index : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function}
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {owner : SourceCompilationPlan.Key}
    (row : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan owner =
      .ok named.specialized)
    {caller target : LocalLambdaInstance}
    (callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody caller)
    (targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody target)
    {read : ExpressionNode} {name : String}
    (readMember : Node.expression read ∈ named.specialized.function.typedBody.nodes)
    (readPath : Descends named.specialized.function.typedBody
      (.expression caller.binding.initializer) (.expression read.id))
    (readForm : read.form = .reference name (.local target.binding.binder.id))
    {lexical : Substitution}
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.substitution)
    (captured : CapturedResidualScope named.specialized.function.typedBody
      target.binding.initializer target.binding.binder.scheme.quantified lexical.domain)
    {lambda : ExpressionNode} {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : named.specialized.function.typedBody.lookupExpression? target.binding.initializer =
      some lambda)
    (form : lambda.form = .lambda parameters result body) :
    BodyView (named.specialized.function.typedBody.applySubstitution lexical)
      (named.specialized.function.typedBody.applySubstitution caller.substitution)
      (lambdaRoots target.binding.initializer body) :=
  GeneralizedLocalResidualAgreement.body_view_of_nodes
    (SelectedCompilationLocalNodeAgreement.nodes_at_local_read selected artifact checked
      position row callerOrigin targetOrigin readMember readPath readForm extension captured found form)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
/-! The actual caller and read packets select the same original final-plan row.
This equality comes from their common exact key, independently of runtime
Source history or equality of lambda headers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {relation : TypedSource → TypedSource → Prop}

/-- The native caller's actual view has exactly its accepted flexible action. -/
theorem compiler_source
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      compiled mapping world function relation) :
    material.code.view = material.candidate.origin.source.applySubstitution material.code.active := by
  rw [material.view, material.active, GeneralizedLocalLambdaEmissionFacts.Emission.source,
    GeneralizedLocalLambdaEmissionFacts.Emission.substitution]

/-- Both accepted factories resolve the exact caller key in the same final
plan. The target binding source is identified by the real read catalog entry. -/
theorem read_source
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      compiled mapping world function relation)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      material.code.compilation.owner material.code.active material.code.view scope id reason lowered)
    {inputs : Inputs} {raw : Core.Expr} (packet : Packet inputs receipt.candidate raw)
    (indexed : Indexed compiled.indexed packet) :
    material.candidate.origin.source = receipt.binding.source := by
  obtain ⟨callerRow, callerSelected, callerSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
  obtain ⟨targetRow, targetSelected, targetSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [material.indexed.plan] at callerSelected
  rw [indexed.plan] at targetSelected
  have owner : material.code.compilation.owner = material.candidate.origin.caller := by
    rw [material.compilation]
    exact material.indexed.owner
  have origins := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  rw [origins.1, owner] at targetSelected
  have same : callerRow = targetRow := Except.ok.inj (callerSelected.symm.trans targetSelected)
  rw [same] at callerSource
  exact callerSource.symm.trans (targetSource.trans origins.2.1)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalAttachmentTransport
/-! The actual caller packet, the read's selected packet, and the saved capture
supply a body view at the current context. The saved lexical context and the
same native packet remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalAttachmentTransport
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

private theorem exact_member {plan : Plan}
    {owner : SourceCompilationPlan.Key} {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- A reached read inside this actual contextual invocation supplies its
ordering, capture scope, and exact source row. No equality between the saved
and current substitution is required. -/
theorem attachment_at_contextual_read
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization cached mapping world function relation)
    (callerInitializer : material.candidate.origin.initializer = material.inputs.initializer)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      material.code.compilation.owner material.code.active material.code.view scope id reason lowered)
    (reached : Reaches material.code.view (function.body.map NodeId.statement) (.expression id))
    {inputs : Inputs} {raw : Core.Expr} (packet : Packet inputs receipt.candidate raw)
    (indexed : Indexed cached.indexed packet)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical material.code.active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer) :
    GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding material.code.active := by
  have bindingId := receipt.binding_identity.2
  have sameReadSource := SelectedCompilationLocalSourceReceipts.read_source material receipt packet indexed
  have origins := GeneralizedLocalAcceptedCatalogFormation.read_origins receipt
  have active : material.code.active = material.candidate.origin.localInstance.substitution := by
    exact material.active.trans (GeneralizedLocalLambdaEmissionFacts.Emission.substitution _)
  have targetInitializer : receipt.candidate.origin.localInstance.binding.initializer =
      receipt.binding.initializer := origins.2.2.2
  have targetBinder : receipt.candidate.origin.localInstance.binding.binder =
      receipt.binding.binder := origins.2.2.1
  obtain ⟨row, rowFound, rowSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
  rw [material.indexed.plan] at rowFound
  obtain ⟨index, named, position, sameRow⟩ :=
    SelectedCompilationCachedSources.row_position cached (exact_member rowFound)
  obtain ⟨selected, _⟩ := SourceBodyTemplateScope.cached_selection_scope artifact checked position
  have sameSource : named.specialized.function.typedBody = material.candidate.origin.source := by
    rw [sameRow]
    exact rowSource
  have sameBindingSource : named.specialized.function.typedBody = receipt.binding.source :=
    sameSource.trans sameReadSource
  have callerOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody
      material.candidate.origin.localInstance := by
    rw [sameSource]
    exact GeneralizedLocalLexicalOrigin.materialized_origin material
  have targetOrigin : LocalLambdaInstance.LexicalReadOrigin named.specialized.function.typedBody
      receipt.candidate.origin.localInstance := by
    rw [sameBindingSource, ← origins.2.1]
    exact GeneralizedLocalLexicalOrigin.packet_origin packet
  have callerFound := material.code.found
  rw [SelectedCompilationLocalSourceReceipts.compiler_source material, material.codeId,
    ← callerInitializer] at callerFound
  obtain ⟨callerNode, callerParameters, callerResult, callerFound, callerForm⟩ :=
    GeneralizedLocalCapturedLambdaHeader.lambda_header_before_substitution callerFound
      (material.code.form.trans material.code.sourceForm)
  have rawReached : Reaches material.candidate.origin.source
      (function.body.map NodeId.statement) (.expression id) := by
    apply (reaches_substitution material.code.active).mp
    rwa [← SelectedCompilationLocalSourceReceipts.compiler_source material]
  have readPath := rawReached.descends_from_lambda callerFound callerForm
  have readFacts := lookupExpression?_sound receipt.originalFound
  have actualPath : Descends named.specialized.function.typedBody
      (.expression material.candidate.origin.localInstance.binding.initializer)
      (.expression receipt.original.id) := by
    simpa only [sameSource, SourceCompilationPlan.LocalLambdaCatalogEntry.initializer, readFacts.2] using readPath
  have readMember : Node.expression receipt.original ∈ named.specialized.function.typedBody.nodes := by
    rw [sameBindingSource]
    exact readFacts.1
  obtain ⟨name, readForm⟩ := receipt.originalForm
  have targetRead : receipt.original.form =
      .reference name (.local receipt.candidate.origin.localInstance.binding.binder.id) := by
    rw [targetBinder, bindingId]
    exact readForm
  obtain ⟨targetNode, targetParameters, targetResult, targetFound, targetForm⟩ :=
    GeneralizedLocalCapturedLambdaHeader.captured_header saved captures unique initializer
  have targetFound' : named.specialized.function.typedBody.lookupExpression?
      receipt.candidate.origin.localInstance.binding.initializer = some targetNode := by
    rw [sameBindingSource, targetInitializer]
    exact targetFound
  have captured : CapturedResidualScope named.specialized.function.typedBody
      receipt.candidate.origin.localInstance.binding.initializer
      receipt.candidate.origin.localInstance.binding.binder.scheme.quantified lexical.domain := by
    rw [sameBindingSource, targetInitializer, targetBinder]
    exact saved.captured
  have extended : GeneralizedLocalBundleContexts.ContextExtension lexical
      material.candidate.origin.localInstance.substitution := by
    rw [← active]
    exact extension
  have actualRow : SourceCompilationPlan.exactSpecialization cached.indexed.base.plan
      material.candidate.origin.caller = .ok named.specialized := by
    simpa only [sameRow] using rowFound
  have related := SelectedCompilationLocalScopeAgreement.body_view_at_local_read selected
    artifact checked position actualRow callerOrigin targetOrigin readMember actualPath targetRead
    extended captured targetFound' targetForm
  have currentView : BodyView (receipt.binding.source.applySubstitution lexical)
      (receipt.binding.source.applySubstitution material.code.active)
      (lambdaRoots descriptor.initializer descriptor.body) := by
    simpa only [sameBindingSource, ← active, targetInitializer, initializer] using related
  exact ⟨GeneralizedLocalPreparedClosure.materialized_closed material,
    saved.view.trans currentView⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalAttachmentTransport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
/-! A concrete contextual read consumes the transported capture and returns
the same native materialization together with its actual body-entry scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalAcceptedMaterialization

private theorem expression_node {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    source.lookupNode? id.occurrence = some (.expression node) := by
  unfold TypedSource.lookupExpression? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | statement => simp [selected] at found
    | expression expression =>
      have same : expression = node := by simpa [selected] using found
      simp only [same]

/-- This evidence is attached to the existing materialization; it adds no
native value, body model, or assumed execution law. -/
structure Entry {cached : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : Materialization cached mapping world function relation) : Prop where
  initializer : material.candidate.origin.initializer = material.inputs.initializer
  covered : ResidualEntryCovered material.candidate.origin.source
    (function.body.map NodeId.statement) material.code.active.domain

/-- Every input comes from this invocation, its reached read, and the same
stored Snapshot. The active body view is derived before materialization. -/
theorem materialize_at_contextual_read
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {callerMapping : GeneralHeap.LocationMap} {callerWorld : StoreTyping} {callerFunction : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (caller : Materialization cached callerMapping callerWorld callerFunction relation)
    (callerEntry : Entry caller)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller.code.compilation.owner caller.code.active caller.code.view scope id reason lowered)
    (reached : Reaches caller.code.view (callerFunction.body.map NodeId.statement) (.expression id))
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical caller.code.active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply caller.code.active)
    (sameType : actualType = receipt.node.rawType) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization cached mapping world function
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧
      material.candidate = receipt.candidate ∧ material.actualType = actualType ∧ material.semantic = semantic ∧
      material.context = context ∧ material.callerEvidence = callerEvidence ∧ material.produced = produced ∧
      material.requirements = requirements ∧ material.frameLocation = frameLocation ∧ Entry material ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual := by
  have activeAttachment : GeneralizedLocalReachedAllocation.Attachment descriptor receipt.binding
      caller.code.active := by
    cases row with
    | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder
        savedAttachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
      exact SelectedCompilationLocalAttachmentTransport.attachment_at_contextual_read artifact checked
        caller callerEntry.initializer receipt reached packet indexed saved extension captures unique initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEvidenceEq, producedEq, requirementsEq, frameEq, originInitializer, nativeEq⟩ :=
    GeneralizedLocalReachedAssociation.materialize_snapshot_at_read receipt row activeAttachment
      captures unique initializer instantiation sameScheme sameType
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq,
    contextEq, callerEvidenceEq, producedEq, requirementsEq, frameEq, ⟨originInitializer, ?_⟩, nativeEq⟩
  obtain ⟨node, parameters, result, found, form⟩ :=
    GeneralizedLocalCapturedLambdaHeader.captured_header saved captures unique initializer
  have covered := saved.captured.body
    (GeneralizedLocalCapturedScopes.read_keys receipt extension) (expression_node found) form
  have sourceEq : material.candidate.origin.source = receipt.binding.source := by
    rw [candidateEq]
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.1
  have activeEq : material.code.active = receipt.candidate.origin.substitution := by
    rw [material.active, GeneralizedLocalLambdaEmissionFacts.Emission.substitution, candidateEq]
  simpa only [sourceEq, activeEq, Dynamic.GeneralizedClosure.instantiate] using covered

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalReadMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization
/-! A named caller reads under the empty active substitution. Its stored
Snapshot materializes with the same saved frame and carries the actual next
body entry, using the existing representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalAcceptedMaterialization
open SelectedCompilationLocalReadMaterialization (Entry)
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)

private theorem packet_entry {cached : SourceCoreUnifiedCompilation.Compiled}
    {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller .empty source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical .empty)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (same : candidate = receipt.candidate) (packet : Packet inputs candidate raw)
    (initializer : inputs.initializer = receipt.binding.initializer) :
    ResidualEntryCovered receipt.binding.source (packet.statements.map NodeId.statement)
      packet.original.emission.prepared.substitution.domain := by
  subst candidate
  exact GeneralizedLocalCapturedScopes.body_at_read cached receipt saved extension packet initializer

/-- The empty named context transports the saved attachment and the actual
accepted Packet supplies the new body scope. -/
theorem materialize_at_named_read
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      caller .empty source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical .empty)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply .empty)
    (sameType : actualType = receipt.node.rawType) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization cached mapping world function
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧
      material.candidate = receipt.candidate ∧ material.actualType = actualType ∧ material.semantic = semantic ∧
      material.context = context ∧ material.callerEvidence = callerEvidence ∧ material.produced = produced ∧
      material.requirements = requirements ∧ material.frameLocation = frameLocation ∧ Entry material ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual := by
  have activeAttachment := GeneralizedLocalCapturedScopes.Attachment.at_empty extension saved
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEvidenceEq, producedEq, requirementsEq, frameEq, originInitializer, nativeEq⟩ :=
    GeneralizedLocalReachedAssociation.materialize_snapshot_at_read receipt row activeAttachment
      captures unique initializer instantiation sameScheme sameType
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq,
    contextEq, callerEvidenceEq, producedEq, requirementsEq, frameEq, ⟨originInitializer, ?_⟩, nativeEq⟩
  have covered := packet_entry receipt saved extension candidateEq material.packet
    (material.initializer.trans (congrArg SourceCoreLocalPolymorphism.Binding.initializer bindingEq))
  rw [(GeneralizedLocalAcceptedBodyCompiler.lambda_fields material).2.2, ← material.active] at covered
  have sourceEq : material.candidate.origin.source = receipt.binding.source := by
    rw [candidateEq]
    exact (GeneralizedLocalAcceptedCatalogFormation.read_origins receipt).2.1
  simpa only [sourceEq] using covered

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReadMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationHeads
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

include globals slots prefixZero in
/-- The literal formation copies the captured cells; the formed closure over the
copies is represented in the formed state. -/
theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope canonical)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ captured after payload finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies (CallableIndexedNamedGeneration.source caller.named) environment before captured after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) finalStore ∧
      ValueRep compiled.compatible.checked receiving functions finalMap finalWorld
        receipt.site.code.sourceNode.type (.closure (receipt.toFormation.function captured)) payload lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  let head := receipt.toFormation
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := CallableIndexedOwnedPhysicalLambdaCaptures.captures_for allSlots globals entry environments agrees nativeTyped
  have observed := CallableIndexedOwnedPhysicalLambdaCaptures.capture_globals_for allSlots globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  have capturedSlots := CallableIndexedOwnedPhysicalLambdaCaptures.capture_slots_for allSlots globals entry environments agrees nativeTyped
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults := head.support environment
  obtain ⟨formed, _sourceTrace, native, _determined, member⟩ :=
    @CallableIndexedOwnedPhysicalLambdaFormation.formation_member compiled headers keys
      bodyRegistry semanticFaults mapping world (head.function environment) scope actual canonical before store
      captured code support owner initial.val initial.property profile rfl observed (receipt.at environment globals)
      capturedSlots _ _ heaps receipt.site.snapshots receipt.ordinary receipt.coercions
  have payload := CallableIndexedOwnedPreparedPhysicalCellOrigins.payload_static_member (registry := receiving) profile (CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember.legacy member)
  let actualHistory : History code :=
    @CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at compiled headers keys bodyRegistry
      semanticFaults (head.function environment) scope mapping world before store actual canonical
      captured code support owner initial.val initial.property
  refine ⟨formed.captured, formed.finalHeap, value code formed.embedding actualHistory.native formed.closureActual,
    formed.finalStore, formed.finalMap, formed.finalWorld, formed.copy, ?_, ?_, formed.heaps, formed.maps, formed.worlds,
    formed.frame⟩
  · simpa only [code, Formation.code, recaptureCode, head, receipt.emitted, captured, CallableIndexedOwnedPhysicalLambdaCaptures.captures_for, actualHistory] using native
  have sourceType : receipt.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, Formation.code, recaptureCode, head, receipt.emitted] using nativeType
  rw [emittedType]
  exact payload

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
/-! Ordinary lambda formation uses the actual named packet and keeps the
same positive closure member in the public receiving model. The retained
Site and body are static compiler receipts; captures come from this input,
and the formation copies them, so the caller packet is transported to the
formed state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedPhysicalNestedCanonicalState.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {parameters result body failedScope call reason}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have actual : ∀ {shape requirements}, Staging.Recursive.Occurrence scope id shape requirements →
      shape = .lambda parameters result body := by
    intro shape requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases actual occurrence


variable (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

include globals slots prefixZero sameSource unique runtime covers in
theorem preserves (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt.toFormation
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : ∃ captured, outcome = .value (.closure {head.function environment with captured := captured}) ∧
      Dynamic.EnvironmentCopies (head.function environment).source (head.function environment).captured before captured after := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source (head.function environment).captured before code.id value after := by
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.value_plain
      obtain ⟨captured, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨captured, rfl, copy⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.site.code.sourceForm receipt.coercions trace)
  obtain ⟨captured, rfl, copy⟩ := changed
  obtain ⟨formedCaptured, formedHeap, payload, finalStore, finalMap, finalWorld, formedCopy, native, represented,
      finalHeaps, maps, worlds, frame⟩ := SelectedCompilationPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨.inRight .word payload, finalStore, finalMap, finalWorld, native, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

include globals slots prefixZero sameSource runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨captured, after, payload, formedStore, finalMap, finalWorld, copy, native, represented, finalHeaps, maps,
      worlds, frame⟩ := SelectedCompilationPhysicalLambdaFormationHeads.forms caller owner context invocation profile globals slots
    prefixZero receipt environments heaps agrees nativeTyped initial.base.property initial.base.val
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure (receipt.toFormation.function captured))) after := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.site.code.sourceForm]
    simpa only [Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (before := before) (after := after) (captured := captured)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements) receipt.ordinary
        (by rw [sameSource]; exact copy))
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedPhysicalNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedPhysicalNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial maps worlds frame copy.metadata_extends
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, finalMap, finalWorld, sourceTrace, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  have closureTyped := SelectedCompilationLambdaAdmission.value_typed runtime covers (copy.agrees locals)
    sourceFound receipt.site.code.sourceForm receipt.coercions typed
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative ((bridge).pool initial)
    ((bridge).pool reached) admitted.rows frame, ?_⟩
  intro value same
  cases same
  refine ⟨?_, admitted.heap.copy copy⟩
  simpa only [ Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using closureTyped

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalLambdaFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedSupport
/-! Each named scoped child retains its actual physical mixed root and compiler
prefix. The authentic named receipt supplies the complete collected statement
tree and its catalog sites; execution is supplied by the shared numeric family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationMixedRootSupport (RootAt)
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Certificate
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  ∃ root : RootAt compiled headers stages context invocation scope id lowered semanticFaults,
    root.compilation.administrativePrefix = 1

structure Support
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry) (receipt : Receipt header)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  certified : SelectedCompilationNamedSourceTyping.Certified header
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    header.function.source invalidProjection missingDefault)
  tree : ∀ child, stages.Closure header.function child →
    ∃ expressionSyntax : ExpressionId → Prop,
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults)
      header.layouts header.owner header.active compiled.indexed.ancestry.layout.frame
      header.globals header.onError (.initial compiled.compatible.checked) child.source expressionSyntax
      (TypedCertificate child.source (fun context => Certificate headers stages semanticFaults context child))
      compiled.indexed.layouts.definitions
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      header.context (parameterScope header) (.statements true header.function.body)
      header.function.resultType header.output receipt.flow

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedScopedSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
/-! The actual selected closure and accepted physical row determine the two
ordered argument vectors independently. Raw Source typing follows the executed
successful argument trace at its reached heap. The positive contextual payload
retains the real closure Code; native bundle equality supplies no Source count.
No body or application meaning is part of this argument producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {environment : Dynamic.Environment}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.Closure} {carrier : Value} {parameter result : TypeSystem.Ty}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {calleeHeap : Dynamic.Heap} {index : ProtectedStateTransition.Index}
  (reached : callerProtocol.State index)
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include dispatch selected count in
/-- Original binding, actual Source list length and the same selected second
row fix physical closure arity before either packed type is used. -/
theorem source_arity {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    sources.length = function.parameters.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  have physical : dispatch.row.entry.parameterCount = function.parameters.length := by
    cases dispatch.bound with
    | closure parameters _ =>
      exact (selected.parameter_count retained).trans (congrArg List.length parameters)
  exact trace.sound.length.symm.trans (count.symm.trans physical)

include bridge profile compiler reached dispatch selected count in
/-- At the actual successful argument endpoint, the original Source trace
constructs raw closure admission and its frame. The same positive payload then
constructs the retained contextual member and exact native binder arguments. -/
theorem at_arguments
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap sources sourceTypes)
    (extension : Dynamic.HeapMetadataExtend calleeHeap index.heap)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (admitted : Admission bridge context reached)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (calleeRelated : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry semanticFaults profile index.mapping index.world
      (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) sources values)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap sources ∧
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function ∧
    ∃ bindings parameterCore resultCore,
      CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember headers keys bodyRegistry semanticFaults
        index.mapping index.world function carrier bindings parameterCore resultCore ∧
      compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore ∧
      CallableIndexedParameterMeaning.Arguments model index.mapping index.world bindings sources values := by
  have arity := source_arity dispatch selected count trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, evidence⟩
  obtain ⟨bindings, parameterCore, resultCore, member, nativeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have sameTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    ((actualFunctionType ▸ compiler.callableType).trans nativeType)
  have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans (sameTypes.1.trans (member.parameter_core profile)))
  obtain ⟨parameters, _result, _signatures, _code, _evidence, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [member.source_binders]
    exact bundle.trans parameters
  have bindingArity : sources.length = bindings.length := by
    have retainedBinders : bindings.length = function.parameters.length := by
      simpa only [List.length_map] using congrArg List.length member.source_binders
    exact arity.trans retainedBinders.symm
  exact ⟨raw, valid, bindings, parameterCore, resultCore, member, sameTypes.1, sameTypes.2,
    CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
      bindingArity sourceBundle nativeBundle⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingClosureStaticSupport
/-! Actual scoped closure compilation retains the original flow and mixed
expression roots at each reached lexical context. No execution law is stored. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingClosureStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

structure SelectedBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Branching code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type where
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  readFuel : Nat
  «prefix» : code.compilation.administrativePrefix = 1
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  assignmentAuthority : Nonempty (PreparedAssignmentDiagnosticAuthority.SourcePort compiled
    function.source invalidProjection missingDefault)
  collected : ∀ child, stages.Closure function child →
    CallableIndexedOwnedPreparedBranchingCatalogSites.Collected invalidProjection missingDefault (faults := semanticFaults) compiled.indexed.layouts packet.allocationOwner packet.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length packet.onError
      (.initial compiled.compatible.checked) child.source (fun _ => True)
      (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate child.source
        (fun context scope id lowered => Nonempty (Σ rawType,
          SelectedCompilationMixedRootSupport.Root compiled headers stages
            code.policy code.lowerBody code.compilation readFuel context child code.reasonAt
            scope id lowered rawType semanticFaults)))
      compiled.indexed.layouts.definitions administrative
      inputs.context (parameterScope code) (.statements true function.body) function.resultType code.receipt.resultCore packet.flow

abbrev SelectedBody.tree {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @SelectedBody compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :=
  (support.collected child selected).tree

theorem SelectedBody.sites {compiled function scope administrative headers code inputs stages packet semanticFaults}
    (support : @SelectedBody compiled function scope administrative headers code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (registry : SourceCoreRawMetadata.Registry) :
    PreparedBranchingCatalogSites.CatalogSites support.invalidProjection support.missingDefault registry semanticFaults
      (support.tree child selected) :=
  (support.collected child selected).sites registry

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingClosureStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaBodyBounds
/-! The retained physical packet supplies the existing scoped flow engine
with actual captured global slots. Local allocation, mutation and finite loops
keep those slots and the reached pool throughout every method or indirect child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedSourceAdmission
open SelectedCompilationMixedRootSupport (RootAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)
open SelectedCompilationPhysicalBranchingClosureStaticSupport (SelectedBody)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : SelectedBody headers code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled
    code.compilation.administrativePrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "canonicalBridge" =>
  CallableIndexedOwnedNamedCallerProtocol.Carrier.forgetSlots
    (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
      code.compilation.administrativePrefix)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      completion.result.diagnostics (.semantic reason) token))


private theorem capturedSlots_after_prefix
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope canonical)
    (added : Environment) (length : added.length = bindings.length)
    (copied : Environment) {final : Environment} (spine : final = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) final := by
  subst final
  intro slot signature found
  have offset : (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + callerPrefix + slot =
      added.length + (scope.length + callerPrefix + slot) := by simp only [List.length_append, List.length_map, List.length_reverse]; omega
  rw [offset, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, kept _ (by omega)]
  exact slots slot signature found

private theorem forget_post (callerPrefix : Nat) {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.base.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

include support capturedSlots physical ownerPhysical stable beforeTyped argumentsTyped semantic faithful observations assignmentInterpretation in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict recursive whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have tree := support.tree child selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape child.source true function.body := by
    rw [stages.source selected]
    exact packet.shape
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact support.frame.code.graph.nodeOccurrencesUnique
  have slots := capturedSlots_after_prefix capturedSlots added length copied spine kept
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩ := ⟨⟨reached, slots⟩,
          (physical.install (frameLocation := owner.key.frameLocation)
            (native := (caller.rows owner.position).authority.current) entry.currentRead entry.next).extend entry.entry.frame⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge inputs.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  obtain ⟨flowValue, bodyStore, finalMap, finalWorld, evaluated, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_at
      canonicalBridge
      (CallableIndexedOwnedPhysicalCanonicalState.bindings code.compilation.administrativePrefix)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport code.compilation.administrativePrefix)
      functions faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) code.compilation.administrativePrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) code.compilation.administrativePrefix stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨rawType, root⟩ := certified
        exact children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner
          ownerPhysical
          ⟨rfl, rfl, rfl⟩)
      unique tree (support.sites child selected completion.result.context.registry) semantic
      (by
        rw [stages.source selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection within entry.entry.environments entry.entry.heaps
      entry.entry.locals entry.entry.lookups entry.entry.actualTyped entry.entry.reference entry.entry.read
      entry.entry.unmapped initial conditioned canonicalAdmitted trace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    unique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨value, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented evaluated
      packet.fellThrough packet.escaped entry.entry.embedding
  have outcomeEq := CallableIndexedOwnedAdmittedStagedLexicalFooter.outcome_eq matched
  subst outcome
  refine ⟨value, bodyStore, finalMap, finalWorld, ?_, representedBody, heaps,
    maps, worlds, frame, metadata, returned.base.val, related, forget_post code.compilation.administrativePrefix returned post⟩
  simpa only [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] using evaluatedBody

include support capturedSlots physical ownerPhysical stable beforeTyped argumentsTyped semantic functionTypes faithful observations assignmentInterpretation in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _sourceComplete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source packet.selected] at sourceTyped
  have originalTyping : ProtectedStateImperativeTypedSourceSites.Statements packet.child.source inputs.context function.body :=
    ⟨_, _, _, sourceTyped⟩
  have graph : OccurrenceGraphWellFormed packet.child.source := by
    rw [stages.source packet.selected]
    exact valid.code.graph
  have tree := support.tree packet.child packet.selected
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape packet.child.source true function.body := by
    rw [stages.source packet.selected]
    exact packet.shape
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  have slots := capturedSlots_after_prefix capturedSlots added length copied spine kept
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys code.compilation.administrativePrefix).State
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap,
        entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩,
          (physical.install (frameLocation := owner.key.frameLocation)
            (native := (caller.rows owner.position).authority.current)
            (CallableIndexedOwnedFunctionEntries.reached_frame_read caller owner.position) entry.next).extend entry.frame⟩
  have canonicalAdmitted : CallableIndexedOwnedSourceAdmission.Admission canonicalBridge inputs.context initial :=
    ⟨admitted.heap, admitted.rows⟩
  have conditioned := CallableIndexedOwnedAllocationProducer.stableOwner_selected owner.position entry.nextHistory
  have bodyTrace := completed
  rw [packet.emitted, CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at bodyTrace
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix bodyTrace within
  obtain ⟨sourceSize, finalContext, bodyOutcome, after, finalMap, finalWorld, trace, represented, heaps,
      maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedScopedImperativeFlow.reflects_at
      canonicalBridge
      (CallableIndexedOwnedPhysicalCanonicalState.bindings code.compilation.administrativePrefix)
      (CallableIndexedOwnedPhysicalCanonicalState.administrativeTransport code.compilation.administrativePrefix)
      functions functionTypes faithful observations completion.result.extension rfl (CallableIndexedAmbient.frame_registered compiled.indexed)
      (CallableIndexedOwnedPhysicalCanonicalState.markedProducer
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) code.compilation.administrativePrefix)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (fun _ _ stable => CallableIndexedOwnedPhysicalCanonicalState.readyAt_of_stableOwner
        (headers := headers) (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions) code.compilation.administrativePrefix stable)
      (fun context size smaller scope id lowered certified => by
        obtain ⟨rawType, root⟩ := certified
        exact children size smaller
          (SelectedCompilationMixedRootSupport.RootAt.ofRoot root) owner
          ownerPhysical
          ⟨rfl, rfl, rfl⟩)
      graph tree (support.sites packet.child packet.selected completion.result.context.registry) semantic
      (by
        rw [stages.source packet.selected]
        obtain ⟨port⟩ := support.assignmentAuthority
        exact assignmentInterpretation port functions _) rfl shape originalTyping support.projection (Nat.le_of_lt strict) entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped initial
      conditioned canonicalAdmitted flowTrace
  have post := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post
  have controlClosed := Staging.Recursive.TypedControlBoundary.function
    graph.nodeOccurrencesUnique sourceTyped rfl trace.sound
  have represented := CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents.to_function support.projection represented controlClosed
  obtain ⟨bodyValue, evaluatedBody, representedBody⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates represented flowTrace.sound
      packet.fellThrough packet.escaped entry.embedding
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic bodyTrace.sound evaluatedBody
  subst bodyValue
  subst flowStore
  exact ⟨sourceSize, finalContext, bodyOutcome, _, after, finalMap, finalWorld, trace,
    represented.body_result, representedBody, heaps, maps, worlds, frame, metadata, returned.base.val, related, forget_post code.compilation.administrativePrefix returned post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaApplicationBounds
/-! The retained scoped body fills the public closure application ports from
canonical expression children. Actual parameter installation retains its
binding spine, while the saved caller receives the exact reached pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching)
open SelectedCompilationPhysicalBranchingClosureStaticSupport (SelectedBody)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Branching code stages)
  (support : SelectedBody headers code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled
    code.compilation.administrativePrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (ownerPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))


include support capturedSlots physical ownerPhysical stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic faithful observations assignmentInterpretation in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length copied spine kept reached childSize strict =>
      SelectedCompilationPhysicalBranchingLambdaBodyBounds.source_body_at (semantic := semantic)
        (faithful := faithful) (observations := observations) (assignmentInterpretation := assignmentInterpretation)
        (functions := functions) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (capturedSlots := capturedSlots) (physical := physical) (ownerPhysical := ownerPhysical) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry added length copied spine kept reached children (Nat.le_of_lt strict))
    trace within

include support capturedSlots physical ownerPhysical stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime semantic functionTypes faithful observations assignmentInterpretation in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      SelectedCompilationPhysicalBranchingLambdaBodyBounds.native_body_at (semantic := semantic)
        (functionTypes := functionTypes) (faithful := faithful) (observations := observations)
        (assignmentInterpretation := assignmentInterpretation)
        (functions := functions) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (capturedSlots := capturedSlots) (physical := physical) (ownerPhysical := ownerPhysical) (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaBodyBounds
/-! The real closure parameter entry retains every captured global reference
and every installed cache cell. Terminal expression bounds use the resulting
physical caller, with the original frame and whole returned pool. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (callerPrefix : Nat)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {expression : ExpressionId}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
  (terminal : Receipt policy fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression function.body code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ lowered,
    policy.lowerExpression terminal.childFuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression reasonAt = .ok lowered →
    certificate
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression lowered)

private theorem capturedSlots_after_prefix
    {bindings : List CallableIndexedParameterCertificates.Binding}
    {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope canonical)
    (added : Environment) (length : added.length = bindings.length)
    (copied : Environment) {final : Environment} (spine : final = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) final := by
  subst final
  intro slot signature found
  have offset : (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + callerPrefix + slot =
      added.length + (scope.length + callerPrefix + slot) := by simp only [List.length_append, List.length_map, List.length_reverse]; omega
  rw [offset, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, kept _ (by omega)]
  exact slots slot signature found

private theorem forget_post {index : ProtectedStateTransition.Index}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (state : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State index)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots
      context type outcome state) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys))
      context type outcome state.base.val := by
  cases outcome with
  | value value => exact ⟨post.rows, post.successful⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, post.successful⟩
    | stage origin call reason => exact post

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies in
/-- The actual Source closure rule supplies its selected scope and frame.
The same compiler body and parameter pool satisfy the Source body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment) (length : added.length = code.receipt.loweredParameters.length)
    (copied : Environment) (spine : entry.entry.canonical = added ++ copied)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (budget bodySize : Nat) (within : bodySize ≤ budget)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  have slots := capturedSlots_after_prefix capturedSlots added length copied spine kept
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State
      ⟨_, entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := ⟨⟨reached, slots⟩, (physical.install (frameLocation := owner.key.frameLocation)
        (native := (caller.rows owner.position).authority.current) entry.currentRead entry.next).extend entry.entry.frame⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots)
    (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
    (environments := entry.entry.environments) (heaps := entry.entry.heaps)
    (locals := entry.entry.locals) (agrees := entry.entry.lookups)
    (typed := entry.entry.actualTyped) (initial := initial) (admitted := ⟨admitted.heap, admitted.rows⟩)
    unique budget (children child selected) trace matched within
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, returned.base.val, related, forget_post callerPrefix returned post⟩

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies in
/-- Native completion uses the same retained parameter prefix and original
registry scope. Its independently graded Source body is constructed from the
strict expression reflection at that actual entry. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function)
    (budget nativeSize : Nat) (within : nativeSize ≤ budget)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := faults)
      captured code history inputs functions owner caller entry reached child nativeSize := by
  intro value bodyStore completed
  have view : LambdaMetadataViews.MetadataView child.source code.view := by
    rw [stages.source selected]
    exact code.viewOfSource
  obtain ⟨staticFinal, facts, bodyTyped, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters valid inputs.extended
  rw [← stages.source selected] at bodyTyped
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact valid.code.graph.nodeOccurrencesUnique
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
  have slots := capturedSlots_after_prefix capturedSlots added length copied spine kept
  let initial : (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys callerPrefix).State
      ⟨_, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩ := ⟨⟨reached, slots⟩, (physical.install (frameLocation := owner.key.frameLocation)
        (native := (caller.rows owner.position).authority.current)
        (CallableIndexedOwnedFunctionEntries.reached_frame_read caller owner.position) entry.next).extend entry.frame⟩
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context initial := ⟨heapTyped, rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, meaning,
      heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
      (receipt := terminal) (view := view) (bridge := (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots)
      (bodyTyped := bodyTyped) (complete := completes) (certifies := certifies)
      (environments := entry.environments) (heaps := entry.heaps)
      (locals := entry.locals) (agrees := entry.lookups) (typed := entry.actualTyped)
      (initial := initial) (admitted := admitted) unique budget children completed within
  exact ⟨sourceSize, inputs.context,
    CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome,
    outcome, after, finalMap, finalWorld, trace, matched, meaning,
    heaps, maps, worlds, frame, metadata, returned.base.val, related, forget_post callerPrefix returned post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
/-! The actual retained closure application constructs its terminal body
ports from the same compiler receipt and strict expression hypotheses.
Parameter installation and caller restoration use their original producers;
semantic and stage failures keep their exact Source scope and reached state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (callerPrefix : Nat)
  (capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled callerPrefix scope captured.canonical)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {expression : ExpressionId}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
  (terminal : Receipt policy fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression function.body code.receipt.resultCore reasonAt fellThrough escaped code.receipt.body)
  {certificate : GenericExpressionMeaning.Certificate}
  (certifies : ∀ lowered,
    policy.lowerExpression terminal.childFuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression reasonAt = .ok lowered →
    certificate
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression lowered)


variable (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- The strict body port is manufactured at the genuine parameter entry.
The Source application and both native prefixes run once. -/
theorem application_preserves (budget : Nat)
    (children : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
        (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry added length copied spine kept reached childSize strict =>
      SelectedCompilationPhysicalTerminalLambdaBodyBounds.source_body_at
        captured code history inputs functions owner caller callerPrefix capturedSlots physical stable beforeTyped argumentsTyped terminal certifies
        entry added length copied spine kept reached budget childSize (Nat.le_of_lt strict) children)
    trace within

include capturedSlots physical stable beforeTyped argumentsTyped terminal certifies represented heaps locals reference currentCarried allowed callerRuntime in
/-- Reflection selects the authentic strict native body child and constructs
its independently graded Source body from the expression hypothesis. -/
theorem application_reflects (child : Staging.Recursive.Scope)
    (selected : stages.Closure function child) (valid : Dynamic.ClosureFrame program function)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) callerPrefix).forgetSlots inputs.context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      stages child certificate faults budget)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies program stages sourceSize invocation callContext before
        (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := registry) (faults := faults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable child selected valid budget
    (fun entry reached childSize strict =>
      SelectedCompilationPhysicalTerminalLambdaBodyBounds.native_body_at
        captured code history inputs functions owner caller callerPrefix capturedSlots physical stable beforeTyped argumentsTyped terminal certifies
        entry reached child selected valid budget childSize (Nat.le_of_lt strict) children)
    completed within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport
/-! Canonical terminal closure roots retain the same compiler, original Source
and parameter context. Actual captured global values are supplied later by the
real parameter entry, and are not a static support premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues

structure SelectedBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function localScope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
    packet.expression packet.receipt.child
  readFuel : Nat
  «prefix» : code.compilation.administrativePrefix = 1
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    SelectedCompilationMixedRootSupport.RootChoice compiled headers stages code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child function.resultType semanticFaults

def SelectedBody.rootAt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    {code : Code compiled.indexed function localScope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {stages : Staging.Recursive.Registry}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    {semanticFaults : FunctionCalls.FaultRep}
    (support : SelectedBody (headers := headers) code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    SelectedCompilationMixedRootSupport.RootAt compiled headers stages inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults :=
  SelectedCompilationMixedRootSupport.RootAt.ofChoice (support.roots child selected)

/-- Terminal and scoped flow packets both refer to the identical retained Code. -/
inductive Packet {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (stages : Staging.Recursive.Registry) where
  | terminal (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
  | branching (packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code stages)

def Support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry) (packet : Packet code stages)
    (semanticFaults : FunctionCalls.FaultRep) : Type :=
  match packet with
  | .terminal terminal => SelectedBody (headers := headers) code inputs stages terminal semanticFaults
  | .branching branching => SelectedCompilationPhysicalBranchingClosureStaticSupport.SelectedBody
      headers code inputs stages branching semanticFaults

def LegacyPacketFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry) : Type :=
  match association with
  | .ordinary _ _ code _ _ _ _ _ _ _ _ => Packet code stages
  | .principal _ _ code _ _ _ _ _ _ _ _ => Packet code stages

def LegacySupportFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry)
    (packet : LegacyPacketFor association stages) : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      Support (headers := headers) code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _ =>
      Support (headers := headers) code support.body.toContext stages packet semanticFaults

def PacketFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry) : Type :=
  match association with
  | .legacy original => LegacyPacketFor original.original stages
  | .preparedOrdinary _ _ code _ _ _ _ _ _ _ _ _ _ => Packet code stages
  | .preparedBranching _ _ code _ _ _ _ _ _ _ _ _ _ => Packet code stages

def SupportFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry)
    (packet : PacketFor association stages) : Type :=
  match association with
  | .legacy original => LegacySupportFor original.original stages packet
  | .preparedOrdinary _ _ code _ support _ _ _ _ _ _ _ _ =>
      Support (headers := headers) code support.body.toContext stages packet semanticFaults
  | .preparedBranching _ _ code _ support _ _ _ _ _ _ _ _ =>
      Support (headers := headers) code support.body.toContext stages packet semanticFaults

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
/-! A positive retained closure keeps all captured physical slots. Its genuine
terminal or scoped application consumes the shared strict mixed-root induction and retains
the exact caller, Source heap, native store and ordered handle histories. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))


section ContextualApplication
variable (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)
  (packet : PacketFor association stages)
  (supported : SupportFor association stages packet)
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)


include physical owners supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- The actual Association and chosen packet retain the original parameter
context. Each body branch constructs its application port from the strict Root IH. -/
theorem application_preserves (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before (.closure function) sources outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        finalMap finalWorld function.resultType resultCore callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  cases association with
  | legacy legacyAssociation =>
    rcases legacyAssociation with ⟨original, slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : ∀ child, stages.Closure function child →
            CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages child terminal.certificate callFaults budget := by
          intro child selected
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt child selected) owner
            (owners owner) point
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            budget below trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) children trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : ∀ child, stages.Closure function child →
            CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages child terminal.certificate callFaults budget := by
          intro child selected
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt child selected) owner
            (owners owner) point
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            budget below trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) children trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt child selected) owner
          (owners owner) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt child selected) owner
          (owners owner) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include physical owners supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- Reflection uses the packet-selected Source scope. The original parameter
installation, independent Source grade and literal returned caller are preserved. -/
theorem application_reflects (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {invocation : Staging.Recursive.Scope} {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        finalMap finalWorld function.resultType resultCore callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  cases association with
  | legacy legacyAssociation =>
    rcases legacyAssociation with ⟨original, slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages terminal.child terminal.certificate callFaults budget := by
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
            (owners owner) point
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            terminal.child terminal.selected valid budget below completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) valid children completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages terminal.child terminal.certificate callFaults budget := by
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
            (owners owner) point
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            terminal.child terminal.selected valid budget below completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) valid children completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (owners owner) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) valid children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (owners owner) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) valid children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end ContextualApplication
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureParentBounds
/-! The real indirect closure parent uses the same selected Association and
retained terminal packet at its application boundary. Both numeric
grades, physical gates, original three binds and returned caller restoration
are the existing proofs. The strict Root IH supplies the called body internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {argumentMap : LocationMap} {argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled argumentMap argumentsStore)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.closure function))
  (argumentsTyped : Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes)
  (argumentMetadata : Dynamic.HeapMetadataExtend calleeHeap argumentsHeap)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeRelated : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
    headers keys bodyRegistry completion.result.context.registry semanticFaults profile argumentMap argumentWorld
    (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions

local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))


include physical owners bridge profile compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  dispatch selected count accepted argumentsTyped argumentMetadata runtime calleeTyped
  actualFunctionType calleeRelated represented bundle originalResult semantic assignmentInterpretation in
/-- The genuine argument endpoint feeds the actual closure application once.
Its native suffix and original three binds complete the whole parent. -/
theorem preserves_parent
    (packets : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.closure function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, _valid, bindings, parameterCore, resultCore, member, _parameterEq, resultEq, parameters⟩ :=
    SelectedCompilationPhysicalClosureArgumentRows.at_arguments bridge profile compiler reached dispatch
      selected count runtime argumentsTyped argumentMetadata calleeTyped bundle admitted
      actualFunctionType calleeRelated represented argumentsTrace
  obtain ⟨association⟩ := member
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_preserves (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      profile association (packets association) (supported association) (bridge.pool reached)
      raw parameters heaps physical owners admitted.rows runtime budget children called within
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps,
    maps.trans applicationMaps, worlds.trans applicationWorlds, frame.trans applicationFrame,
    heapMetadata.trans applicationMetadata, returned, callerProtocol.trans related callerRelated, parentPost⟩

include physical owners bridge profile compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  dispatch selected count accepted argumentsTyped argumentMetadata runtime calleeTyped
  actualFunctionType calleeRelated represented bundle originalResult semantic assignmentInterpretation in
/-- The concrete selected closure suffix constructs the original applied
parent. Both numeric grades and every transient reached effect are retained. -/
theorem reflects_suffix
    (packets : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, valid, bindings, parameterCore, resultCore, member, parameterEq, resultEq, parameters⟩ :=
    SelectedCompilationPhysicalClosureArgumentRows.at_arguments bridge profile compiler reached dispatch
      selected count runtime argumentsTyped argumentMetadata calleeTyped bundle admitted
      actualFunctionType calleeRelated represented argumentsTrace
  obtain ⟨association⟩ := member
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_reflects (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      profile association (packets association) (supported association) (bridge.pool reached)
      raw parameters heaps physical owners admitted.rows runtime valid budget children application (Nat.le_of_lt strict)
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize],
    outcome, after, finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity applied,
    parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

end Parent

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureUserDispatch
/-! The authentic user prefix dispatches a closure through its exact chosen
retained terminal packet and static support. A strict Root family at the same
point budget constructs the called body. Physical arity rejection, original
argument rows, independent numeric grades and the returned caller PostAdmission
retain their existing proofs. The global prefix remains the original named
branch. This internal interface supplies the future mutual body induction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureUserDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)
open SelectedCompilationIndirectBuiltinPreservationDispatch (ParentAt)
open SelectedCompilationIndirectBuiltinApplicationDispatch (UserApplicationPrefix ParentResult)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open SelectedCompilationGlobalCallPrefixes (GlobalAppliedPrefix)
open SelectedCompilationGlobalCallPrefixes (GlobalApplicationPrefix)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))



variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include physical owners sourceParent occurrence preparedStages receiver runtime sourceEq tree unique
  parentTyped calleeFound guardFrame actualFunctionType semantic assignmentInterpretation in
/-- Authentic Source application and prefix witnesses construct the original
closure parent. Physical count rejection keeps the reached argument heap and
literal receiving arity word; success preserves the actual selected body once. -/
theorem preserves_closure_or_global
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (user : Staging.CallBoundary.UserCallable sourceValue)
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize ≤ budget)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functions)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after ∨
    GlobalAppliedPrefix (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after := by
  cases user with
  | global function =>
    exact .inr ⟨function, rfl, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩
  | closure function =>
    have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
      simpa only [sourceEq] using tree
    have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
    have originalTyping : ExpressionHasType source context id compiler.original.type := by
      simpa only [sourceEq] using parentTyped
    obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
      CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
        originalTree originalUnique originalTyping calleeFound
    have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
      simpa only [sourceEq] using argumentsTyped
    obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
      calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
      originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
      represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
      frame, heapMetadata, sourceValuesTyped, argumentMetadata, reached, related, admitted⟩ := prefixResult
    cases boundary with
    | user dispatch selected =>
      by_cases count : dispatch.row.entry.parameterCount = ids.length
      · have calleeNative := calleePost.1
        obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
        have calleeHeapTyped := calleeAdmission.at_value.2.heap
        have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        have relatedCallee : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
            headers keys bodyRegistry completion.result.context.registry semanticFaults profile finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
          change GenericHeap.PayloadModel.Represents model finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type
          simpa only [functionType] using calleeRelated
        exact .inl (SelectedCompilationPhysicalClosureParentBounds.preserves_parent (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          bridge profile compiler prepared sourceParent occurrence initial reached related admitted
          heaps (physical reached) owners maps worlds frame heapMetadata dispatch selected count accepted sourceValuesTyped argumentMetadata runtime rawCallee actualFunctionType relatedCallee
          represented bundle originalResult packets supported budget bodyChildren calleeTrace argumentsTrace called within
          calleeNative firstGate argumentsNative)
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have different : function.parameters.length ≠ ids.length := by
          simpa only [physical] using count
        cases called with
        | closure selectedChild valid parameters _copy allocate bodyTrace bodyResult =>
          exact False.elim (different (allocate.length_eq.trans valuesCount))
        | closureArity mismatch =>
          have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
              prepared.site.call ids (.closure function) := by
            simpa only [guardFrame, prepared.call] using accepted
          have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
              (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
              (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
            simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
              using argumentsNative
          have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
            (result := compiler.resultType) dispatch selected actualAccepted count
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
          change Evaluates actual store
            (CallableContract.call prepared.site.gates
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              (compiler.calleeCode.expression.rename ξ)
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
          rw [← prepared.lowered_rename compiler ξ] at native
          obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
            CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
              compiler prepared preparedStages selected receiver initial functions reached related heaps
              (sourceResult := compiler.original.type) (resultCore := lowered.type) count
          cases sameState
          have loweredType : lowered.type = compiler.resultType :=
            (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
          have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
          have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
              compiler.original.type
              (.fault (.semantic (.argumentArityMismatch function.parameters.length sources.length))) reached :=
            ⟨admitted.rows, by intro value impossible; cases impossible⟩
          refine .inl ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
            argumentsTrace sourceParent.arity (.closureArity mismatch),
            .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
            argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
            heapMetadata, reached, keptRelated, post⟩
          · simpa only [loweredType] using native
          · simpa only [physical, valuesCount] using faultRep


include physical owners sourceParent occurrence preparedStages receiver runtime sourceEq tree unique parentTyped calleeFound actualFunctionType semantic assignmentInterpretation in
/-- User classification and physical arity happen inside the actual retained
prefix. The closure branch constructs full parent meaning; only the literal
global application remains for the separate named producer. -/
theorem reflects_closure_or_global
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    {budget size : Nat} {value : Value} {finalStore : Store}
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (user : UserApplicationPrefix (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (functionModel := functions) (completion := completion)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge compiler prepared initial budget value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨sourceValue, userKind, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  cases userKind with
  | global function =>
    exact .inr ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
      calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
      argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩
  | closure function =>
    obtain ⟨calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
      _callView, boundary, heaps, maps, worlds, frame, heapMetadata, sourceValuesTyped, argumentMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩ := tail
    cases boundary with
    | user dispatch selected =>
      by_cases same : dispatch.row.entry.parameterCount = ids.length
      · obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
        have calleeHeapTyped := calleeAdmission.at_value.2.heap
        have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        have relatedCallee : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins
            headers keys bodyRegistry completion.result.context.registry semanticFaults profile finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
          change GenericHeap.PayloadModel.Represents model finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type
          simpa only [functionType] using calleeRelated
        obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
          returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
          SelectedCompilationPhysicalClosureParentBounds.reflects_suffix (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            bridge profile compiler prepared sourceParent occurrence initial reached related admitted
            heaps (physical reached) owners maps worlds frame heapMetadata dispatch selected same accepted sourceValuesTyped argumentMetadata runtime rawCallee actualFunctionType relatedCallee
            represented bundle originalResult packets supported budget bodyChildren calleeTrace argumentsTrace suffix
            (Nat.le_of_lt strict)
        exact .inl ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
          resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
          returned, returnedRelated, returnedPost⟩
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have failedSource := CallableIndexedOwnedPreparedSecondCallGateRejection.closure_source
          occurrence compiler.argumentCoercions sourceParent.arity argumentsTrace calleeTrace accepted
          (by simpa only [physical] using same)
        have lowerType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        obtain ⟨sameValue, sameStore⟩ :=
          CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
            dispatch.shape selected dispatch.found same suffix
        cases sameStore
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) same
        cases sameState
        refine .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
          .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
          argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
          heapMetadata, reached, keptRelated, ?_⟩
        · simpa only [physical] using failedSource
        · have exactValue : value = .inLeft lowered.type
              (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
                .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
            simpa only [lowerType] using sameValue
          rw [exactValue]
          exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
          exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureUserDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalDomains
/-! The accepted contextual factory identifies its original cached body.
The resulting domain exclusion applies to the same Packet and native code. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalDomains
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

private theorem exact_member {plan : Plan}
    {owner : SourceCompilationPlan.Key} {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- The key exclusion is derived from this Packet's own accepted preparation,
the real cache position, and the original body checker. -/
theorem packet_domain_excludes_earlier
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance}
    {raw : Core.Expr} (packet : Packet inputs candidate raw)
    (indexed : Indexed cached.indexed packet)
    {earlier : InitializedLetBinding}
    (member : earlier ∈ initializedLetBindings candidate.origin.source)
    (before : earlier.binder.id.binderIndex <
      candidate.origin.localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ packet.original.emission.prepared.substitution.domain := by
  obtain ⟨row, selected, source, substitution, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan] at selected
  obtain ⟨index, named, position, same⟩ :=
    SelectedCompilationCachedSources.row_position cached (exact_member selected)
  obtain ⟨body, _⟩ :=
    SourceBodyTemplateScope.cached_selection_scope artifact checked position
  have sameSource : named.specialized.function.typedBody = candidate.origin.source := by
    rw [same]
    exact source
  have origin : LocalLambdaInstance.LexicalReadOrigin
      named.specialized.function.typedBody candidate.origin.localInstance := by
    rw [sameSource]
    exact GeneralizedLocalLexicalOrigin.packet_origin packet
  have retained : earlier ∈ initializedLetBindings named.specialized.function.typedBody := by
    rwa [sameSource]
  rw [substitution]
  exact body.local_domain_excludes_earlier artifact checked position origin retained before quantified

/-- The native code's active substitution is the same accepted Packet's
substitution, so its domain has the same actual-owner exclusion. -/
theorem materialized_domain_excludes_earlier
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {relation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization
      cached mapping world function relation)
    {earlier : InitializedLetBinding}
    (member : earlier ∈ initializedLetBindings material.candidate.origin.source)
    (before : earlier.binder.id.binderIndex <
      material.candidate.origin.localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ material.code.active.domain := by
  rw [material.active]
  exact packet_domain_excludes_earlier artifact checked material.packet material.indexed
    member before quantified

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalDomains
end
