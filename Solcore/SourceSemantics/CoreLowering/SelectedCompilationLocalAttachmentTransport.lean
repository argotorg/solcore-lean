import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalScopeAgreement
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalSourceReceipts
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalCapturedLambdaHeader
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadBindingIdentity

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
