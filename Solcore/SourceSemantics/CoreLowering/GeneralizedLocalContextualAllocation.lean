import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization

/-! Allocation attaches the current body's Source view to the existing
Snapshot. Both the caller and the candidate select the same actual plan row.
This producer uses the accepted Packet and compiler catalog, so callers do not
supply a separate equality with the binding's original Source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInstanceValues (referenceIndex value)
open GeneralizedLocalAcceptedInstances (Snapshot)
open GeneralizedLocalContextualMaterialization (Attachment)
open CallableAncestryProfiles.SourceComposition

private theorem source_at {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source)
    {original : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok original) :
    source = original.function.typedBody.applySubstitution active := by
  cases receipt with
  | original found =>
      cases Except.ok.inj (found.symm.trans selected)
      exact (EmptySourceSubstitution.source _).symm
  | contextual accepted =>
      obtain ⟨row, found, _, _, same⟩ := LambdaSourceAlignment.prepared_source accepted
      cases Except.ok.inj (found.symm.trans selected)
      exact same

/-- Named entry supplies an empty closed context. A contextual invocation
obtains its closed context from the actual local matcher and cumulative key. -/
theorem read_context_closed {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    (closed : RangesClosed active) : RangesClosed receipt.candidate.origin.substitution := by
  rw [receipt.candidate_key]
  exact RangesClosed.compose closed (matchClosed_ranges receipt.matched)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem attachment_of_packet {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {currentSource : TypedSource}
    (current : LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      binding.caller active currentSource)
    (view : LambdaMetadataViews.MetadataView function.source currentSource)
    (closed : RangesClosed active) : Attachment function binding active := by
  obtain ⟨owner, originalSource, _, _⟩ :=
    SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, source, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have same := source_at current selected
  rw [source, originalSource] at same
  exact ⟨closed, same ▸ view⟩

/-- The actual native closure is formed and its retained row contains the
allocation view. Later readout consumes this row to reconstruct full Code. -/
theorem formation_at_frame {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : Substitution} {candidate : SourceCoreLocalPolymorphism.Instance}
    {inputs : Inputs} {raw : Core.Expr} {packet : Packet inputs candidate raw}
    (indexed : Indexed compiled.indexed packet) {actual : Core.Environment}
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext lexical)
    (sameLexical : indexed.lexical = lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    {currentSource : TypedSource}
    (current : LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      binding.caller lexical currentSource)
    (view : LambdaMetadataViews.MetadataView function.source currentSource)
    (closed : RangesClosed lexical)
    (origin : Origin compiled.indexed function binding lexical)
    (captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world
      inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type compiled.indexed.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (reference : captured.canonical[referenceIndex indexed]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame origin.native)) :
    Evaluates actual store (raw.rename captured.embedding)
      (value indexed captured.embedding origin.native actual) store ∧
    Snapshot compiled.indexed mapping world function binding lexical location
      (Attachment function binding lexical) candidate
      (value indexed captured.embedding origin.native actual) := by
  have attached := attachment_of_packet indexed located member current view closed
  obtain ⟨_, source, binder, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  exact GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical owner initializer
    source (congrArg TypedBinder.id binder) _ attached origin captured declarations ownership issuer
    typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAllocation
